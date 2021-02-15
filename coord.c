// Copyright (C) 2016, 2017 Alexey Khrabrov, Bogdan Simion
//                     2020 Angela Demke Brown
// Distributed under the terms of the GNU General Public License.
//
// This file is part of Assignment 3, CSC469, Fall 2020.
//
// This is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This file is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this file.  If not, see <http://www.gnu.org/licenses/>.

// The coordinator implementation

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/socket.h>

#include "defs.h"
#include "util.h"

// Program arguments

// Ports for listening to incoming connections from clients and servers
static uint16_t clients_port = 0;
static uint16_t servers_port = 0;

// Server configuration file name
static char cfg_file_name[PATH_MAX] = "";

// Timeout for detecting server failures;
// you might want to adjust this default value.
static const int default_server_timeout = 5;
static int server_timeout = 0;

// Log file name
static char log_file_name[PATH_MAX] = "";

// Pointer to pre-packaged configuration response for clients
config_response *config_msg = NULL;

// Structure describing the recovery state
typedef struct _recovery_info
{
	bool recovery_mode;
	bool updated_primary;
	bool updated_secondary;
	int KV_aa_sid;
	int KV_b_sid;
} recovery_info;

// One variable to denote the recovery state is sufficient since there will be no crashes during recovery
static recovery_info recovery_status; 

static void usage(char **argv)
{
	printf("usage: %s -c <client port> -s <servers port> -C <config file> "
		   "[-t <timeout (seconds)> -l <log file>]\n",
		   argv[0]);
	printf("Default timeout is %d seconds\n", default_server_timeout);
	printf("If the log file (-l) is not specified, log output is written to stdout\n");
}

// Returns false if the arguments are invalid
static bool parse_args(int argc, char **argv)
{
	char option;
	while ((option = getopt(argc, argv, "c:s:C:l:t:")) != -1)
	{
		switch (option)
		{
		case 'c':
			clients_port = atoi(optarg);
			break;
		case 's':
			servers_port = atoi(optarg);
			break;
		case 'l':
			strncpy(log_file_name, optarg, PATH_MAX);
			break;
		case 'C':
			strncpy(cfg_file_name, optarg, PATH_MAX);
			break;
		case 't':
			server_timeout = atoi(optarg);
			break;
		default:
			fprintf(stderr, "Invalid option: -%c\n", option);
			return false;
		}
	}

	if (server_timeout == 0)
	{
		server_timeout = default_server_timeout;
	}

	// Insist on coordinator starting on known ports
	return (clients_port != 0) && (servers_port != 0) &&
		   (cfg_file_name[0] != '\0');
}

// Current machine host name
static char coord_host_name[HOST_NAME_MAX] = "";

// Sockets for incoming connections from clients and servers
static int clients_fd = -1;
static int servers_fd = -1;

// Store socket fds for all connected clients, up to MAX_CLIENT_SESSIONS
static int client_fd_table[MAX_CLIENT_SESSIONS];

// Structure describing a key-value server state
typedef struct _server_node
{
	// Server host name, possibly prefixed by "user@" (for starting servers remotely via ssh)
	char host_name[HOST_NAME_MAX];
	// Servers/client/coordinator port numbers
	uint16_t srvport;
	uint16_t clport;
	uint16_t coport;
	// Server ID
	int sid;
	// Socket for receiving requests from this server
	int sockfd_in;
	// Socket for sending requests to this server
	int sockfd_out;
	// Server process PID (it is a child process of coordinator)
	pid_t pid;

	// time of the last heartbeat received
	time_t last_heartbeat;

} server_node;

// Total number of servers
static int num_servers = 0;
// Server state information
static server_node *server_nodes = NULL;

// Read the configuration file, fill in the server_nodes array
// Returns false if the configuration is invalid
static bool read_config_file()
{
	FILE *cfg_file = fopen(cfg_file_name, "r");
	if (cfg_file == NULL)
	{
		log_perror("Invalid configuration file");
		return false;
	}

	// The first line contains the number of servers
	if (fscanf(cfg_file, "%d\n", &num_servers) < 1)
	{
		fclose(cfg_file);
		return false;
	}

	// Need at least 3 servers to avoid cross-replication
	if (num_servers < 3)
	{
		log_error("Invalid number of servers: %d\n", num_servers);
		fclose(cfg_file);
		return false;
	}

	if (num_servers > MAX_KV_SERVERS)
	{
		log_error("Too many servers in config file (%d), using first %d\n",
				  num_servers, MAX_KV_SERVERS);
		num_servers = MAX_KV_SERVERS;
	}

	if ((server_nodes = calloc(num_servers, sizeof(server_node))) == NULL)
	{
		log_perror("calloc");
		fclose(cfg_file);
		return false;
	}

	bool result = true;

	for (int i = 0; i < num_servers; i++)
	{
		server_node *node = &(server_nodes[i]);

		// Format: <host_name> <clients port> <servers port> <coord_port>
		if ((fscanf(cfg_file, "%s %hu %hu %hu\n",
					node->host_name, &(node->clport),
					&(node->srvport), &(node->coport)) < 4))
		{
			log_error("Error scanning config file at line %d", i + 1);
			result = false;
			break;
		}

		if (strcmp(node->host_name, "localhost") == 0)
		{
			// Canonicalize host name for 'localhost'
			if (get_local_host_name(node->host_name, HOST_NAME_MAX) < 0)
			{
				log_error("Could not canonicalize localhost");
				result = false;
				break;
			}
		}
		else if (strchr(node->host_name, '@') == NULL)
		{
			// host_name not "localhost" and no "user@host" given
			log_error("Bad host on line %d", i + 1);
			result = false;
			break;
		}

		// Uncomment this to require specific server ports in config file
		//if ((node->clport==0) || (node->srvport==0) || (node->coport==0)) {
		//	log_error("Bad ports on line %d",i+1);
		//	result = false;
		//	break;
		//}

		node->sid = i;
		node->sockfd_in = -1;
		node->sockfd_out = -1;
		node->pid = 0;
	}

	if (result == false)
	{
		free(server_nodes);
		server_nodes = NULL;
	}
	else
	{
		// Print server configuration
		printf("Key-value servers configuration:\n");
		for (int i = 0; i < num_servers; i++)
		{
			server_node *node = &(server_nodes[i]);
            printf("\thost: %s, client port: %d, server port: %d,"
                   " coord port: %d\n",
                   node->host_name, node->clport,
                   node->srvport, node->coport);
        }
	}

	fclose(cfg_file);
	return result;
}

static void cleanup();
static bool init_servers();

// Initialize and start the coordinator
static bool init_coordinator()
{
	char timebuf[TIME_STR_SIZE];

	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++)
	{
		client_fd_table[i] = -1;
	}

	// Get the host name that coordinator is running on
	if (get_local_host_name(coord_host_name, sizeof(coord_host_name)) < 0)
	{
		return false;
	}
	log_write("%s Coordinator starts on host: %s\n",
			  current_time_str(timebuf, TIME_STR_SIZE), coord_host_name);

	// Create sockets for incoming connections from servers
	if ((servers_fd = create_server(servers_port, num_servers + 1, NULL)) < 0)
	{
		goto cleanup;
	}

	// Start key-value servers
	if (!init_servers())
	{
		goto cleanup;
	}

	// Create sockets for incoming connections from clients
	if ((clients_fd = create_server(clients_port, MAX_CLIENT_SESSIONS, NULL)) < 0)
	{
		goto cleanup;
	}

	recovery_status.recovery_mode = false;
	recovery_status.updated_primary = false;
	recovery_status.updated_secondary = false;
	recovery_status.KV_aa_sid = -1;
	recovery_status.KV_b_sid = -1;
	log_write("Coordinator initialized\n");
	return true;

cleanup:
	cleanup();
	return false;
}

// Cleanup and release all the resources
static void cleanup()
{
	close_safe(&clients_fd);
	close_safe(&servers_fd);

	// Close all client connections
	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++)
	{
		close_safe(&(client_fd_table[i]));
	}

	if (server_nodes != NULL)
	{
		for (int i = 0; i < num_servers; i++)
		{
			server_node *node = &(server_nodes[i]);

			if (node->sockfd_out != -1)
			{
				server_ctrl_request request = {0};
				// Tell server to dump primary key table to disk
				request.hdr.type = MSG_SERVER_CTRL_REQ;
				request.type = DUMP_PRIMARY;
				send_msg(node->sockfd_out, &request, sizeof(request));

				// Tell server to dump secondary key table to disk
				request.hdr.type = MSG_SERVER_CTRL_REQ;
				request.type = DUMP_SECONDARY;
				send_msg(node->sockfd_out, &request, sizeof(request));

				// Request server shutdown
				request.hdr.type = MSG_SERVER_CTRL_REQ;
				request.type = SHUTDOWN;
				send_msg(node->sockfd_out, &request, sizeof(request));
			}

			// Wait with timeout (or kill if timeout expires)
			// for the server process to exit
			if (server_nodes[i].pid > 0)
			{
				kill_safe(&(server_nodes[i].pid), 5);
			}

			// Close the connections
			close_safe(&(server_nodes[i].sockfd_out));
			close_safe(&(server_nodes[i].sockfd_in));
		}

		free(server_nodes);
		server_nodes = NULL;
	}
}

static const int max_cmd_length = 32;

// WARNING: YOU WILL NEED TO CHANGE THIS PATH TO MATCH YOUR SETUP!
static const char *remote_path = "/h/u8/c0/00/nanahjik/csc2208/group_0210/a3/";

// Generate a command to start a key-value server.
// (see server.c for arguments description)
static char **get_spawn_cmd(int sid)
{
	char **cmd = calloc(max_cmd_length, sizeof(char *));
	assert(cmd != NULL);

	server_node *node = &(server_nodes[sid]);
	int i = -1;

	// For remote server, host_name format is "user@host"

	if (strchr(node->host_name, '@') != NULL)
	{
		// Use ssh to run the command on a remote machine
		cmd[++i] = strdup("ssh");
		cmd[++i] = strdup("-o");
		cmd[++i] = strdup("StrictHostKeyChecking=no");
		cmd[++i] = strdup(node->host_name);
		cmd[++i] = strdup("cd");
		cmd[++i] = strdup(remote_path);
		cmd[++i] = strdup("&&");
	}

	cmd[++i] = strdup("./server\0");

	cmd[++i] = strdup("-h");
	cmd[++i] = strdup(coord_host_name);

	cmd[++i] = strdup("-m");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%hu", servers_port);

	cmd[++i] = strdup("-c");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%hu", node->clport);

	cmd[++i] = strdup("-s");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%hu", node->srvport);

	cmd[++i] = strdup("-M");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%hu", node->coport);

	cmd[++i] = strdup("-S");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%d", sid);

	cmd[++i] = strdup("-n");
	cmd[++i] = malloc(8);
	sprintf(cmd[i], "%d", num_servers);

	cmd[++i] = strdup("-l");
	cmd[++i] = malloc(20);
	sprintf(cmd[i], "server_%d.log", sid);

	cmd[++i] = NULL;
	assert(i < max_cmd_length);
	return cmd;
}

static void free_cmd(char **cmd)
{
	assert(cmd != NULL);

	for (int i = 0; i < max_cmd_length; i++)
	{
		if (cmd[i] != NULL)
		{
			free(cmd[i]);
		}
	}
	free(cmd);
}

// Start a key-value server with given id
static int spawn_server(int sid)
{
	char timebuf[TIME_STR_SIZE];

	server_node *node = &(server_nodes[sid]);

	close_safe(&(node->sockfd_in));
	close_safe(&(node->sockfd_out));
	kill_safe(&(node->pid), 0);

	// Spawn the server as a process on either the local machine or a remote machine (using ssh)
	pid_t pid = fork();
	switch (pid)
	{
	case -1:
		log_perror("fork");
		return -1;
	case 0:
	{
		char **cmd = get_spawn_cmd(sid);
		execvp(cmd[0], cmd);
		// If exec returns, some error happened
		perror(cmd[0]);
		free_cmd(cmd);
		_exit(1);
	}
	default:
		node->pid = pid;
		break;
	}

	// Wait for the server to connect
	int fd_idx = accept_connection(servers_fd, &(node->sockfd_in), 1);
	if (fd_idx < 0)
	{
		// Something went wrong, kill the server process
		kill_safe(&(node->pid), 1);
		return -1;
	}
	assert(fd_idx == 0);

	// Wait for server to send coordinator the ports that it is using.
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(node->sockfd_in, req_buffer,
				  MAX_MSG_LEN, MSG_COORD_CTRL_REQ))
	{
		// Something went wrong, kill the server process
		close_safe(&(node->sockfd_in));
		kill_safe(&(node->pid), 1);
		return -1;
	}
	coord_ctrl_request *req = (coord_ctrl_request *)req_buffer;
	assert(req->type == STARTED);
	node->clport = req->ports[0];
	node->srvport = req->ports[1];
	node->coport = req->ports[2];
	log_write("%s Coordinator got ports from server %d: (%hu, %hu, %hu)\n",
			  current_time_str(timebuf, TIME_STR_SIZE), sid,
			  node->clport, node->srvport, node->coport);

	// Extract the host name from "user@host"
	char *at = strchr(node->host_name, '@');
	char *host = (at == NULL) ? node->host_name : (at + 1);

	// Connect to the server
	if ((node->sockfd_out = connect_to_server(host, node->coport)) < 0)
	{
		// Something went wrong, kill the server process
		close_safe(&(node->sockfd_in));
		kill_safe(&(node->pid), 1);
		return -1;
	}

	node->last_heartbeat = time(0);

	return 0;
}

// Send the initial SET-SECONDARY message to a newly created server; returns true on success
static bool send_set_secondary(int sid)
{
	char buffer[MAX_MSG_LEN] = {0};
	server_ctrl_request *request = (server_ctrl_request *)buffer;

	// Fill in the request parameters
	request->hdr.type = MSG_SERVER_CTRL_REQ;
	request->type = SET_SECONDARY;
	server_node *secondary_node = &(server_nodes[secondary_server_id(sid, num_servers)]);
	request->port = secondary_node->srvport;

	// Extract the host name from "user@host"
	char *at = strchr(secondary_node->host_name, '@');
	char *host = (at == NULL) ? secondary_node->host_name : (at + 1);

	int host_name_len = strlen(host) + 1;
	strncpy(request->host_name, host, host_name_len);

	// Send the request and receive the response
	server_ctrl_response response = {0};
	if (!send_msg(server_nodes[sid].sockfd_out, request, sizeof(*request) + host_name_len) ||
		!recv_msg(server_nodes[sid].sockfd_out, &response, sizeof(response), MSG_SERVER_CTRL_RESP))
	{
		return false;
	}

	if (response.status != CTRLREQ_SUCCESS)
	{
		log_error("Server %d failed SET-SECONDARY\n", sid);
		return false;
	}
	return true;
}

// Start all key-value servers
static bool init_servers()
{
	// Spawn all the servers
	for (int i = 0; i < num_servers; i++)
	{
		if (spawn_server(i) < 0)
		{
			return false;
		}
	}

	// Let each server know the location of its secondary replica
	for (int i = 0; i < num_servers; i++)
	{
		if (!send_set_secondary(i))
		{
			return false;
		}
	}
	return true;
}

// Copy prepared configuration response into fresh message buffer, since
// send_msg() can mangle the message buffer contents.
// You may wish to modify this function to send a different configuration
// response while recovery is in progress.
static int prepare_config_response(config_response *conf)
{
	int bytes_left = MAX_MSG_LEN;
	int bytes_used = 0;
	int cur;
	int i;
	int sid;

	// Need to generate a new config if we are in recovery mode
	if (config_msg != NULL && recovery_status.recovery_mode)
	{
		// free the old config_msg
		free(config_msg);
		config_msg = NULL;
	}

	// Initialize configuration message buffer once and re-use
	if (config_msg == NULL)
	{
		config_msg = (config_response *)calloc(MAX_MSG_LEN, sizeof(char));
		if (config_msg == NULL)
		{
			log_perror("calloc");
			return 0;
		}

		config_msg->hdr.type = MSG_CONFIG_RESP;
		config_msg->num_entries = num_servers;
		bytes_left -= sizeof(config_response);
		for (i = 0, sid = 0; i < num_servers; i++)
		{
			// check to see if this config is being generated in recovery mode
			if (recovery_status.recovery_mode && i == recovery_status.KV_aa_sid)
			{
				// KV_b's hostname and client port replace the entry for KV_a in the 
				// configuration that will be sent back in response to a client request
				sid = secondary_server_id(i, num_servers);
			}
			else
			{
				sid = i;
			}

			// Extract the host name from "user@host"
			char *at = strchr(server_nodes[sid].host_name, '@');
			char *host;
			if (at == NULL)
			{
				host = server_nodes[sid].host_name;
			}
			else
			{
				host = (at + 1);
			}
			// print hostname and client port into entry_buffer
			cur = snprintf(config_msg->entry_buffer + bytes_used,
						   bytes_left, "%s %hu;",
						   host, server_nodes[sid].clport);
			if (cur > bytes_left)
			{
				// Ran out of room
				log_error("message buffer too small for config\n");
				free(config_msg);
				return 0;
			}
			bytes_used += cur;
			bytes_left -= cur;
		}
		// Add 1 for null-terminator written by snprintf at end of last entry
		config_msg->hdr.length = sizeof(config_response) + bytes_used + 1;
	}

	memcpy(conf, config_msg, config_msg->hdr.length);
	return config_msg->hdr.length;
}

// Connection will be closed after calling this function regardless of result
static void process_client_message(int fd)
{
	char timebuf[TIME_STR_SIZE];
	char buffer[MAX_MSG_LEN];
	int len;

	log_write("%s Receiving a client message\n",
			  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	config_request request = {0};
	if (!recv_msg(fd, &request, sizeof(request), MSG_CONFIG_REQ))
	{
		return;
	}

	len = prepare_config_response((config_response *)buffer);
	assert(len != 0);

	send_msg(fd, buffer, len);
}

// Returns false if the message was invalid (so the connection will be closed)
static bool process_server_message(int fd)
{

	char timebuf[TIME_STR_SIZE];
	char req_buffer[MAX_MSG_LEN] = {0};

	log_write("%s Receiving a server message\n", current_time_str(timebuf, TIME_STR_SIZE));

	// read and process the message

	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_COORD_CTRL_REQ))
	{
		log_write("Coordinator couldn't receive server message\n");
		return false;
	}

	coord_ctrl_request *req = (coord_ctrl_request *)req_buffer;

	switch (req->type)
	{
	case HEARTBEAT:
		server_nodes[req->server_id].last_heartbeat = time(0);
		return true;
	case UPDATED_PRIMARY:
		// CO receives KV_b's UPDATED_PRIMARY message and awaits confirmation from KV_c as well
		recovery_status.updated_primary = true;
		break;
	case UPDATED_SECONDARY:
		// CO receives KV_c's UPDATED_SECONDARY message and awaits confirmation from KV_b as well
		recovery_status.updated_secondary = true;
		break;
	default:
		log_write("Unknown Message\n");
		return false;
	}

	if (recovery_status.updated_primary && recovery_status.updated_secondary)
	{
		// CO receives UPDATED_PRIMARY and UPDATED_SECONDARY messages
		// CO sends KV_b a SWITCH-PRIMARY message
		int fd = (&(server_nodes[recovery_status.KV_b_sid]))->sockfd_out;
		char send_buffer[MAX_MSG_LEN] = {0};
		server_ctrl_request *request = (server_ctrl_request *)send_buffer;
		request->hdr.type = MSG_SERVER_CTRL_REQ;
		request->hdr.length = sizeof(*request);
		request->type = SWITCH_PRIMARY;

		if (!send_msg(fd, request, request->hdr.length))
		{
			log_error("failed Sending a SWITCH_PRIMARY message to sid:%d for finishing recovery\n", recovery_status.KV_b_sid);
			return false;
		}
		
		char recv_buffer[MAX_MSG_LEN] = {0};
		if (!recv_msg(fd, recv_buffer, sizeof(recv_buffer), MSG_SERVER_CTRL_RESP))
		{
			log_error("failed to receive response from sid:%d for SWITCH_PRIMARY for finishing recovery\n", recovery_status.KV_b_sid);
			return false;
		}
		operation_response *response = (operation_response *)recv_buffer;
		if ((int) response->status != (int) CTRLREQ_SUCCESS)
		{
			log_error("Received failure response from sid:%d for SWITCH_PRIMARY\n", recovery_status.KV_b_sid);
			return false;
		}

		// KV_aa starts acting as primary server for its primary kets
		if (!send_set_secondary(recovery_status.KV_aa_sid))
		{
			log_error("Failed to set secondary to the new server that started as part of recovery");
			return false;
		}

		if (config_msg != NULL)
		{
			// Clear the config_msg so that next client gets an updated version of the config
			free(config_msg);
			config_msg = NULL;
		}

		// CO receives the confirmation message from KV_b and marks KV_aa as the new primary for set X in the configuration,
		// then resumes responding to client requests with the new configuration.
		recovery_status.recovery_mode = false;
		recovery_status.updated_primary = false;
		recovery_status.updated_secondary = false;
		recovery_status.KV_aa_sid = -1;
		recovery_status.KV_b_sid = -1;
	}

	return true;
}

static bool send_server_msg(int my_sid, server_ctrlreq_type type, int send_to_sid)
{
	int fd = (&(server_nodes[send_to_sid]))->sockfd_out;

	char send_buffer[MAX_MSG_LEN] = {0};
	server_ctrl_request *request = (server_ctrl_request *)send_buffer;
	request->hdr.type = MSG_SERVER_CTRL_REQ;
	request->type = type;

	// Extract the host name from "user@host"
	char *at = strchr(server_nodes[my_sid].host_name, '@');
	char *host_name;
	if (at == NULL)
	{
		host_name = server_nodes[my_sid].host_name;
	}
	else
	{
		host_name = (at + 1);
	}

	// We need to send host name and port so that the other servers
	// can connect to the new server
	int host_name_len = (strlen(host_name) + 1);
	strncpy(request->host_name, host_name, host_name_len);
	request->hdr.length = host_name_len + sizeof(*request);
	request->port = (server_nodes[my_sid]).srvport;

	if (!send_msg(fd, request, request->hdr.length))
	{
		log_error("Failed sending a message to sid:%d for recovery start\n", send_to_sid);
		return false;
	}

	char recv_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, recv_buffer, sizeof(recv_buffer), MSG_SERVER_CTRL_RESP))
	{
		log_error("Failed to receive response from sid:%d for recovery start\n", send_to_sid);
		return false;
	}
	operation_response *response = (operation_response *)recv_buffer;

	if ((int) response->status != (int) CTRLREQ_SUCCESS) // keep compiler happy
	{
		log_error("Received failure response from sid:%d for recovery start\n", send_to_sid);
		return false;
	}

	return true;
}

static bool recover_server_failure(server_node *failed_node)
{
	uint16_t srvport = failed_node->srvport;
	uint16_t clport = failed_node->clport;
	uint16_t coport = failed_node->coport;

	// spawn a new server to replace the failed server
	// Note: new server connects back to CO and sends its port info on startup
	if (spawn_server(failed_node->sid) < 0)
	{
		log_error("Failed to spawn a new server for recovery");
		return false;
	}

	int KV_b = secondary_server_id(failed_node->sid, num_servers);
	int KV_c = primary_server_id(failed_node->sid, num_servers);

	server_node *new_server = &(server_nodes[failed_node->sid]);
	new_server->srvport = srvport;
	new_server->clport = clport;
	new_server->coport = coport;

	new_server->last_heartbeat = time(0);

	// CO sends KV_b an UPDATE-PRIMARY message containing information on KV_aa
	if (!send_server_msg(failed_node->sid, UPDATE_PRIMARY, KV_b))
	{
		log_error("Failed to send UPDATE_PRIMARY message");
		return false;
	}

	// update the recovery_mode status so that the new clients get correct config_msg
	recovery_status.recovery_mode = true;
	recovery_status.KV_aa_sid = failed_node->sid;
	recovery_status.KV_b_sid = KV_b;

	// CO sends KV_c an UPDATE-SECONDARY message containing information on KV_aa
	if (!send_server_msg(failed_node->sid, UPDATE_SECONDARY, KV_c))
	{
		log_error("Failed to send UPDATE_SECONDARY message");
		return false;
	}

	return true;
}

static const int select_timeout_interval = 1; // seconds
static const int heartbeat_timeout_interval = 3; // seconds

// Returns false if stopped due to errors, true if shutdown was requested
static bool run_coordinator_loop()
{
	// Usual preparation stuff for select()
	fd_set rset, allset;
	FD_ZERO(&allset);
	// End-of-file on stdin (e.g. Ctrl+D in a terminal) is used to request
	// shutdown of the coordinator.
	FD_SET(fileno(stdin), &allset);
	FD_SET(servers_fd, &allset);
	FD_SET(clients_fd, &allset);

	int max_server_fd = -1;
	for (int i = 0; i < num_servers; i++)
	{
		FD_SET(server_nodes[i].sockfd_in, &allset);
		max_server_fd = max(max_server_fd, server_nodes[i].sockfd_in);
	}

	int maxfd = max(clients_fd, servers_fd);
	maxfd = max(maxfd, max_server_fd);

	// Coordinator sits in an infinite loop waiting for incoming connections
	// from clients and for incoming messages from already connected servers
	// and clients.
	for (;;)
	{
		rset = allset;

		struct timeval time_out;
		time_out.tv_sec = select_timeout_interval;
		time_out.tv_usec = 0;

		// Wait with timeout (in order to be able to handle asynchronous
		// events such as heartbeat messages)
		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, &time_out);
		if (num_ready_fds < 0)
		{
			log_perror("select");
			return false;
		}
		if (num_ready_fds <= 0)
		{
			// Due to time out
			continue;
		}

		// Stop if detected EOF on stdin
		if (FD_ISSET(fileno(stdin), &rset))
		{
			char buffer[1024];
			if (fgets(buffer, sizeof(buffer), stdin) == NULL)
			{
				return true;
			}
		}

		// Check for any messages from connected servers
		for (int i = 0; i < num_servers; i++)
		{
			server_node *node = &(server_nodes[i]);
			if ((node->sockfd_in != -1) && FD_ISSET(node->sockfd_in, &rset))
			{
				if (!process_server_message(node->sockfd_in))
				{
					// Received an invalid message, close the connection
					log_error("Closing server %d connection\n", i);
					FD_CLR(node->sockfd_in, &allset);
					close_safe(&(node->sockfd_in));
				}
				--num_ready_fds;
			}

			if (num_ready_fds <= 0)
			{
				break;
			}
		}

		// implement failure detection and recovery
		// Need to go through the list of servers and figure out which
		// servers have not sent a heartbeat message yet within the
		// timeout interval. Keep information in the server_node
		// structure regarding when the last heartbeat was received from
		// a server and compare to current time.
		// Initiate recovery if discovered a failure.

		for (int i = 0; i < num_servers; i++)
		{
			server_node *node = &(server_nodes[i]);
			if (difftime(time(0), node->last_heartbeat) > heartbeat_timeout_interval)
			{
				// CO detects failure
				log_write("HeartBeat of server with sid:%d took %f seconds which is too long\n", i, difftime(time(0), node->last_heartbeat));
				if (recover_server_failure(node))
				{
					log_write("Recovered failure of server with sid:%d successfully\n", i);
					FD_SET(server_nodes[i].sockfd_in, &allset);
					max_server_fd = max(max_server_fd, server_nodes[i].sockfd_in);
				}
				else
				{
					log_error("Failed to spawn new server\n");
					return false;
				}
			}
		}

		if (num_ready_fds <= 0)
		{
			continue;
		}

		// Incoming connection from a client
		if (FD_ISSET(clients_fd, &rset))
		{
			int fd_idx = accept_connection(clients_fd, 
										   client_fd_table, 
										   MAX_CLIENT_SESSIONS);
			if (fd_idx >= 0)
			{
				FD_SET(client_fd_table[fd_idx], &allset);
				maxfd = max(maxfd, client_fd_table[fd_idx]);
			}

			if (--num_ready_fds <= 0)
			{
				continue;
			}
		}

		// Check for any messages from connected clients
		for (int i = 0; i < MAX_CLIENT_SESSIONS; i++)
		{
			if ((client_fd_table[i] != -1) &&
				FD_ISSET(client_fd_table[i], &rset))
			{
				process_client_message(client_fd_table[i]);
				// Close connection after processing
				// (semantics are "one connection per request")
				FD_CLR(client_fd_table[i], &allset);
				close_safe(&(client_fd_table[i]));

				if (--num_ready_fds <= 0)
				{
					break;
				}
			}
		}
	}
}

int main(int argc, char **argv)
{
	signal(SIGPIPE, SIG_IGN);

	if (!parse_args(argc, argv))
	{
		usage(argv);
		return 1;
	}

	open_log(log_file_name);

	if (!read_config_file())
	{
		log_error("Invalid configuraion file\n");
		return 1;
	}

	if (!init_coordinator())
	{
		return 1;
	}

	bool result = run_coordinator_loop();

	cleanup();
	return result ? 0 : 1;
}