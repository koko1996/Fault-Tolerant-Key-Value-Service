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

// The key-value server implementation

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
#include "hash.h"
#include "util.h"

// Program arguments

// Host name and port number of the metadata server
static char coord_host_name[HOST_NAME_MAX] = "";
static uint16_t coord_port = 0;

// Ports for listening to incoming connections from clients, servers and coord
static uint16_t clients_port = 0;
static uint16_t servers_port = 0;
static uint16_t coord_in_port = 0;

// Current server id and total number of servers
static int server_id = -1;
static int num_servers = 0;

// Log file name
static char log_file_name[PATH_MAX] = "";

// Threads
static pthread_t client_handler_thread;
static pthread_t heartbeat_thread;
static pthread_t primary_update_thread;
static pthread_t secondary_update_thread;

// true if the primary server of the secondary_hash is in recovery mode
// false otherwise
static bool updating_primary_server = false;

static void usage(char **argv)
{
	printf("usage: %s -h <coord host> -m <coord port> -c <clients port> "
		   "-s <servers port> -M <coord incoming port> -S <server id> "
		   "-n <num servers> [-l <log file>]\n",
		   argv[0]);
	printf("If the log file (-l) is not specified, log output is written "
		   "to stdout\n");
}

// Returns false if the arguments are invalid
static bool parse_args(int argc, char **argv)
{
	char option;
	while ((option = getopt(argc, argv, "h:m:c:s:M:S:n:l:")) != -1)
	{
		switch (option)
		{
		case 'h':
			strncpy(coord_host_name, optarg, HOST_NAME_MAX);
			break;
		case 'm':
			coord_port = atoi(optarg);
			break;
		case 'c':
			clients_port = atoi(optarg);
			break;
		case 's':
			servers_port = atoi(optarg);
			break;
		case 'M':
			coord_in_port = atoi(optarg);
			break;
		case 'S':
			server_id = atoi(optarg);
			break;
		case 'n':
			num_servers = atoi(optarg);
			break;
		case 'l':
			strncpy(log_file_name, optarg, PATH_MAX);
			break;
		default:
			fprintf(stderr, "Invalid option: -%c\n", option);
			return false;
		}
	}

	// Allow server to choose own ports. Uncomment extra conditions if
	// server ports must be specified on command line.
	return (coord_host_name[0] != '\0') && (coord_port != 0) &&
		   //(clients_port != 0) && (servers_port != 0) &&
		   //(coord_in_port != 0) &&
		   (num_servers >= 3) && (server_id >= 0) && (server_id < num_servers);
}

// Socket for sending requests to the coordinator
static int coord_fd_out = -1;
// Socket for receiving requests from the coordinator
static int coord_fd_in = -1;

// Sockets for listening for incoming connections from clients, servers
// and coordinator
static int my_clients_fd = -1;
static int my_servers_fd = -1;
static int my_coord_fd = -1;

// Store fds for all connected clients, up to MAX_CLIENT_SESSIONS
static int client_fd_table[MAX_CLIENT_SESSIONS];

// Store fds for connected servers
#define MAX_SERVER_SESSIONS 2
static int server_fd_table[MAX_SERVER_SESSIONS] = {-1, -1};

// Storage for this server's primary key set
hash_table primary_hash = {0};
// Storage for this server's secondary key set
hash_table secondary_hash = {0};

// Primary server (the one that stores the primary copy for this server's
// secondary key set)
static int primary_sid = -1;
static int primary_fd = -1;

// Secondary server (the one that stores the secondary copy for this server's
// primary key set)
static int secondary_sid = -1;
static int secondary_fd = -1;

static void cleanup();

static const int hash_size = 65536;

// Function for sending periodic heartbeat messages
static void *heartbeat()
{
	const int MSG_INTERVAL = 2;
	// Make sure the thread executing this function is cancelable 
	pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);
	for (;;)
	{
		char send_buffer[MAX_MSG_LEN] = {0};
		coord_ctrl_request *req = (coord_ctrl_request *)send_buffer;
		req->hdr.type = MSG_COORD_CTRL_REQ;
		req->type = HEARTBEAT;
		req->server_id = server_id;

		if (!send_msg(coord_fd_out, req, sizeof(*req)))
		{
			log_write("Error sending heartbeat message");
		}
		sleep(MSG_INTERVAL);
	}
	return NULL;
}

// Hash iterator for sending (key,value) pairs to fd specified in arg
static void send_key_iterator_f(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg)
{
	assert(key != NULL);

	char req_buffer[MAX_MSG_LEN] = {0};
	operation_request *request = (operation_request *)req_buffer;
	request->type = OP_PUT;
	request->hdr.type = MSG_OPERATION_REQ;
	memcpy(request->key, key, KEY_SIZE);
	strncpy(request->value, value, value_sz);	

	char resp_buffer[MAX_MSG_LEN] = {0};
	operation_response *response = (operation_response *)resp_buffer;
	response->hdr.type = MSG_OPERATION_RESP;
	
	if (!send_msg(*((int *)arg), request, sizeof(*request) + value_sz) ||
		!recv_msg(*((int *)arg), response, sizeof(response), MSG_OPERATION_RESP))
	{
		log_error("failed to send key %s from sid %d as part of recovery\n", key_to_str(request->key), server_id);
	}
}

// Function to send the entries in secondary_hash one by one to primary_fd (i.e. KV_aa)
void * send_secondary_hash_table()
{
	// Make sure the thread executing this function is cancelable 
	pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);

	hash_iterate(&secondary_hash, send_key_iterator_f, &primary_fd);
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request *)send_buffer;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = UPDATED_PRIMARY;
	req->server_id = server_id;

	// updater thread is done sending set secondary_hash to KV_aa, 
	// it contacts CO with an UPDATED_PRIMARY confirmation message
	if (!send_msg(coord_fd_out, req, sizeof(*req)))
	{
		log_error("sid %d: failed sending confirmation for UPDATED_PRIMARY to coordinator \n", server_id);
	}
	return NULL;
}

// Function to send the entries in primary_hash one by one to secondary_fd (i.e. KV_aa)
void * send_primary_hash_table()
{
	// Make sure the thread executing this function is cancelable 
	pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);

	hash_iterate(&primary_hash, send_key_iterator_f, &secondary_fd);
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request *)send_buffer;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = UPDATED_SECONDARY;
	req->server_id = server_id;

	// updater is done sending a secondary copy of primary_hash to KV_aa, 
	// it sends an UPDATED_SECONDARY confirmation message to coordinator
	if (!send_msg(coord_fd_out, req, sizeof(*req)))
	{
		log_error("sid %d: failed sending confirmation for UPDATED_SECONDARY to coordinator \n", server_id);
	}
	return NULL;
}

// Initialize and start the server
static bool init_server()
{
	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++)
	{
		client_fd_table[i] = -1;
	}

	// Get the host name that server is running on
	char my_host_name[HOST_NAME_MAX] = "";
	char timebuf[TIME_STR_SIZE];

	if (get_local_host_name(my_host_name, sizeof(my_host_name)) < 0)
	{
		return false;
	}
	log_write("%s Server starts on host: %s\n",
			  current_time_str(timebuf, TIME_STR_SIZE), my_host_name);

	// Create sockets for incoming connections from clients and other servers
	uint16_t newport = 0;
	my_clients_fd = create_server(clients_port, MAX_CLIENT_SESSIONS, &newport);
	if (my_clients_fd < 0)
	{
		goto cleanup;
	}
	if (newport != 0)
	{
		clients_port = newport;
		newport = 0;
	}

	my_servers_fd = create_server(servers_port, MAX_SERVER_SESSIONS, &newport);
	if (my_servers_fd < 0)
	{
		goto cleanup;
	}
	if (newport != 0)
	{
		servers_port = newport;
		newport = 0;
	}

	my_coord_fd = create_server(coord_in_port, 1, &newport);
	if (my_coord_fd < 0)
	{
		goto cleanup;
	}
	if (newport != 0)
	{
		coord_in_port = newport;
		newport = 0;
	}

	// Determine the ids of replica servers
	primary_sid = primary_server_id(server_id, num_servers);
	secondary_sid = secondary_server_id(server_id, num_servers);

	// Initialize primary key-value storage
	if (!hash_init(&primary_hash, hash_size))
	{
		goto cleanup;
	}

	// Initialize secondary key-value storage
	if (!hash_init(&secondary_hash, hash_size))
	{
		goto cleanup;
	}

	// Connect to coordinator to "register" that we are live
	if ((coord_fd_out = connect_to_server(coord_host_name, coord_port)) < 0)
	{
		goto cleanup;
	}
	// Tell coordinator about the port numbers we are using
	char send_buffer[MAX_MSG_LEN] = {0};
	coord_ctrl_request *req = (coord_ctrl_request *)send_buffer;
	req->hdr.type = MSG_COORD_CTRL_REQ;
	req->type = STARTED;
	req->server_id = server_id;
	req->ports[0] = clients_port;
	req->ports[1] = servers_port;
	req->ports[2] = coord_in_port;

	if (!send_msg(coord_fd_out, req, sizeof(*req) + 3 * sizeof(uint16_t)))
	{
		goto cleanup;
	}

	// Create a thread for sending periodic heartbeat messages
	if (pthread_create(&heartbeat_thread, NULL, heartbeat, NULL))
	{
		log_error("Error creating heartbeat thread\n");
		goto cleanup;
	}

	log_write("Server initialized\n");
	return true;

cleanup:
	log_write("Server initialization failed.\n");
	cleanup();
	return false;
}

// Hash iterator for freeing memory used by values; called during storage cleanup
static void clean_iterator_f(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg)
{
	(void)key;
	(void)value_sz;
	(void)arg;

	assert(value != NULL);
	free(value);
}

// Cleanup and release all the resources
static void cleanup()
{
	log_write("Cleaning up and exiting ...\n");

	close_safe(&coord_fd_out);
	close_safe(&coord_fd_in);
	close_safe(&my_clients_fd);
	close_safe(&my_servers_fd);
	close_safe(&my_coord_fd);
	close_safe(&secondary_fd);
	close_safe(&primary_fd);

	for (int i = 0; i < MAX_CLIENT_SESSIONS; i++)
	{
		close_safe(&(client_fd_table[i]));
	}
	for (int i = 0; i < MAX_SERVER_SESSIONS; i++)
	{
		close_safe(&(server_fd_table[i]));
	}

	hash_iterate(&primary_hash, clean_iterator_f, NULL);
	hash_cleanup(&primary_hash);

	// release all other resources

	hash_iterate(&secondary_hash, clean_iterator_f, NULL);
	hash_cleanup(&secondary_hash);

	pthread_cancel(client_handler_thread);
	pthread_join(client_handler_thread, NULL);

	pthread_cancel(heartbeat_thread);
	pthread_join(heartbeat_thread, NULL);

	pthread_cancel(primary_update_thread);
	pthread_join(primary_update_thread, NULL);

	pthread_cancel(secondary_update_thread);
	pthread_join(secondary_update_thread, NULL);
}

// Connection will be closed after calling this function regardless of result
static void process_client_message(int fd)
{
	char timebuf[TIME_STR_SIZE];

	log_write("%s Receiving a client message\n",
			  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_OPERATION_REQ))
	{
		return;
	}
	operation_request *request = (operation_request *)req_buffer;

	// Initialize the response
	char resp_buffer[MAX_MSG_LEN] = {0};
	operation_response *response = (operation_response *)resp_buffer;
	response->hdr.type = MSG_OPERATION_RESP;
	uint16_t value_sz = 0;

	// primary server id of the key in request
	int key_srv_id = key_server_id(request->key, num_servers);
	// hash table to be used for the key
	hash_table *table_ptr = &primary_hash;
	// fd of the secondary server to be used for replication
	int replica_server_fd = secondary_fd;

	// Check if the primary server of secondary_hash is in recovery mode and the key in 
	// request belongs to secondary_hash
	if (updating_primary_server && server_id == secondary_server_id(key_srv_id, num_servers))
	{
		// act as primary for keys in secondary_hash since we are updating primary server 
		// and any PUT requests for keys in secondary_hash is received by this server
		key_srv_id = server_id;
		table_ptr = &secondary_hash;
		// any PUT requests for keys in secondary_hash are to be sent synchronously to KV_aa
		replica_server_fd = primary_fd;
	}

	// Check that requested key is valid.
	// A server should only respond to requests for which it holds the
	// primary replica after it is initialized and completed the recovery 
	// procedure. For debugging and testing, however, we also want
	// to allow the secondary server to respond to OP_VERIFY requests,
	// to confirm that replication has succeeded. To check this, we need
	// to know the primary server id for which this server is the secondary.
	if (((key_srv_id != server_id) &&
		 ((key_srv_id != primary_sid) || (request->type != OP_VERIFY))) ||
		((key_srv_id == server_id) && (secondary_fd == -1))) // this is a newly setup server still receiving keys
	{
		log_error("sid %d: Invalid client key %s sid %d\n", server_id, key_to_str(request->key), key_srv_id);
		// This can happen if client is using incorrect config 
		response->status = INVALID_REQUEST;
		send_msg(fd, response, sizeof(*response) + value_sz);
		return;
	}

	// Process the request based on its type
	switch (request->type)
	{
	case OP_NOOP:
		response->status = SUCCESS;
		break;

	case OP_GET:
	{
		void *data = NULL;
		size_t size = 0;

		assert(key_srv_id == server_id);
		// Lock to avoid synchronization issues with the server handler thread (i.e. main thread)
		hash_lock(table_ptr, request->key);
		// Get the value for requested key from the hash table
		if (!hash_get(table_ptr, request->key, &data, &size))
		{
			// unlcok as we are done
			hash_unlock(table_ptr, request->key);
			log_write("Key %s not found\n", key_to_str(request->key));
			response->status = KEY_NOT_FOUND;
			break;
		}

		// Copy the stored value into the response buffer
		memcpy(response->value, data, size);
		value_sz = size;
		// unlcok as we are done
		hash_unlock(table_ptr, request->key);

		response->status = SUCCESS;
		break;
	}

	case OP_PUT:
	{
		// Need to copy the value to dynamically allocated memory
		size_t value_size = request->hdr.length - sizeof(*request);
		void *value_copy = malloc(value_size);

		assert(key_srv_id == server_id);

		if (value_copy == NULL)
		{
			log_perror("malloc");
			log_error("sid %d: Out of memory\n", server_id);
			response->status = OUT_OF_SPACE;
			break;
		}
		memcpy(value_copy, request->value, value_size);

		void *old_value = NULL;
		size_t old_value_sz = 0;
		
		// Lock to avoid synchronization issues with the server handler thread (i.e. main thread)
		hash_lock(table_ptr, request->key);
		// Put the <key, value> pair into the hash table
		if (!hash_put(table_ptr, request->key, value_copy, value_size, &old_value, &old_value_sz))
		{
			// unlock as we are done
			hash_unlock(table_ptr, request->key);
			log_error("sid %d: Out of memory\n", server_id);
			free(value_copy);
			response->status = OUT_OF_SPACE;
			break;
		}
		// Need to free the old value (if there was any)
		if (old_value != NULL)
		{
			free(old_value);
		}
		// unlock as we are done
		hash_unlock(table_ptr, request->key);

		
		char recv_buffer[MAX_MSG_LEN] = {0};
		// Use the same request
		if (!send_msg(replica_server_fd, request, sizeof(*request) + value_size) ||
			!recv_msg(replica_server_fd, recv_buffer, sizeof(recv_buffer), MSG_OPERATION_RESP))
		{
			log_error("sid %d: failed to forward key:%s to replicate\n", server_id, key_to_str(request->key));
			response->status = SERVER_FAILURE;
			break;
		}

		operation_response *replicate_response = (operation_response *)recv_buffer;
		if (replicate_response->status != SUCCESS)
		{
			log_error("sid %d: replication of key:%s failed at the receving server\n", server_id, key_to_str(request->key));
			response->status = SERVER_FAILURE;
			break;
		}

		response->status = SUCCESS;
		break;
	}

	case OP_VERIFY:
	{
		// Checked for invalid OP_VERIFY earlier. Now just check
		// if we are primary or secondary for this key.
		if (key_srv_id == server_id)
		{
			// Handle just like a GET request
			void *data = NULL;
			size_t size = 0;

			// Get the value for key from the primary hash table
			hash_lock(table_ptr, request->key); 
			if (!hash_get(table_ptr, request->key, &data, &size))
			{
				hash_unlock(table_ptr, request->key);
				log_write("Key %s not found\n",
						  key_to_str(request->key));
				response->status = KEY_NOT_FOUND;
			}
			else
			{
				// Copy the value into the response buffer
				memcpy(response->value, data, size);
				value_sz = size;
				hash_unlock(table_ptr, request->key);
				response->status = SUCCESS;
			}
		}
		else if (key_srv_id == primary_sid)
		{
			// Server should hold secondary replica of key
			// Process like a GET request, using secondary keys.
			// Will not be executed during recovery when this server
			// is primary for both hash tables
			void *data = NULL;
			size_t size = 0;
			
			// Lock to avoid synchronization issues with the server handler thread (i.e. main thread)
			hash_lock(&secondary_hash, request->key);
			// Get the value for key from the primary hash table
			if (!hash_get(&secondary_hash, request->key, &data, &size))
			{
				hash_unlock(&secondary_hash, request->key);
				response->status = KEY_NOT_FOUND;
				log_write("Key %s not found in secondary hash table\n", key_to_str(request->key));
			}
			else
			{
				// Copy the value into the response buffer
				memcpy(response->value, data, size);
				value_sz = size;
				// Unlock the bucket since we are done
				hash_unlock(&secondary_hash, request->key);
				response->status = SUCCESS;
				log_write("Key %s found in secondary hash table\n", key_to_str(request->key));
			}
		}
		else
		{
			// Should not be possible if logic for checking
			// invalid request prior to switch is correct.
			log_error("invalid request handling is inccorect \n");
			assert(false);
		}
		break;
	}
	default:
		log_error("sid %d: Invalid client operation type\n", server_id);
		return;
	}

	// Send reply to the client	
	send_msg(fd, response, sizeof(*response) + value_sz);
}

// Returns false if either the message was invalid or if this was the last message
// (in both cases the connection will be closed)
static bool process_server_message(int fd)
{
	char timebuf[TIME_STR_SIZE];

	log_write("%s Receiving a server message\n",
			  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_OPERATION_REQ))
	{
		return false;
	}
	operation_request *request = (operation_request *)req_buffer;

	// process the message and send the response

	char resp_buffer[MAX_MSG_LEN] = {0};
	operation_response *response = (operation_response *)resp_buffer;
	response->hdr.type = MSG_OPERATION_RESP;
	uint16_t value_sz = 0;

	int key_srv_id = key_server_id(request->key, num_servers);

	hash_table *table_ptr = &primary_hash;
	if (server_id == secondary_server_id(key_srv_id, num_servers))
	{
		table_ptr = &secondary_hash;
	}

	// Process the request based on its type
	switch (request->type)
	{
	case OP_NOOP: // NOOP operation request is used to indicate the last message in an UPDATE sequence
		log_write("Received the last server message, closing connection\n");
		return false;

	case OP_PUT:
	{
		// Need to copy the value to dynamically allocated memory
		size_t value_size = request->hdr.length - sizeof(*request);
		void *value_copy = malloc(value_size);

		if (value_copy == NULL)
		{
			log_perror("malloc");
			log_error("sid %d: Out of memory\n", server_id);
			response->status = OUT_OF_SPACE;
			break;
		}
		memcpy(value_copy, request->value, value_size);

		void *old_value = NULL;
		size_t old_value_sz = 0;

		// Lock to avoid synchronization issues with the client handler thread and recovery thread
		hash_lock(table_ptr, request->key);
		// Put the <key, value> pair into the hash table
		if (!hash_put(table_ptr, request->key, value_copy, value_size, &old_value, &old_value_sz))
		{
			hash_unlock(table_ptr, request->key);
			log_error("sid %d: Out of memory\n", server_id);
			free(value_copy);
			response->status = OUT_OF_SPACE;
			break;
		}

		// Need to free the old value (if there was any)
		if (old_value != NULL)
		{
			free(old_value);
		}
		hash_unlock(table_ptr, request->key);

		response->status = SUCCESS;
		break;
	}

	default:
		// server can only send OP_PUT and OP_NOOP to another server
		log_error("sid %d: Invalid server operation type:%d \n", server_id, request->type);
		return false;
	}
	// Send reply to the server
	send_msg(fd, response, sizeof(*response) + value_sz);
	return true;
}

// Hash iterator for printing keys into the file pointer passed as arg
static void print_key_iterator_f(const char key[KEY_SIZE], void *value, size_t value_sz, void *arg)
{
	(void)key;
	(void)value;
	(void)value_sz;

	assert(key != NULL);
	fprintf(arg, "key:%s\n", key_to_str(key));
}

// Helper function to write primary keys from hash table to file, 
// overwriting any previous content in the output file.
static void dump_keys(hash_table *table, bool is_primary)
{
	FILE *fp;
	char filename[30] = "";
	if (is_primary)
	{
		// The output file should be named "server_<sid>.primary",
		// where <sid> is the server id number of this server.
		snprintf(filename, 30, "server_%d.primary", server_id);
	}
	else
	{
		// The output file should be named "server_<sid>.secondary",
		// where <sid> is the server id number of this server.
		snprintf(filename, 30, "server_%d.secondary", server_id);
	}

	fp = fopen(filename, "w");

	if (fp == NULL)
	{
		log_error("Error opening file to dump keys: %s\n", strerror(errno));
	}
	else
	{
		hash_iterate(table, print_key_iterator_f, fp);
		fclose(fp);
	}
}

// Returns false if the message was invalid (so the connection will be closed)
// Sets *shutdown_requested to true if received a SHUTDOWN message (so the server will terminate)
static bool process_coordinator_message(int fd, bool *shutdown_requested)
{
	char timebuf[TIME_STR_SIZE];

	assert(shutdown_requested != NULL);
	*shutdown_requested = false;

	log_write("%s Receiving a coordinator message\n",
			  current_time_str(timebuf, TIME_STR_SIZE));

	// Read and parse the message
	char req_buffer[MAX_MSG_LEN] = {0};
	if (!recv_msg(fd, req_buffer, MAX_MSG_LEN, MSG_SERVER_CTRL_REQ))
	{
		return false;
	}
	server_ctrl_request *request = (server_ctrl_request *)req_buffer;

	// Initialize the response
	server_ctrl_response response = {0};
	response.hdr.type = MSG_SERVER_CTRL_RESP;
	response.status = SERVER_CTRLREQ_STATUS_MAX; // Detect unset status

	// Process the request based on its type
	switch (request->type)
	{
	case SET_SECONDARY:
		if ((secondary_fd = connect_to_server(request->host_name,
											  request->port)) < 0)
		{
			response.status = CTRLREQ_FAILURE;
		}
		else
		{
			response.status = CTRLREQ_SUCCESS;
		}
		break;

	case UPDATE_PRIMARY:
		// denote that the primary is being updated (i.e. in recovery)
		updating_primary_server = true;
		// update the primary_fd since there is a new server 
		primary_fd = connect_to_server(request->host_name, request->port);
		if (primary_fd < 0)
		{
			response.status = CTRLREQ_FAILURE; 
			break;
		}
		// spawns a new thread to asynchronously send its secondary_hash to the new server
		if (pthread_create(&primary_update_thread, NULL, (void *)send_secondary_hash_table, NULL))
		{
			log_error("Error creating asynchronously updater thread\n");
			response.status = CTRLREQ_FAILURE; 
			break;
		}

		// send a confirmation back to coordinator to indicate that we received the UPDATE_PRIMARY message
		response.status = CTRLREQ_SUCCESS;
		break;

	case UPDATE_SECONDARY:
		// update the secondary_fd since there is a new server 
		secondary_fd = connect_to_server(request->host_name, request->port);
		if (secondary_fd < 0)
		{
			response.status = CTRLREQ_FAILURE;
			break;
		}
		// spawns a new thread to asynchronously send its primary_hash to the new server
		if (pthread_create(&secondary_update_thread, NULL, (void *)send_primary_hash_table, NULL))
		{
			log_error("Error creating asynchronously updater thread\n");
			response.status = CTRLREQ_FAILURE; 
			break;
		}

		// confirm the UPDATE_SECONDARY message by sending a confirmation message to coordinator
		response.status = CTRLREQ_SUCCESS;

		break;

	case SWITCH_PRIMARY:
		// finish any in-flight PUT requests and stop acting as the primary for secondary_hash
		// Denote that primary server is done updating any clients that issue PUT requests for keys 
		// in secondary_hash after next instruction is executed will receive an 'invalid request' response
		updating_primary_server = false;
		// send a confirmation message to coordinator indicating that the SWITCH_PRIMARY message was handled
		response.status = CTRLREQ_SUCCESS;
		response.hdr.type = MSG_SERVER_CTRL_RESP;

		break;

	case SHUTDOWN:
		*shutdown_requested = true;
		return true;

	case DUMP_PRIMARY:
		// write primary keys from hash table to file, overwriting
		// any previous content in the output file.
		// The output file should be named "server_<sid>.primary",
		// where <sid> is the server id number of this server.
		// No response is expected, so after dumping keys, just return.
		dump_keys(&primary_hash, true);
		return true;

	case DUMP_SECONDARY:
		// write secondary keys from hash table to file, overwriting
		// any previous content in the output file.
		// The output file should be named "server_<sid>.secondary",
		// where <sid> is the server id number of this server.
		// No response is expected, so after dumping keys, just return.
		dump_keys(&secondary_hash, false);
		return true;

	default: // impossible
		assert(false);
		break;
	}

	assert(response.status != SERVER_CTRLREQ_STATUS_MAX);

	send_msg(fd, &response, sizeof(response));
	return true;
}

static void *run_client_request_loop()
{
	// Make sure the thread executing this function is cancelable 
	pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);

	// Usual preparation stuff for select()
	fd_set rset, allset;
	FD_ZERO(&allset);
	FD_SET(my_clients_fd, &allset);

	int maxfd = my_clients_fd;

	// Server sits in an infinite loop waiting for incoming connections
	// from coordinator or clients, and for incoming messages from already
	// connected coordinator or clients
	//

	for (;;)
	{

		rset = allset;

		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, NULL);
		if (num_ready_fds < 0)
		{
			log_perror("select");
			return false;
		}

		if (num_ready_fds <= 0)
		{
			continue;
		}

		// Incoming connection from a client
		if (FD_ISSET(my_clients_fd, &rset))
		{
			int fd_idx = accept_connection(my_clients_fd, client_fd_table, MAX_CLIENT_SESSIONS);
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
			if ((client_fd_table[i] != -1) && FD_ISSET(client_fd_table[i], &rset))
			{
				process_client_message(client_fd_table[i]);
				// Close connection after processing (semantics are "one connection per request")
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

// Returns false if stopped due to errors, true if shutdown was requested
static bool run_server_loop()
{
	// Usual preparation stuff for select()
	fd_set rset, allset;
	FD_ZERO(&allset);
	FD_SET(my_coord_fd, &allset);
	FD_SET(my_servers_fd, &allset);

	int maxfd = max(my_coord_fd, my_servers_fd);

	// Server sits in an infinite loop waiting for incoming connections
	// from coordinator or clients, and for incoming messages from already
	// connected coordinator or clients
	//
	for (;;)
	{
		rset = allset;

		int num_ready_fds = select(maxfd + 1, &rset, NULL, NULL, NULL);
		if (num_ready_fds < 0)
		{
			log_perror("select");
			return false;
		}

		if (num_ready_fds <= 0)
		{
			continue;
		}

		// Incoming connection from the coordinator
		if (FD_ISSET(my_coord_fd, &rset))
		{
			int fd_idx = accept_connection(my_coord_fd, &coord_fd_in, 1);
			if (fd_idx >= 0)
			{
				FD_SET(coord_fd_in, &allset);
				maxfd = max(maxfd, coord_fd_in);
			}
			assert(fd_idx == 0);

			if (--num_ready_fds <= 0)
			{
				continue;
			}
		}

		// Check for any messages from the coordinator
		if ((coord_fd_in != -1) && FD_ISSET(coord_fd_in, &rset))
		{
			bool shutdown_requested = false;
			if (!process_coordinator_message(coord_fd_in,
											 &shutdown_requested))
			{
				// Received an invalid message, close the connection
				log_error("sid %d: Closing coordinator connection\n", server_id);
				FD_CLR(coord_fd_in, &allset);
				close_safe(&(coord_fd_in));
			}
			else if (shutdown_requested)
			{
				return true;
			}

			if (--num_ready_fds <= 0)
			{
				continue;
			}
		}

		// Incoming connection from servers
		if (FD_ISSET(my_servers_fd, &rset))
		{
			int fd_idx = accept_connection(my_servers_fd, server_fd_table, MAX_SERVER_SESSIONS);
			if (fd_idx >= 0)
			{
				FD_SET(server_fd_table[fd_idx], &allset);
				maxfd = max(maxfd, server_fd_table[fd_idx]);
			}

			if (--num_ready_fds <= 0)
			{
				continue;
			}
		}

		// Check for any messages from connected servers
		for (int i = 0; i < MAX_SERVER_SESSIONS; i++)
		{
			if ((server_fd_table[i] != -1) && FD_ISSET(server_fd_table[i], &rset))
			{
				if (!process_server_message(server_fd_table[i]))
				{
					log_error("sid %d: closing connection to server %d\n", server_id, i);
					FD_CLR(server_fd_table[i], &allset);
					close_safe(&(server_fd_table[i]));
				}

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

	if (!init_server())
	{
		return 1;
	}
	// start the client handler thread
	if (pthread_create(&client_handler_thread, NULL, (void *)run_client_request_loop, NULL))
	{
		log_error("Error creating client handler thread\n");
		cleanup();
		return 1;
	}

	bool result = run_server_loop();

	cleanup();
	return result ? 0 : 1;
}
