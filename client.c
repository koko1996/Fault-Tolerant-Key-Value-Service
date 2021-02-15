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

// A simple client program that uses the key-value service

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "defs.h"
#include "md5.h"
#include "util.h"

// Program arguments

// Host name and port number of the coordinator
static char coord_host_name[HOST_NAME_MAX] = "";
static uint16_t coord_port = 0;

// Operations file to be executed; if not specified, the client interactively reads input from stdin
static char ops_file_name[PATH_MAX] = "";
// Log file name
static char log_file_name[PATH_MAX] = "";

// Client's view of the service configuration, initialized using coordinator's
// response to MSG_CONFIG_REQ
static int num_servers = 0;			// number of key-value servers configured in service
static config_entry *config = NULL; // array of num_servers config_entry structs

static void usage(char **argv)
{
	printf("usage: %s -h <coord host name> -p <coord port> [-f <operations file> -l <log file>]\n", argv[0]);
	printf("If the operations file (-f) is not specified, the input is read from stdin\n");
	printf("If the log file (-l) is not specified, log output is written to stdout\n");
}

// Returns false if the arguments are invalid
static bool parse_args(int argc, char **argv)
{
	char option;
	while ((option = getopt(argc, argv, "h:p:f:l:")) != -1)
	{
		switch (option)
		{
		case 'h':
			strncpy(coord_host_name, optarg, HOST_NAME_MAX);
			break;
		case 'p':
			coord_port = atoi(optarg);
			break;
		case 'f':
			strncpy(ops_file_name, optarg, PATH_MAX);
			break;
		case 'l':
			strncpy(log_file_name, optarg, PATH_MAX);
			break;
		default:
			fprintf(stderr, "Invalid option: -%c\n", option);
			return false;
		}
	}

	return (coord_host_name[0] != '\0') && (coord_port != 0);
}

// Operation types (in the operation file format)
#define OP_TYPE_NOOP '0'
#define OP_TYPE_GET 'G'
#define OP_TYPE_PUT 'P'

// VERIFY is a special type of operation for checking consistency.
// The 'value' field is the expected value.
// Unlike in ex3, it is sent as a distinct VERIFY operation. This allows 'VERIFY'
// to be sent to either the primary or secondary replica of a key, for testing
// that replication is being carried out correctly by the servers.
// The result is checked against the expected value.
#define OP_TYPE_VERIFY 'V'

static op_type get_op_type(char type)
{
	switch (type)
	{
	case OP_TYPE_NOOP:
		return OP_NOOP;
	case OP_TYPE_GET:
		return OP_GET;
	case OP_TYPE_VERIFY:
		return OP_VERIFY;
	case OP_TYPE_PUT:
		return OP_PUT;
	default:
		return -1;
	}
}

// Maximum length of a string describing an operation
#define MAX_STR_LEN 2048

// Keys and values used by this client are non-empty null-terminated strings
// " " is a special value for VERIFY operations meaning that the key shouldn't exist
typedef struct _operation
{
	char key[MAX_STR_LEN];
	char value[MAX_STR_LEN];
	char type; // noop/get/put/verify
	int count;
	int index; // corresponds to line number in the operation file
} operation;

typedef struct _result
{
	char value[MAX_STR_LEN];
	op_status status;
} result;

// Read a key-value operation from the given string. Returns false if the input doesn't match the format
static bool parse_operation(const char *str, operation *op)
{
	assert(str != NULL);
	assert(op != NULL);

	// Format: {0|G|P|C} "<key>" ["<value>" <count>]
	// See 'man 2 scanf' for the matching string format description
	//
	// NOTE: no need to limit the length of strings being read since both the 'op->key'
	//       and 'op->value' buffers have the same length as the whole input string
	int matches_num = sscanf(str, " %c \"%[^\"]\" \"%[^\"]\" %d", &(op->type), op->key, op->value, &(op->count));
	if (matches_num < 1)
	{ // no type
		return false;
	}

	if (matches_num < 4)
	{ // count not specified
		op->count = 1;
	}
	if (op->count <= 0)
	{
		return false;
	}

	// " " is a special value; set it to an empty string for simplicity
	// Also need to ignore the value for NOOP and GET
	if ((strcmp(op->value, " ") == 0) || (op->type == OP_TYPE_NOOP) || (op->type == OP_TYPE_GET))
	{
		op->value[0] = '\0';
	}

	switch (op->type)
	{
	case OP_TYPE_NOOP:
	case OP_TYPE_GET:
		// no value needed (unless need to specify count)
		return matches_num >= 2;
	case OP_TYPE_VERIFY:
		return matches_num >= 3;
	case OP_TYPE_PUT:
		// value must be non-empty
		return (matches_num >= 3) && (op->value[0] != '\0');
	default:
		return false;
	}
}

// Contact coordinator and obtain the current service configuration.
// Returns true if a valid configuration was retrieved from the coordinator.
static bool get_config()
{
	int coord_fd = connect_to_server(coord_host_name, coord_port);
	if (coord_fd < 0)
	{
		return false;
	}

	config_request request = {0};
	request.hdr.type = MSG_CONFIG_REQ;

	char recv_buffer[MAX_MSG_LEN] = {0};
	if (!send_msg(coord_fd, &request, sizeof(request)) ||
		!recv_msg(coord_fd, recv_buffer, sizeof(recv_buffer), MSG_CONFIG_RESP))
	{
		close(coord_fd);
		return false;
	}

	close(coord_fd); // one request per connection
	config_response *response = (config_response *)recv_buffer;

	if (config == NULL)
	{
		// Might request config many times, but number of servers can't
		// change dynamically, so only need to allocate memory for it once.
		num_servers = response->num_entries;
		assert(num_servers >= 3);
		config = (config_entry *)calloc(num_servers, sizeof(config_entry));
		if (config == NULL)
		{
			return false;
		}
	}
	else
	{
		// Make sure number of servers has not changed
		assert(num_servers == response->num_entries);
		// zero out previous config
		memset(config, 0, num_servers * sizeof(config_entry));
	}

	// Now we need to extract host names and ports from the response
	// Need to first set up an array of structures to hold server/port info
	char *entry_start = response->entry_buffer;
	for (int i = 0; i < num_servers; i++)
	{
		int matches;
		int nscanned;
		char fmtstr[20];
		// Ugly, but gets HOST_NAME_MAX-1 into width specifier for string
		sprintf(fmtstr, "%%%ds %%hu;%%n", HOST_NAME_MAX);

		// Use sscanf on the response buffer to fill in values
		matches = sscanf(entry_start, fmtstr,
						 &config[i].host, &config[i].port, &nscanned);
		if (matches != 2)
		{
			// something went wrong...
			return false;
		}
		entry_start += nscanned;
	}

	return true;
}

static int get_key_server(const char key[KEY_SIZE])
{
	int sid;
	assert(key != NULL);

	if (config == NULL)
	{
		if (get_config() == false)
		{
			return -1;
		}
	}

	assert(num_servers >= 3);
	assert(config != NULL);

	sid = key_server_id(key, num_servers);
	// index into config array and return
	return connect_to_server(config[sid].host, config[sid].port);
}

// Send a GET/PUT operation to the server (connected to via server_fd) and get reply back
// Fills the result with the server's response
// Returns true if the operation was successfully executed (but not necessarily with a SUCCESS status)
// If the server fails to respond, fills the result status with SERVER_FAILURE and returns false
static bool send_operation(int server_fd, const char key[KEY_SIZE], const operation *op, result *res)
{
	assert(key != NULL);
	assert(op != NULL);
	assert(res != NULL);

	char send_buffer[MAX_MSG_LEN] = {0};
	operation_request *request = (operation_request *)send_buffer;
	request->hdr.type = MSG_OPERATION_REQ;
	request->type = get_op_type(op->type);
	memcpy(request->key, key, KEY_SIZE);

	// Need to copy the value, only for PUT operations
	int value_sz = 0;
	if (request->type == OP_PUT)
	{
		value_sz = strlen(op->value) + 1;
		strncpy(request->value, op->value, value_sz);
	}

	char recv_buffer[MAX_MSG_LEN] = {0};
	if (!send_msg(server_fd, request, sizeof(*request) + value_sz) ||
		!recv_msg(server_fd, recv_buffer, sizeof(recv_buffer), MSG_OPERATION_RESP))
	{
		res->status = SERVER_FAILURE;
		return false;
	}

	operation_response *response = (operation_response *)recv_buffer;
	res->status = response->status;
	value_sz = response->hdr.length - sizeof(operation_response);
	strncpy(res->value, response->value, value_sz);

	// A key-value server can return the INVALID_REQUEST status if it
	// is not the correct primary for the requested key. It can also
	// return SERVER_FAILURE even if the server is alive
	// (e.g. if it fails to forward a PUT operation to its secondary replica)
	return ((res->status != INVALID_REQUEST) &&
			(res->status != SERVER_FAILURE));
}

// Contact the key-value server, get response
static bool execute_operation(const operation *op, result *res)
{
	assert(op != NULL);

	char *key = (char *)md5sum((const unsigned char *)op->key, 0);
	log_write("\"%s\" -> %s\n", op->key, key_to_str(key));

	int server_fd = get_key_server(key);
	if (server_fd < 0)
	{
		free(key);
		res->status = SERVER_FAILURE;
		return false;
	}

	bool send_result = send_operation(server_fd, key, op, res);
	close(server_fd); // one request per connection

	// OP_VERIFY should also be sent to the secondary server for key.
	// Note that OP_VERIFY is not expected to work on the secondary
	// (as calculated in the client, using the configuration information)
	// during failure recovery, when servers are temporarily filling
	// additional roles. An error response to OP_VERIFY from a secondary
	// should not be catastrophic.
	// We expect to use OP_VERIFY to test that replication is happening
	// correctly during normal (failure-free) operation.
	//
	// Compare results returned from primary and secondary to check that they
	// are the same. If not, log a "primary-secondary mismatch for key" message.
	//
	// Return the results from executing the operation on the primary server.

	/// Get the secondary server id for this key
	int secondary_id = secondary_server_id(key_server_id(key, num_servers), num_servers);

	if (config == NULL)
	{
		if (get_config() == false)
		{
			free(key);
			log_error("Client could not get the config file\n");
			return send_result;
		}
	}
	// Get the fd of the secondary server for this key
	int secondary_fd = connect_to_server(config[secondary_id].host, config[secondary_id].port);
	if (secondary_fd < 0)
	{

		free(key);
		log_error("Client could not connect to the secondary server\n");
		return send_result;
	}

	// Create the verify operation
	operation verify_op = {0};
	verify_op.count = op->count;
	verify_op.type = OP_TYPE_VERIFY;

	result verify_res = {0};
	// Send the verify operation
	if (!send_operation(secondary_fd, key, &verify_op, &verify_res))
	{
		free(key);
		log_error("Client could not send verify operation to the secondary server\n");
		return send_result;
	}

	// Check the result of verify op
	if (verify_res.status == KEY_NOT_FOUND)
	{
		log_write("primary-secondary mismatch for key %s\n", key_to_str(op->key));
	}

	close(secondary_fd); // one request per connection
	free(key);
	return send_result;
}

// Time (in seconds) between reconnection attempts
static const int retry_interval = 1;

// If the key-value server times out or fails, retry the coordinator
static bool execute_operation_retry(const operation *op, result *res, int attempts)
{
	for (int i = 0; i < attempts; i++)
	{
		if (execute_operation(op, res))
		{
			return true;
		}
		if (i < attempts - 1)
		{
			log_write("Failed to execute operation #%d, retrying ...\n", op->index);
			if (config != NULL )
			{
				// free the old config
				free(config);
				config = NULL;
			}
			sleep(retry_interval);
		}
	}

	res->status = SERVER_FAILURE;
	return false;
}

static void report_operation_failure(int index, op_status status)
{
	assert(status < OP_STATUS_MAX);
	log_error("Operation #%d failed with: %s\n", index, op_status_str[status]);
}

// Validate and output the result of an operation
static bool check_operation_result(const operation *op, const result *res, bool interactive)
{
	assert(op != NULL);
	assert(res != NULL);

	// Check if the operation succeeded (except for the special case of
	// VERIFY with no value)
	if ((res->status != SUCCESS) &&
		!((op->type == OP_TYPE_VERIFY) && (op->value[0] == '\0')))
	{
		report_operation_failure(op->index, res->status);
		return false;
	}

	switch (op->type)
	{
	case OP_TYPE_NOOP:
		return true;

	case OP_TYPE_GET:
		if (interactive)
			printf("value[\"%s\"] == \"%s\"\n", op->key, res->value);
		log_write("value[\"%s\"] == \"%s\"\n", op->key, res->value);
		return true;

	case OP_TYPE_PUT:
		if (interactive)
			printf("value[\"%s\"] <- \"%s\"\n", op->key, op->value);
		log_write("value[\"%s\"] <- \"%s\"\n", op->key, op->value);
		return true;

	case OP_TYPE_VERIFY:
		if (op->value[0] == '\0')
		{
			// Expect KEY_NOT_FOUND as the result
			if (res->status == KEY_NOT_FOUND)
			{
				if (interactive)
					printf("Check #%d passed: key \"%s\" not found\n", op->index, op->key);
				log_write("Check #%d passed: key \"%s\" not found\n", op->index, op->key);
				return true;
			}
			if (res->status == SUCCESS)
			{
				log_error("Check #%d failed: value[\"%s\"] == \"%s\" != none\n", op->index, op->key, res->value);
				return false;
			}
			report_operation_failure(op->index, res->status);
			return false;
		}

		if (strcmp(op->value, res->value) == 0)
		{
			if (interactive)
				printf("Check #%d passed: value[\"%s\"] == \"%s\"\n", op->index, op->key, res->value);
			log_write("Check #%d passed: value[\"%s\"] == \"%s\"\n", op->index, op->key, res->value);
			return true;
		}
		log_error("Check #%d failed: value[\"%s\"] == \"%s\" != \"%s\"\n", op->index, op->key, res->value, op->value);
		return false;

	default: // impossible
		assert(false);
		return false;
	}
}

static void prompt(FILE *input)
{
	if (input == stdin)
	{
		printf("> ");
		fflush(stdout);
	}
}

// The number of attempts to execute the operation before giving up
static const int max_attempts = 10;

// The number of failed operations before stopping the client
static const int max_failed_ops = 2;

// Read and execute a set of operations from given input stream; returns true if no failures occured
static bool execute_operations(FILE *input)
{
	assert(input != NULL);
	bool success = true;
	int failed_ops_count = 0;

	int index = 1;
	char line[MAX_STR_LEN] = "";
	prompt(input);
	while (fgets(line, sizeof(line), input) != NULL)
	{
		// Remove trailing '\n'
		size_t len = strnlen(line, sizeof(line));
		if (line[len - 1] == '\n')
		{
			line[len - 1] = '\0';
		}

		// Skip empty lines
		if (line[0] == '\0')
		{
			goto next;
		}

		// Parse next operation
		operation op = {0};
		if (!parse_operation(line, &op))
		{
			log_error("Invalid operation format\n");
			goto next;
		}
		op.index = index++;

		// Print operation if not interactive
		if (input != stdin)
		{
			printf("#%d: %c \"%s\" \"%s\" %d\n", op.index, op.type, op.key, op.value, op.count);
		}

		// Execute the operation (possibly multiple times)
		for (int i = 0; i < op.count; i++)
		{
			result res = {0};
			if (execute_operation_retry(&op, &res, max_attempts))
			{
				if (!check_operation_result(&op, &res, input == stdin))
				{
					failed_ops_count++;
					success = false;
				}
			}
			else
			{
				assert(res.status == SERVER_FAILURE);
				report_operation_failure(op.index, res.status);
				failed_ops_count++;
				success = false;
			}

			// Stop after failures if not interactive
			if ((input != stdin) && (failed_ops_count >= max_failed_ops))
				break;
		}

		// Stop after failures if not interactive
		if ((input != stdin) && (failed_ops_count >= max_failed_ops))
		{
			assert(!success);
			log_error("%d operations failed, exiting\n", failed_ops_count);
			break;
		}

	next:
		prompt(input);
	}

	printf("\n");
	return success;
}

int main(int argc, char **argv)
{
	signal(SIGPIPE, SIG_IGN);

	if (!parse_args(argc, argv))
	{
		usage(argv);
		return 1;
	}

	// Canonicalize "localhost"
	if (strcmp(coord_host_name, "localhost") == 0)
	{
		// Canonicalize host name for 'localhost'
		if (get_local_host_name(coord_host_name, HOST_NAME_MAX) < 0)
		{
			log_error("Could not canonicalize localhost");
			return 1;
		}
	}

	open_log(log_file_name);

	bool success = false;
	// If the operation file is not given, read input from stdin
	if (ops_file_name[0] != '\0')
	{
		FILE *ops_file = fopen(ops_file_name, "r");
		if (ops_file == NULL)
		{
			perror(ops_file_name);
			return 1;
		}

		log_write("Reading input from %s\n", ops_file_name);
		success = execute_operations(ops_file);

		fclose(ops_file);
	}
	else
	{
		success = execute_operations(stdin);
	}

	// Return 0 only if no failures occured
	return success ? 0 : 1;
}
