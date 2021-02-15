// Copyright (C) 2016, 2017 Alexey Khrabrov, Bogdan Simion
//                     2020 Angela Demke Brown
//
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


// Various helper functions used by the programs (client, server, coordinator)

#define _GNU_SOURCE

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <netdb.h>
#include <arpa/inet.h>

#include "util.h"


static FILE *log_file = NULL;

// If the log file is not specified or can't be opened,
// the log output is directed to stdout.
void open_log(const char *file_name)
{
	if ((file_name == NULL) || (file_name[0] == '\0')) {
		log_file = stdout;
		return;
	}

	if ((log_file = fopen(file_name, "a+")) == NULL) {
		perror(file_name);
		log_file = stdout;
	}
}

// Write a message to the log file
// Accepts a variable-length list of arguments (like printf)
void log_write(const char *format, ...)
{
	assert(format != NULL);

	if (log_file != NULL) {
		va_list args;
		va_start(args, format);
		vfprintf(log_file, format, args);
		va_end(args);

#ifndef NDEBUG
		// Flush the buffer (debug builds only)
		log_flush();
#endif
	}
}

// Flush buffered log output to the file
void log_flush()
{
	if (log_file != NULL) {
		fflush(log_file);
	}
}

// perror()-style function for writing errors to both stderr and the log file
// Prefixes messages with the pid of the calling process, so that you can
// distinguish between messages from coordinator and servers; pids of the server
// processes are available in coord.c in the server_node structs
void log_perror(const char *function)
{
	char timebuf[TIME_STR_SIZE];
	char msg[1024];
	snprintf(msg, sizeof(msg), "%s [%d] %s failed with %d: %s\n",
		 current_time_str(timebuf, TIME_STR_SIZE), getpid(), function,
		 errno, strerror(errno));
	log_error("%s", msg);
}

// Same as log_perror, but for functions that report addrinfo errors
void log_gai_error(const char *function, int err)
{
	char timebuf[TIME_STR_SIZE];
	char msg[1024];
	snprintf(msg, sizeof(msg), "%s [%d] %s failed with %d: %s\n",
		 current_time_str(timebuf, TIME_STR_SIZE), getpid(), function,
		 err, gai_strerror(err));
	log_error("%s", msg);
}


// Convert a key to its string representation. This is intended for
// printing information (e.g., for debugging) about the server operation.
char *key_to_str_buffer(const char key[KEY_SIZE], char *buffer, size_t length)
{
	assert(buffer != NULL);
	assert(length != 0);

	char *c = buffer;
	for (int i = 0; i < KEY_SIZE; i++) {
		c += snprintf(c, length - (c - buffer), "%02hhx", key[i]);
	}
	return buffer;
}

// Get current time string in the 'ctime' format (but without the trailing '\n').
// On success, returns a pointer to the string pointed to by buf
// (this is the same behavior as ctime_r).
// Buffer for time string, buf, must have space for at least TIME_STR_SIZE bytes.
// This function is thread-safe. 
char *current_time_str(char *buf, size_t length)
{	
	assert(length >= TIME_STR_SIZE); 

	time_t now = time(NULL);
	char *str = ctime_r(&now, buf);
	assert(str != NULL);

	// Remove trailing '\n'
	size_t len = strlen(str);
	if (str[len - 1] == '\n') {
		str[len - 1] = '\0';
	}

	return str;
}


// Connect to a TCP server given its host name and port number.
// Returns a connected socket fd.
int connect_to_server(const char *host_name, uint16_t port)
{
	struct addrinfo hints, *addrs, *p;
	int sockfd = -1;
	char port_str[10];
	int err;
	
	assert(host_name != NULL);

	// Resolve the host name
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = AF_UNSPEC;     // either IPv4 or IPv6
	hints.ai_socktype = SOCK_STREAM; // TCP stream sockets
	hints.ai_protocol = IPPROTO_TCP;
	snprintf(port_str, 10, "%hu", port);
	
	if ((err = getaddrinfo(host_name, port_str, &hints, &addrs)) != 0) {
		log_gai_error("getaddrinfo", err);
		return -1;
	}

	// Try to create a socket and connect on the returned addrs
	for(p = addrs; p != NULL; p = p->ai_next) {	
		// Create socket fd
		sockfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
		if (sockfd < 0) {
			log_perror("socket");
			continue;
		}

		// Connect to the server
		if (connect(sockfd, p->ai_addr, p->ai_addrlen) < 0) {
			log_perror("connect");
			close(sockfd);
			sockfd = -1;
			continue;
		}
	}

	freeaddrinfo(addrs);
	
	return sockfd;
}

// Read the whole "packet" from a TCP socket.
// Returns the number of bytes read (or -1 on failure).
// Doesn't stop reading until either the buffer is full, an EOF is encountered,
// or an error occurs.
ssize_t read_whole(int fd, void *buffer, size_t length)
{
	assert(buffer != NULL);
	assert(length != 0);

	size_t total = 0;
	while (total < length) {
		ssize_t bytes = read(fd, buffer + total, length - total);
		if (bytes < 0) {
			log_perror("read");
			return -1;
		}
		if (bytes == 0) {// EOF (the socket was closed on the other end)
			break;
		}
		total += bytes;
	}

	return (ssize_t)total;
}


// Helper functions for converting messages to/from host/network byte order
// and validating them.

static void hton_msg_hdr(msg_hdr *hdr)
{
	assert(hdr != NULL);
	hdr->magic = HDR_MAGIC;
	assert(hdr->type < MSG_TYPE_MAX);
	assert(hdr->length <= MAX_MSG_LEN);
	hdr->length = htons(hdr->length);
}

static bool ntoh_msg_hdr(msg_hdr *hdr)
{
	assert(hdr != NULL);
	hdr->length = ntohs(hdr->length);
	return (hdr->magic == HDR_MAGIC) && (hdr->type < MSG_TYPE_MAX)
		&& (hdr->length <= MAX_MSG_LEN);
}

static void hton_config_request(config_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_CONFIG_REQ);
	assert(msg->hdr.length == sizeof(config_request));
}

static bool ntoh_config_request(config_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_CONFIG_REQ);
	return msg->hdr.length == sizeof(config_request);
}

static void hton_config_response(config_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_CONFIG_RESP);
	assert(msg->hdr.length > sizeof(config_response));
	msg->num_entries = htons(msg->num_entries);
	assert(msg->entry_buffer[msg->hdr.length - sizeof(config_response) - 1] == '\0');
}

static bool ntoh_config_response(config_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_CONFIG_RESP);
	if (msg->hdr.length <= sizeof(config_response)) {
		return false;
	}
	msg->num_entries = ntohs(msg->num_entries);
	// Null-terminate the string
	msg->entry_buffer[msg->hdr.length - sizeof(config_response) - 1] = '\0';
	return true;
}

static void hton_operation_request(operation_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_OPERATION_REQ);
	assert(msg->hdr.length >= sizeof(operation_request));
	assert(msg->type < OP_TYPE_MAX);
	if ((msg->type == OP_NOOP) || (msg->type == OP_GET) ||
	    (msg->type == OP_VERIFY)) {
		assert(msg->hdr.length == sizeof(operation_request));
	} else {
		assert(msg->hdr.length > sizeof(operation_request));
	}
}

static bool ntoh_operation_request(operation_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_OPERATION_REQ);
	if ((msg->hdr.length < sizeof(operation_request)) || (msg->type >= OP_TYPE_MAX)) {
		return false;
	}
	if ((msg->type == OP_NOOP) || (msg->type == OP_GET) ||
	    (msg->type == OP_VERIFY)) {
		return msg->hdr.length == sizeof(operation_request);
	} else {
		return msg->hdr.length > sizeof(operation_request);
	}	
}

static void hton_operation_response(operation_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_OPERATION_RESP);
	assert(msg->hdr.length >= sizeof(operation_response));
	assert(msg->status < OP_STATUS_MAX);
}

static bool ntoh_operation_response(operation_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_OPERATION_RESP);
	return (msg->hdr.length >= sizeof(operation_response)) && (msg->status < OP_STATUS_MAX);
}

static void hton_coord_ctrl_request(coord_ctrl_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_COORD_CTRL_REQ);
	assert(msg->hdr.length >= sizeof(coord_ctrl_request));
	assert(msg->type < COORD_CTRLREQ_TYPE_MAX);
	msg->server_id = htons(msg->server_id);
	if (msg->type == STARTED) {
		// expect three port numbers in startup message; hton them
		int portsz = 3 * sizeof(uint16_t);
		assert(msg->hdr.length == sizeof(coord_ctrl_request) + portsz);
		for (int i = 0; i < 3; i++) {
			msg->ports[i] = htons(msg->ports[i]);
		}
	} else {
		assert(msg->hdr.length == sizeof(coord_ctrl_request));
	}
}

static bool ntoh_coord_ctrl_request(coord_ctrl_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_COORD_CTRL_REQ);
	msg->server_id = ntohs(msg->server_id);
	if (msg->type == STARTED) {
		// expect three port numbers in startup message; hton them
		int portsz = 3 * sizeof(uint16_t);
		if (msg->hdr.length != sizeof(coord_ctrl_request) + portsz) {
			return false;
		}
		for (int i = 0; i < 3; i++) {
			msg->ports[i] = ntohs(msg->ports[i]);
		}
		return true;
	} else {
		return (msg->hdr.length == sizeof(coord_ctrl_request)) &&
			(msg->type < COORD_CTRLREQ_TYPE_MAX);
	}
}

static void hton_server_ctrl_request(server_ctrl_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_SERVER_CTRL_REQ);
	assert(msg->hdr.length >= sizeof(server_ctrl_request));
	assert(msg->type < SERVER_CTRLREQ_TYPE_MAX);
	if ((msg->type == SET_SECONDARY) || (msg->type == UPDATE_PRIMARY) || (msg->type == UPDATE_SECONDARY)) {
		assert(msg->hdr.length > sizeof(server_ctrl_request));
		msg->port = htons(msg->port);
		assert(msg->host_name[msg->hdr.length - sizeof(server_ctrl_request) - 1] == '\0');
		assert(msg->hdr.length == sizeof(server_ctrl_request) + strlen(msg->host_name) + 1);
	} else {
		assert(msg->hdr.length == sizeof(server_ctrl_request));
	}
}

static bool ntoh_server_ctrl_request(server_ctrl_request *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_SERVER_CTRL_REQ);
	if ((msg->hdr.length < sizeof(server_ctrl_request)) ||
	    (msg->type >= SERVER_CTRLREQ_TYPE_MAX)) {
		return false;
	}
	if ((msg->type == SET_SECONDARY) || (msg->type == UPDATE_PRIMARY) ||
	    (msg->type == UPDATE_SECONDARY)) {
		msg->port = ntohs(msg->port);
		if (msg->hdr.length <= sizeof(server_ctrl_request)) {
			return false;
		}
		// Null-terminate the string
		msg->host_name[msg->hdr.length - sizeof(server_ctrl_request) - 1] = '\0';
		return msg->hdr.length == sizeof(server_ctrl_request) + strlen(msg->host_name) + 1;
	} else {
		return msg->hdr.length == sizeof(server_ctrl_request);
	}
	return true;
}

static void hton_server_ctrl_response(server_ctrl_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_SERVER_CTRL_RESP);
	assert(msg->hdr.length == sizeof(server_ctrl_response));
	assert(msg->status < SERVER_CTRLREQ_STATUS_MAX);
}

static bool ntoh_server_ctrl_response(server_ctrl_response *msg)
{
	assert(msg != NULL);
	assert(msg->hdr.type == MSG_SERVER_CTRL_RESP);
	return (msg->hdr.length == sizeof(server_ctrl_response)) &&
	       (msg->status < SERVER_CTRLREQ_STATUS_MAX);
}


// Write message contents to log, based on its type
// The 'received' argument must be true if this message was received current program
void log_msg(const void *msg, bool received)
{
	assert(msg != NULL);
	char subtype[MAX_MSG_LEN] = "";
	char contents[MAX_MSG_LEN] = "";

	const msg_hdr *hdr = msg;
	switch (hdr->type) {
	case MSG_NONE:
		break;

	case MSG_CONFIG_REQ:
		break;
		
	case MSG_CONFIG_RESP: {
		const config_response *m = msg;
		snprintf(contents, sizeof(contents), ", nentries = %d: %s",
			 m->num_entries, m->entry_buffer);
		break;
	}

	case MSG_OPERATION_REQ: {
		const operation_request *m = msg;
		snprintf(subtype, sizeof(subtype), ", subtype = %s",
			 op_type_str[m->type]);
		if (m->type == OP_PUT) {
			// Assume that value is a null-terminated string
			snprintf(contents, sizeof(contents),
				 ", key = %s, value = %s",
				 key_to_str(m->key), m->value);
		} else {
			snprintf(contents, sizeof(contents), ", key = %s",
				 key_to_str(m->key));
		}
		break;
	}

	case MSG_OPERATION_RESP: {
		const operation_response *m = msg;
		if (hdr->length > sizeof(operation_response)) {
			// Assume that value is a null-terminated string
			snprintf(contents, sizeof(contents),
				 ", status = %s, value = %s",
				 op_status_str[m->status], m->value);
		} else {
			snprintf(contents, sizeof(contents), ", status = %s",
				 op_status_str[m->status]);
		}
		break;
	}

	case MSG_COORD_CTRL_REQ: {
		const coord_ctrl_request *m = msg;
		snprintf(subtype, sizeof(subtype), ", subtype = %s",
			 coord_ctrlreq_type_str[m->type]);
		snprintf(contents, sizeof(contents), ", sid = %d", m->server_id);
		break;
	}
		
	case MSG_SERVER_CTRL_REQ: {
		const server_ctrl_request *m = msg;
		snprintf(subtype, sizeof(subtype), ", subtype = %s",
			 server_ctrlreq_type_str[m->type]);
		if ((m->type == SET_SECONDARY) ||
		    (m->type == UPDATE_PRIMARY) ||
		    (m->type == UPDATE_SECONDARY)) {
			snprintf(contents, sizeof(contents),
				 ", host = %s, port = %hu",
				 m->host_name, m->port);
		}
		break;
	}
		
	case MSG_SERVER_CTRL_RESP: {
		const server_ctrl_response *m = msg;
		snprintf(contents, sizeof(contents), ", status = %s",
			 server_ctrlreq_status_str[m->status]);
		break;
	}
		
	default:// impossible
		assert(false);
		break;
	}
	
	log_write("%s message: type = %s, length = %d%s%s\n",
		  received ? "Received" : "Sending",
	          msg_type_str[hdr->type], hdr->length, subtype, contents);
}

// Write a message to a TCP socket.
// Returns true on success. Takes care of byte order and validates the message.
// Note that this function modifies message contents, so it cannot be re-sent
// again using this function.
bool send_msg(int fd, void *buffer, size_t length)
{
	assert(buffer != NULL);
	assert(length >= sizeof(msg_hdr));

	msg_hdr *hdr = buffer;
	hdr->length = length;

	log_msg(buffer, false);

	// "hton" and validate the message body, based on its type
	switch (hdr->type) {
	case MSG_NONE:
		break;
	case MSG_CONFIG_REQ:
		hton_config_request(buffer);
		break;
	case MSG_CONFIG_RESP:
		hton_config_response(buffer);
		break;
	case MSG_OPERATION_REQ:
		hton_operation_request(buffer);
		break;
	case MSG_OPERATION_RESP:
		hton_operation_response(buffer);
		break;
	case MSG_COORD_CTRL_REQ:
		hton_coord_ctrl_request(buffer);
		break;
	case MSG_SERVER_CTRL_REQ:
		hton_server_ctrl_request (buffer);
		break;
	case MSG_SERVER_CTRL_RESP:
		hton_server_ctrl_response(buffer);
		break;
		
	default:// impossible
		assert(false);
		return false;
	}

	// "hton" and validate the message header
	hton_msg_hdr(hdr);

	// Write the message to the socket
	ssize_t bytes = write(fd, buffer, length);
	if (bytes < 0) {
		log_perror("write");
		return false;
	}
	assert((size_t)bytes == length);
	return true;
}

// Read a single message from TCP socket.
// Returns true on success. Takes care of byte order and validates the message.
// (expected_type == -1 means any type)
bool recv_msg(int fd, void *buffer, size_t length, msg_type expected_type)
{
	assert(buffer != NULL);
	assert(length >= sizeof(msg_hdr));

	// Read and validate the message header
	if (read_whole(fd, buffer, sizeof(msg_hdr)) <= 0) {
		return false;
	}
	msg_hdr *hdr = buffer;
	if (!ntoh_msg_hdr(hdr)) {
		log_error("Invalid message header\n");
		return false;
	}

	// Check expected message type
	if ((expected_type != (msg_type)-1) && (hdr->type != expected_type)) {
		log_error("Wrong message type: %s (expected %s)\n",
			  msg_type_str[hdr->type], msg_type_str[expected_type]);
		return false;
	}
	
	// Check that the buffer is large enough
	if (length < hdr->length) {
		log_error("Buffer too small: need %d bytes, have %zu bytes\n",
			  hdr->length, length);
		return false;
	}

	// If we are expecting more data, read message body
	if (hdr->length > sizeof(msg_hdr) &&
	    (read_whole(fd, buffer+sizeof(msg_hdr),
			hdr->length-sizeof(msg_hdr)) < 0)) {
		return false;
	}

	bool result = false;
	// "ntoh" and validate the message body, based on its type
	switch (hdr->type) {
	case MSG_NONE:
		result = true;
		break;
	case MSG_CONFIG_REQ:
		result = ntoh_config_request (buffer);
		break;
	case MSG_CONFIG_RESP:
		result = ntoh_config_response(buffer);
		break;
	case MSG_OPERATION_REQ:
		result = ntoh_operation_request (buffer);
		break;
	case MSG_OPERATION_RESP:
		result = ntoh_operation_response(buffer);
		break;
	case MSG_COORD_CTRL_REQ:
		result = ntoh_coord_ctrl_request(buffer);
		break;
	case MSG_SERVER_CTRL_REQ:
		result = ntoh_server_ctrl_request (buffer);
		break;
	case MSG_SERVER_CTRL_RESP:
		result = ntoh_server_ctrl_response(buffer);
		break;

	default:// impossible
		assert(false);
		return false;
	}

	if (!result) {
		log_error("Invalid %s message\n", msg_type_str[hdr->type]);
		return false;
	}

	log_msg(buffer, true);
	return true;
}


// If fd is valid (!= -1), closes it, sets it to -1, and returns true;
// otherwise, returns false.
bool close_safe(int *fd)
{
	assert(fd != NULL);

	if (*fd == -1) {
		return false;
	}

	close(*fd);
	*fd = -1;
	return true;
}

// Get the host name that server is running on
int get_local_host_name(char *str, size_t length)
{
	struct addrinfo hints, *addrs;
	char my_host_name[HOST_NAME_MAX] = "";
	int err;

	assert(str != NULL);
	assert(length != 0);

	if (gethostname(my_host_name, HOST_NAME_MAX) < 0) {
		log_perror("gethostname");
		return -1;
	}

	// Resolve the host name
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = AF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_flags = AI_CANONNAME;
	if ((err = getaddrinfo(my_host_name, NULL, &hints, &addrs)) != 0) {
		log_gai_error("getaddrinfo", err);
		return -1;
	}

	strncpy(str, addrs->ai_canonname, length);
	return 0;
}

// Start a TCP server on a given port; returns listening socket fd
// If port == 0, bind to an arbitrary port assigned by the OS;
//               new_port must != NULL in this case
// If port != 0 and bind fails, then an arbitray port is chosen
//              (and returned via *new_port) if new_port != NULL
int create_server(uint16_t port, int max_sessions, uint16_t *new_port)
{
	char host_name[HOST_NAME_MAX];
	struct addrinfo hints, *addrs, *p;
	int sockfd = -1;
	char port_str[10];
	int err;
	bool need_to_get_port = ((port == 0) && (new_port != NULL));
	
	// Obtain address information using the host name and port
	// (See get_local_host_name() in util.c to get the host name.)

	if (get_local_host_name(host_name, HOST_NAME_MAX) < 0) {
		return -1;
	}
	
	memset(&hints, 0 , sizeof(hints));
	hints.ai_family = AF_UNSPEC;     // either IPv4 or IPv6
	hints.ai_socktype = SOCK_STREAM; // TCP stream sockets
	hints.ai_protocol = IPPROTO_TCP;
	snprintf(port_str, 10, "%hu", port);

	if ((err = getaddrinfo(host_name, port_str, &hints, &addrs)) != 0) {
		fprintf(stderr,"getaddrinfo error: %s\n", gai_strerror(err));
		return -1;
	}

	// Create a socket, set the SO_REUSEADDR socket option and bind it..
	// Remember that getaddrinfo returns a list of addresses, and you
	// need to try them in order until you find one that works.
	// Remember also to check if bind() needs to choose the port, and if
	// so, set "new_port" so that it is returned to the caller.

	for(p = addrs; p != NULL; p = p->ai_next) {	
		// Create socket fd
		sockfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
		if (sockfd < 0) {
			perror("socket");
			continue;
		}

		// Set the SO_REUSEADDR socket option
		int opt_val = 1;
		if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, (void*)&opt_val, sizeof(opt_val)) < 0) {
			perror("setsockopt");
			close(sockfd);
			continue;
		}

		// Try to bind to the given port
		if ((err = bind(sockfd, p->ai_addr, p->ai_addrlen)) < 0 ) {
			// Error
			perror("bind");
			// If bind failed because the address (port) was in use
			// then try letting bind pick the port, but only if
			//   (a) we didn't already try that (port != 0) and
			//   (b) caller gave us a place to return the port #.
			if ((err == EADDRINUSE) &&
			    (port != 0) && (new_port != NULL)) {
				// Need to dig into addr and set port to 0. That
				// depends on whether family is IPv4 or IPv6.
				if (p->ai_family == AF_INET) {
					struct sockaddr_in *sa;
					sa = (struct sockaddr_in *)p->ai_addr;
					sa->sin_port = 0;
				} else {
					struct sockaddr_in6 *sa;
					sa = (struct sockaddr_in6 *)p->ai_addr;
					sa->sin6_port = 0;
				}
				err = bind(sockfd, p->ai_addr, p->ai_addrlen);
				if (err < 0) {
					perror("bind second try");
					close(sockfd);
					continue;
				}
				// Success! But need to get port number assigned
				need_to_get_port = true;
				break;
			} else {
				close(sockfd);
				continue;
			}
		} else {
			// bind() successful!
			break;
		}
	}

	if (p == NULL) { // No success.
		fprintf(stderr,"Could not bind to any address.\n");
		return -1;
	}

	// If p is not NULL, then it points to the addr used for socket & bind.
	
	// If bind() assigned a port, find out what it was
	if (need_to_get_port) {
		assert(new_port != NULL);

		if (getsockname(sockfd, p->ai_addr, &p->ai_addrlen) < 0) {
			perror("getsockname");
			close(sockfd);
			return -1;
		}
		if (p->ai_family == AF_INET) {
			*new_port = port = ntohs(((struct sockaddr_in *)p->ai_addr)->sin_port);
		} else { // AF_INET6
			*new_port = port = ntohs(((struct sockaddr_in6 *)p->ai_addr)->sin6_port);
		}
	}

	// Start listening for incoming connections
	if ((err = listen(sockfd, max_sessions)) < 0) {
		perror("listen");
		close(sockfd);
		return -1;
	}

	freeaddrinfo(addrs);

	log_write("Listening on TCP port %hu\n", port);
	return sockfd;
}

// Accept an incoming TCP connection; returns index in the fd table
int accept_connection(int fd, int *fd_table, int fd_table_size)
{
	assert(fd_table != NULL);
	assert(fd_table_size > 0);

	struct sockaddr_in addr;
	socklen_t addr_len = sizeof(struct sockaddr_in);

	int connect_fd = accept(fd, (struct sockaddr*)&addr, &addr_len);
	if (connect_fd < 0) {
		log_perror("accept");
		return -1;
	}

	// We accepted a new connection
	char info_str[HOST_NAME_MAX + 40] = "";
	char timebuf[TIME_STR_SIZE];
	get_peer_info(connect_fd, info_str, sizeof(info_str));
	log_write("%s New connection from %s\n", current_time_str(timebuf, TIME_STR_SIZE), info_str);

	// Find a place in fd_table[] to store the accepted fd
	int i;
	for (i = 0; i < fd_table_size; i++) {
		if (fd_table[i] == -1) {
			fd_table[i] = connect_fd;
			return i;
		}
	}

	assert(i == fd_table_size);
	log_write("%s Too many connections, rejecting an incoming connection\n",
		  current_time_str(timebuf, TIME_STR_SIZE));
	close(connect_fd);
	return -1;
}

// Returns a string with a timestamp, the hostname and the port number of the
// peer connected to the socket fd.
// The port number is converted from network byte order to host byte order
// before printing it into the string
int get_peer_info(int fd, char *str, size_t length)
{
	int err;
	char my_host_name[HOST_NAME_MAX] = "";

	assert(str != NULL);
	assert(length != 0);

	struct sockaddr_in addr;
	socklen_t addr_len = sizeof(addr);
	if (getpeername(fd, (struct sockaddr*)&addr, &addr_len) < 0) {
		log_perror("getpeername");
		return -1;
	}

	err = getnameinfo((struct sockaddr *)&addr, addr_len,
			  my_host_name, HOST_NAME_MAX, NULL, 0, NI_NAMEREQD);
	if (err != 0) {
		log_gai_error("getnameinfo", err);
		return -1;
	}
	
	snprintf(str, length, "%s:%hu", my_host_name, ntohs(addr.sin_port));
	return 0;
}


typedef struct _waitpid_args {
	pid_t pid;
	int *status;
} waitpid_args;

static void *waitpid_timeout_thread_f(void *arg)
{
	assert(arg != NULL);

	// Make the thread cancellable at any point in time
	int rc = pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL);
	if (rc != 0) {
		errno = rc;
		log_perror("pthread_setcanceltype");
		return (void*)-1;
	}

	waitpid_args *args = arg;
	return (void*)(size_t)waitpid(args->pid, args->status, 0);
}

// Wait for a child process to terminate, with a timeout (in seconds)
pid_t waitpid_timeout(pid_t pid, int *status, int timeout)
{
	if (timeout <= 0) {
		return waitpid(pid, status, WNOHANG);
	}

	waitpid_args args = {0};
	args.pid = pid;
	args.status = status;

	pthread_t thread;
	int rc = pthread_create(&thread, NULL, waitpid_timeout_thread_f, &args);
	if (rc != 0) {
		errno = rc;
		log_perror("pthread_create");
		return -1;
	}

	struct timespec ts;
	if (clock_gettime(CLOCK_REALTIME_COARSE, &ts) < 0) {
		log_perror("clock_gettime");
		return -1;
	}
	ts.tv_sec += timeout;

	void *result;
	rc = pthread_timedjoin_np(thread, &result, &ts);
	if (rc == 0) {
		return (pid_t)(size_t)result;
	} else if (rc == ETIMEDOUT) {
		rc = pthread_cancel(thread);
		if (rc != 0) {
			errno = rc;
			log_perror("pthread_cancel");
			return -1;
		}
		pthread_join(thread, NULL);
		return 0;
	} else {
		errno = rc;
		log_perror("pthread_timedjoin_np");
		return -1;
	}
}

// Wait for a child process to terminate, killing it if the timeout
// (in seconds) expires.
// Returns false if had to kill the process
bool wait_or_kill(pid_t pid, int timeout)
{
	if (waitpid_timeout(pid, NULL, timeout) > 0) {
		return true;
	}

	log_write("Killing child process %d\n", pid);
	kill(pid, SIGKILL);
	waitpid(pid, NULL, 0);
	return false;
}

// If pid is valid (> 0), waits for it to terminate with a timeout (in seconds)
// and kills it if the timeout expires, sets it to 0, and returns true;
// otherwise, returns false.
bool kill_safe(pid_t *pid, int timeout)
{
	assert(pid != NULL);

	if (*pid <= 0) {
		return false;
	}

	wait_or_kill(*pid, timeout);
	*pid = 0;
	return true;
}


// Get primary key server id for a key
int key_server_id(const char key[KEY_SIZE], int num_servers)
{
	assert(key != NULL);
	assert(num_servers > 0);

	int byte = (unsigned char)(key[KEY_SIZE - 1]);
	return byte % num_servers;
}

// Get secondary server id for given primary server id
int secondary_server_id(int server_id, int num_servers)
{
	assert(num_servers >= 3);// to avoid cross-replication
	assert((server_id >= 0) && (server_id < num_servers));

	return (server_id + 1) % num_servers;
}

// Get primary server id for given secondary server id
int primary_server_id(int server_id, int num_servers)
{
	assert(num_servers >= 3);// to avoid cross-replication
	assert((server_id >= 0) && (server_id < num_servers));

	return (server_id + num_servers - 1) % num_servers;
}
