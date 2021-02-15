// Copyright (C) 2016, 2017 Alexey Khrabrov, Bogdan Simion
//               2020 Angela Demke Brown
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


// Definition of the communication protocol

#ifndef _DEFS_H_
#define _DEFS_H_

#include <stdint.h>
#include <limits.h>

#ifndef HOST_NAME_MAX
#define HOST_NAME_MAX _POSIX_HOST_NAME_MAX
#endif

// Message types
typedef enum {
	MSG_NONE = 0,

	// Obtaining key-value service configuration
	MSG_CONFIG_REQ,
	MSG_CONFIG_RESP,

	// GET/PUT operations
	MSG_OPERATION_REQ,
	MSG_OPERATION_RESP,

	// Control requests (for failure detection and recovery purposes)
	// handled by the coordinator
	// NOTE: coordinator control requests do not require a response
	MSG_COORD_CTRL_REQ,

	// Control requests (for failure detection and recovery purposes)
	// handled by a key-value server
	MSG_SERVER_CTRL_REQ,
	MSG_SERVER_CTRL_RESP,

	MSG_TYPE_MAX,
// "packed" enum means that it has the least possible
// (hence platform-independent) size, 1 byte in this case
} __attribute__((packed)) msg_type;


// For logging purposes
__attribute__((unused))// to suppress possible "unused variable" warnings
static const char *msg_type_str[MSG_TYPE_MAX] = {
	"NONE",

	"CONFIG request",
	"CONFIG response",

	"OPERATION request",
	"OPERATION response",

	"COORD CTRL request",

	"SERVER CTRL request",
	"SERVER CTRL response"
};


// A "magic number" in the message header (for checking consistency)
#define HDR_MAGIC 0x7B

// Maximum length of a message
#define MAX_MSG_LEN 2048

// A common header for all messages
typedef struct _msg_hdr {
	char magic;
	msg_type type;
	uint16_t length;
// "packed" struct means there is no padding between the fields
// (so that the layout is platform-independent)
} __attribute__((packed)) msg_hdr;


// We use 128-bit (16-byte) MD5 hash as a key
#define KEY_SIZE 16

// Thread-safe version of time-to-string functions need buffer
// with space for at least 26 bytes
#define TIME_STR_SIZE 26

// "Configuration" request: get current key-value service configuration
// Really only need the header in this case.

#define MAX_KV_SERVERS 7
#define MAX_CLIENT_SESSIONS 1000 // maximum number of clients at any one time

typedef struct _config_entry {
	char host[HOST_NAME_MAX];
	uint16_t port;
} config_entry;

typedef struct _config_request {
	msg_hdr hdr;
} __attribute__((packed)) config_request;

typedef struct _config_response {
	msg_hdr hdr;
	uint16_t num_entries;
	char entry_buffer[];
} __attribute__((packed)) config_response;


// Key-value server request - GET or PUT operation

// Operation types
typedef enum {
	OP_NOOP, // Useful for testing communication between clients and servers
	         // Also used as an "end of sequence" message when sending a
	         // set of keys during UPDATE-PRIMARY 
	OP_GET,  // GET the value for the provided key
	OP_PUT,  // PUT (store) the provided value for the provided key
	OP_VERIFY, // DEBUGGING: GET key from primary or secondary replica
	OP_TYPE_MAX
} __attribute__((packed)) op_type;

__attribute__((unused))
static const char *op_type_str[OP_TYPE_MAX] = {
	"NOOP",
	"GET",
	"PUT",
	"VERIFY"
};

// Possible results of an operation
typedef enum {
	SUCCESS,

	SERVER_FAILURE,
	INVALID_REQUEST,
	KEY_NOT_FOUND,
	OUT_OF_SPACE,// not enough memory to store an item

	OP_STATUS_MAX
} __attribute__((packed)) op_status;

__attribute__((unused))
static const char *op_status_str[OP_STATUS_MAX] = {
	"Success",

	"Server failure",
	"Invalid request",
	"Key not found",
	"Out of space"
};

typedef struct _operation_request {
	msg_hdr hdr;
	char key[KEY_SIZE];
	op_type type;
	char value[];
} __attribute__((packed)) operation_request;

typedef struct _operation_response {
	msg_hdr hdr;
	op_status status;
	char value[];
} __attribute__((packed)) operation_response;


// Control requests handled by the coordinator

// Request types (as described in the assignment handout)
typedef enum {
	HEARTBEAT,// for failure detection
	STARTED,  // to report successful startup
	UPDATED_PRIMARY,
	UPDATE_PRIMARY_FAILED,

	UPDATED_SECONDARY,
	UPDATE_SECONDARY_FAILED,

	COORD_CTRLREQ_TYPE_MAX
} __attribute__((packed)) coord_ctrlreq_type;

__attribute__((unused))
static const char *coord_ctrlreq_type_str[COORD_CTRLREQ_TYPE_MAX] = {
	"HEARTBEAT",
	"STARTED",
	
	"UPDATED-PRIMARY",
	"UPDATE-PRIMARY failed",

	"UPDATED-SECONDARY",
	"UPDATE-SECONDARY failed"
};

typedef struct _coord_ctrl_request {
	msg_hdr hdr;
	coord_ctrlreq_type type;
	uint16_t server_id;
	uint16_t ports[]; // On kv server startup, send ports to coordinator
} __attribute__((packed)) coord_ctrl_request;


// Control requests handled by key-value servers

// Request types (as described in the assignment handout)
typedef enum {
	SET_SECONDARY,

	UPDATE_PRIMARY,
	UPDATE_SECONDARY,

	SWITCH_PRIMARY,
	
	SHUTDOWN,// for gracefully terminating the servers
	
	// For debugging and testing
	DUMP_PRIMARY,  // write primary keys from hash table to file
	DUMP_SECONDARY,// write secondary keys from hash table to file

	SERVER_CTRLREQ_TYPE_MAX
} __attribute__((packed)) server_ctrlreq_type;

__attribute__((unused))
static const char *server_ctrlreq_type_str[SERVER_CTRLREQ_TYPE_MAX] = {
	"SET-SECONDARY",

	"UPDATE-PRIMARY",
	"UPDATE-SECONDARY",

	"SWITCH-PRIMARY",

	"SHUTDOWN",
	
	"DUMP-PRIMARY",
	"DUMP-SECONDARY"
};

// Request status
typedef enum {
	CTRLREQ_SUCCESS,
	CTRLREQ_FAILURE,

	SERVER_CTRLREQ_STATUS_MAX
} __attribute__((packed)) server_ctrlreq_status;

__attribute__((unused))
static const char *server_ctrlreq_status_str[SERVER_CTRLREQ_STATUS_MAX] = {
	"Success",
	"Failure"
};

typedef struct _server_ctrl_request {
	msg_hdr hdr;
	server_ctrlreq_type type;
	// Server location (for {SET|UPDATE}_{PRIMARY|SECONDARY} requests)
	uint16_t port;
	char host_name[];
} __attribute__((packed)) server_ctrl_request;

typedef struct _server_ctrl_response {
	msg_hdr hdr;
	server_ctrlreq_status status;
} __attribute__((packed)) server_ctrl_response;


#endif// _DEFS_H_
