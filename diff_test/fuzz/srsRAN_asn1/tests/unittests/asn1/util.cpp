#include <stdint.h>
#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "util.h"



uint8_t* read_bytecode_file(const char *filename, size_t *size) {
  FILE *file = fopen(filename, "rb");  // Open file in binary mode
  if (!file) {
    perror("Failed to open file");
    return NULL;
  }

  // Get file size
  fseek(file, 0, SEEK_END);
  *size = ftell(file);
  rewind(file);

  // Allocate memory for bytecode
  uint8_t *buffer = (uint8_t *) malloc(*size);
  if (!buffer) {
    perror("Memory allocation failed");
    fclose(file);
    return NULL;
  }

  // Read file contents into buffer
  if (fread(buffer, 1, *size, file) != *size) {
    perror("Failed to read file");
    free(buffer);
    fclose(file);
    return NULL;
  }

  fclose(file);
  return buffer;  // Caller must free() this memory
}



void fork_exec_binary(const char *binary, char *input_str, size_t input_size, FILE *fp, int is_python) {
  int input_pipe[2];  // Pipe to send data to child (stdin of child)
  int output_pipe[2]; // Pipe to receive data from child (stdout of child)

  if (pipe(input_pipe) == -1 || pipe(output_pipe) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }

  pid_t pid = fork();
  if (pid == -1) {
    perror("fork");
    exit(EXIT_FAILURE);
  }

  if (pid == 0) { // Child process
    close(input_pipe[1]);  // Close write end of input pipe
    close(output_pipe[0]); // Close read end of output pipe

    // Redirect stdin to read from input pipe
    dup2(input_pipe[0], STDIN_FILENO);
    close(input_pipe[0]);

    // Redirect stdout to write to output pipe
    dup2(output_pipe[1], STDOUT_FILENO);
    close(output_pipe[1]);

    // Execute the binary
    if (is_python == 1) {
      execlp("python3", "python3", binary, (char *)NULL);
    } else {
      execlp(binary, binary, (char *)NULL);
    }
    
    perror("execlp"); // If execlp fails
    exit(EXIT_FAILURE);
  } else { // Parent process
    close(input_pipe[0]);  // Close read end of input pipe
    close(output_pipe[1]); // Close write end of output pipe

    // Write input string to child process
    ssize_t writecount = write(input_pipe[1], input_str, input_size);
    if (writecount == -1) {
      return;
    }
    
    close(input_pipe[1]);  // Close write end after sending data

    // Read output from child process, and write it to stream
    char buffer_output[1024];
    ssize_t count;
    while ((count = read(output_pipe[0], buffer_output, sizeof(buffer_output))) > 0) {
      fwrite(buffer_output, 1, count, fp);
    }
    
    close(output_pipe[0]); // Close read end

    // Wait for child to finish
    wait(NULL);
  }
}

int remove_spaces(char *str) {
    int i = 0, j = 0;
    while (str[i]) {
        if (str[i] != ' ' && str[i] != '\n') {
            str[j++] = str[i];
        }
        i++;
    }

    str[j] = '\0'; // Null-terminate the modified string
    return j;
}
