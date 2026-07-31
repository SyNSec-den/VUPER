#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


uint8_t* read_bytecode_file(const char *filename, size_t *size);

void fork_exec_binary(char *binary, char *input_str, size_t input_size, FILE *fp, int is_python);

int remove_spaces(char *str);
