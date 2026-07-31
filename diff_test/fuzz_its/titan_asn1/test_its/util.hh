#pragma once
#include <stdio.h>
#include <stddef.h>

void fork_exec_binary(const char *binary, const char *input, size_t input_size,
                      FILE *fp, int is_python);
int remove_spaces(char *str);
void normalize_titan_json(char *str);
