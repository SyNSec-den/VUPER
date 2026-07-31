#include "util.hh"
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

void fork_exec_binary(const char *binary, const char *input, size_t input_size,
                      FILE *fp, int is_python) {
  int input_pipe[2];
  int output_pipe[2];

  if (pipe(input_pipe) == -1 || pipe(output_pipe) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }

  pid_t pid = fork();
  if (pid == -1) {
    perror("fork");
    exit(EXIT_FAILURE);
  }

  if (pid == 0) {
    close(input_pipe[1]);
    close(output_pipe[0]);
    dup2(input_pipe[0], STDIN_FILENO);
    close(input_pipe[0]);
    dup2(output_pipe[1], STDOUT_FILENO);
    close(output_pipe[1]);
    if (is_python) {
      execlp("python3", "python3", binary, (char *)NULL);
    } else {
      execlp(binary, binary, (char *)NULL);
    }
    perror("execlp");
    exit(EXIT_FAILURE);
  } else {
    close(input_pipe[0]);
    close(output_pipe[1]);
    write(input_pipe[1], input, input_size);
    close(input_pipe[1]);
    char buf[1024];
    ssize_t n;
    while ((n = read(output_pipe[0], buf, sizeof(buf))) > 0)
      fwrite(buf, 1, n, fp);
    close(output_pipe[0]);
    wait(NULL);
  }
}

int remove_spaces(char *str) {
  int i = 0, j = 0;
  while (str[i]) {
    if (str[i] != ' ' && str[i] != '\n' && str[i] != '\t')
      str[j++] = str[i];
    i++;
  }
  str[j] = '\0';
  return j;
}

/* TITAN encodes ASN.1 hyphenated enum identifiers with underscores in JSON
   (e.g. "alt_000_01" vs OCaml's "alt-000-01"). ITS field names are all
   camelCase, so replacing every '_' with '-' safely normalises enum values. */
void normalize_titan_json(char *str) {
  for (int i = 0; str[i]; i++) {
    if (str[i] == '_')
      str[i] = '-';
  }
}
