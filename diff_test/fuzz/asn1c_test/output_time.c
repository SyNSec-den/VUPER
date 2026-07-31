#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dirent.h>


#include "DL-DCCH-Message.h"
#include "uper_decoder.h"
#include "uper_encoder.h"

uint8_t* read_bytecode_file(FILE *file, size_t *size) {

    // Get file size
    fseek(file, 0, SEEK_END);
    *size = ftell(file);
    rewind(file);

    // Allocate memory for bytecode
    uint8_t *buffer = malloc(*size);
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

    //fclose(file);
    return buffer;  // Caller must free() this memory
}


void measure_total_parsing_time(char *dirpath) {
  DIR* FD = opendir(dirpath);
  struct dirent* in_file;
  //FILE    *entry_file;

  int total_time_clock = 0;
  int num_of_file = 0;
  int error_files = 0;
  int correct_files = 0;

  while ((in_file = readdir(FD))) {
    /* On linux/Unix we don't want current and parent directories
     * On windows machine too, thanks Greg Hewgill
     */
    if (!strcmp (in_file->d_name, "."))
      continue;
    if (!strcmp (in_file->d_name, ".."))    
      continue;

    // skip directories
    if (in_file->d_type == DT_DIR)
      continue;

    
    char filepath[1024];
    snprintf(filepath, sizeof(filepath), "%s/%s", dirpath, in_file->d_name);

    FILE *entry_file = fopen(filepath, "rb");

     if (entry_file == NULL)  {
      //fprintf(stderr, "Error : Failed to open entry file - %s\n", strerror(errno));

      return;
    }

    size_t size;
    /* Doing some struf with entry_file : */
    /* For example use fgets */
    uint8_t *buffer = read_bytecode_file(entry_file, &size);  // Read file first
    DL_DCCH_Message_t *t = NULL;

    clock_t start = clock();
    asn_dec_rval_t dec_r = uper_decode_complete(NULL, &asn_DEF_DL_DCCH_Message, (void **) &t, buffer, size);
    ASN_STRUCT_FREE(asn_DEF_DL_DCCH_Message, t);
    clock_t end = clock();
    total_time_clock += (end - start) ;

    free(buffer);

    /* When you finish with the file, close it */
    fclose(entry_file);

    if ((dec_r.code != RC_OK) && (dec_r.consumed == 0)) {

      error_files += 1;
      
    } else {
  
      correct_files += 1;
      
    }

    num_of_file += 1;
  }

  closedir(FD);
  
  float total_time = (double)total_time_clock / CLOCKS_PER_SEC;
  printf("Total parsing time for %d files: %f seconds\n", num_of_file, total_time);
  printf("correct files: %d, error_files: %d", correct_files, error_files);
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <directory>\n", argv[0]);
        return 1;
    }
  
    measure_total_parsing_time(argv[1]);
    return 0;
}
