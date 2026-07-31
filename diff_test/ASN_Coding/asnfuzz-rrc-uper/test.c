#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include "asnfuzz_rrc_uper.h"  // Include your .h file

#define INPUT_SIZE 1024    // Size for the random input buffer
#define OUTPUT_SIZE 2048   // Size for the output buffer

// Function to print a buffer in hexadecimal format
void print_hex(const char* label, const unsigned char* buf, long len) {
    printf("%s: ", label);
    for (long i = 0; i < len; i++) {
        printf("%02X ", buf[i]);
    }
    printf("\n");
}

static inline unsigned long long rdtsc() {
    unsigned int lo, hi;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((unsigned long long)hi << 32) | lo;
}


int main() {
    // Seed the random number generator

    srand((unsigned int)rdtsc()); // Seed with CPU timestamp counter
    //srand((unsigned int)time(NULL));

    START:
    // Step 1: Generate random input data for `uper_rrc_structure`
    unsigned char input[INPUT_SIZE];
    for (int i = 0; i < INPUT_SIZE; i++) {
        input[i] = rand() % 256;  // Fill with random bytes
    }


    // input[0] = 0x00;
    // input[1] = 0x07;
    // input[2] = 0x00;
    // input[3] = 0x00;
    // input[4] = 0x00;
    // input[5] = 0x01;
    // input[6] = 0x01;
    // input[7] = 0x02;
    // input[8] = 0x38;
    // input[9] = 0x38;
    // input[10] = 0x01;
    // INPUT_SIZE = 4;
    // Step 2: Allocate buffers for `uper_rrc_structure` output
    unsigned char structured_output[OUTPUT_SIZE];

    // Step 3: Call `uper_rrc_structure` and print buffers
    long struct_len = uper_rrc_structure((char*)input, INPUT_SIZE, (char*)structured_output, OUTPUT_SIZE);
    
    if (struct_len < 0) {
        printf("uper_rrc_structure failed with error code: %ld\n", struct_len);
        return 1;
    }

    if (struct_len == 1) {
        // This case is too simple, does not make any sense
        goto START;        
    }

    // Print input and output buffers
    //print_hex("uper_rrc_structure - buf_in", input, INPUT_SIZE);
  //  print_hex("uper_rrc_structure - buf_out", structured_output, struct_len);

    // Here I just put the structured_output into stdout

    /*FILE *fp = fopen("../../message/test.bin", "w");
    if (fp == NULL) {
        printf("Error opening the file");
	} */

    fwrite(structured_output, sizeof(u_char), struct_len, stdout);
    print_hex("uper_rrc_destructure - buf_in", structured_output, struct_len);
    /*
    // Step 4: Allocate buffers for `uper_rrc_destructure` output
    unsigned char unstructured_output[OUTPUT_SIZE];

    // Step 5: Call `uper_rrc_destructure` using the result from `uper_rrc_structure`
    long unstruct_len = uper_rrc_destructure((char*)structured_output, struct_len, (char*)unstructured_output, OUTPUT_SIZE);

    if (unstruct_len < 0) {
        printf("uper_rrc_destructure failed with error code: %ld\n", unstruct_len);
        return 1;
    }
*/
    // Print input and output buffers for `uper_rrc_destructure`
    
    //print_hex("uper_rrc_destructure - buf_out", unstructured_output, unstruct_len);

    return 0;
}
