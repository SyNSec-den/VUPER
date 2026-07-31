/*
  New Custom Mutator for AFL++
*/

// You need to use -I/path/to/AFLplusplus/include -I.
#include "afl-fuzz.h"

#include "asnfuzz_rrc_uper.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "radamsa.h"

#define INPUT_SIZE 1024    // Size for the random input buffer
#define OUTPUT_SIZE 2048   // Size for the output buffer

typedef struct my_mutator {

  afl_state_t *afl;

  // any additional data here!

  unsigned char *rand_input;
  unsigned char *mutate_out;

  int seed;
  
} my_mutator_t;

/**
 * Initialize this custom mutator
 *
 * @param[in] afl a pointer to the internal state object. Can be ignored for
 * now.
 * @param[in] seed A seed for this mutator - the same seed should always mutate
 * in the same way.
 * @return Pointer to the data object this custom mutator instance should use.
 *         There may be multiple instances of this mutator in one afl-fuzz run!
 *         Return NULL on error.
 */
my_mutator_t *afl_custom_init(afl_state_t *afl, unsigned int seed) {

  srand(seed);  // needed also by surgical_havoc_mutate()

  my_mutator_t *data = calloc(1, sizeof(my_mutator_t));
  if (!data) {

    perror("afl_custom_init alloc");
    return NULL;

  }

  if ((data->rand_input = (unsigned char *)malloc(INPUT_SIZE)) == NULL) {

    perror("afl_custom_init malloc");
    return NULL;
  }

  if ((data->mutate_out = (unsigned char *)malloc(OUTPUT_SIZE)) == NULL) {

    perror("afl_custom_init malloc");
    return NULL;
  }

  data->afl = afl;
  data->seed = 0;

  radamsa_init();
  
  return data;

}

/**
 * Perform custom mutations on a given input
 *
 * (Optional for now. Required in the future)
 *
 * @param[in] data pointer returned in afl_custom_init for this fuzz case
 * @param[in] buf Pointer to input data to be mutated
 * @param[in] buf_size Size of input data
 * @param[out] out_buf the buffer we will work on. we can reuse *buf. NULL on
 * error.
 * @param[in] add_buf Buffer containing the additional test case
 * @param[in] add_buf_size Size of the additional test case
 * @param[in] max_size Maximum size of the mutated output. The mutation must not
 *     produce data larger than max_size.
 * @return Size of the mutated output.
 */
size_t afl_custom_fuzz(my_mutator_t *data, uint8_t *buf, size_t buf_size,
                       u8 **out_buf, uint8_t *add_buf,
                       size_t add_buf_size,  // add_buf can be NULL
                       size_t max_size) {

  // Make sure that the packet size does not exceed the maximum size expected by
  // the fuzzer
  // first we destructure the input, and if we found an error,
  // we provide a randomly generated new array.
  unsigned char input_de[INPUT_SIZE];
  long struct_len;
  
  long destruct_len = uper_rrc_destructure((char*)buf, buf_size, (char *)input_de, INPUT_SIZE);

  if (destruct_len < 0) {
    // case where it is impossible to decode, so we randomly give a new string

    for (int i = 0; i < INPUT_SIZE; i++) {
      input_de[i] = rand() % 256;  // Fill with random bytes
    }
    
    struct_len = uper_rrc_structure((char*)input_de, INPUT_SIZE, (char*) data->mutate_out, OUTPUT_SIZE);
    
  } else {

    // First mutate the input

    unsigned char inter_de[OUTPUT_SIZE];
    size_t inter_len = radamsa((uint8_t *) input_de, destruct_len, (uint8_t *) inter_de, OUTPUT_SIZE, data->seed++);
    
    struct_len = uper_rrc_structure((char*) inter_de, inter_len, (char *) data->mutate_out, OUTPUT_SIZE);
  }

  if (struct_len > 0) {
    size_t output_size;
    if ((size_t) struct_len > max_size) {
      output_size = max_size;
    } else {
      output_size = (size_t) struct_len;
    }

    *out_buf = data->mutate_out;
    return output_size;
      
  } else {
    *out_buf = buf;
    return buf_size;
  }

}


/**
 * Deinitialize everything
 *
 * @param data The data ptr from afl_custom_init
 */
void afl_custom_deinit(my_mutator_t *data) {

  free(data->rand_input);
  free(data);

}
