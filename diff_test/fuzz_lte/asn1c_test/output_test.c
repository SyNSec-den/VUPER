#include "DL-DCCH-Message.h"
//#include "VarMeasReport.h"
#include "uper_decoder.h"
#include "uper_encoder.h"
#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "util.h"

void print_hex(unsigned char *data, size_t len) {
  for (size_t i = 0; i < len; i++) {
    printf("%02X ", data[i]);  // Print each byte as a 2-digit hex number
  }
  printf("\n");
}


int main () {

  // uint8_t buffer[50];


  asn_enc_rval_t enc_r;
  asn_dec_rval_t dec_r;

    
  char buffer[4096] = {0};
  size_t size;

  size = fread(buffer, 1, sizeof(buffer), stdin);

  /* First print the buffer with 2x encoding */
  print_hex((unsigned char *) buffer, size);
  
  asn_enc_rval_t er;

  char *stream_buffer = NULL; 
  size_t stream_size = 0;

  /* This stream would be a json string, with first the ASN.1 message, 
     then the OCaml parser message, it should be something like 

     { "asn1c" : asn1_message, 
     "vp" : vp_message
     }
  */
  
  FILE *stream = open_memstream(&stream_buffer, &stream_size);

  fprintf(stream, "{ \"asn1c\" : ");
  
  DL_DCCH_Message_t *t = NULL;

  dec_r = uper_decode_complete(NULL, &asn_DEF_DL_DCCH_Message, (void **) &t, buffer, size);

  /* If there is an error, we write "Error" into the json, 
     otherwise, we write the decoded message. 
  */
  if ((dec_r.code != RC_OK) && (dec_r.consumed == 0)) {
    
    fprintf(stream, "\"Error\"");

    int jer_er = jer_fprint(stream, &asn_DEF_DL_DCCH_Message, t);
  } else {

    printf("dec code is RC_OK: %d; consumed is %zu\n", dec_r.code == RC_OK, dec_r.consumed);
    
    /* Flush jer output into the stream */
    int jer_er = jer_fprint(stream, &asn_DEF_DL_DCCH_Message, t);

    if (jer_er == -1) {
      printf("Error printing the jer message!\n");
      abort();
    }

    /* We should also encode the message again, to see how if it matches the 
       original message
     */
    char *encode_buffer[4096] = {0};
    enc_r = uper_encode_to_buffer(&asn_DEF_DL_DCCH_Message, NULL, t, encode_buffer, 4096);

    
    if (enc_r.encoded == -1) {
      printf("Error encoding the decoded message!\n");
    } else {
      printf("The message's encoding is : \n");
      print_hex((unsigned char *) encode_buffer, enc_r.encoded);
    }
    
  }

  // free the AST message
  ASN_STRUCT_FREE(asn_DEF_DL_DCCH_Message, t);

  // need to write the OCaml structure into the code
  fprintf(stream, ", \"vp\" : ");
  
  // need to call the OCaml code here
  fork_exec_binary("../ocaml_test/_build/default/test/test.exe", buffer, size, stream, 0);
  
  fprintf(stream, "}");
  fflush(stream);

  printf("%s", stream_buffer);


  fclose(stream);
  free(stream_buffer);
  
return 0; 
}
