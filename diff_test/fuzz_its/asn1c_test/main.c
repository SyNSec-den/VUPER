#include "DENM.h"
#include "CAM.h"
#include "uper_decoder.h"
#include "uper_encoder.h"
#include <unistd.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "util.h"

int main () {

  // uint8_t buffer[50];

  while (__AFL_LOOP(10000)) {  // Run 10,000 iterations before restarting


    asn_enc_rval_t enc_r;
    asn_dec_rval_t dec_r;

    
    char buffer[4096];
    size_t buffer_size;

    buffer_size = fread(buffer, 1, sizeof(buffer), stdin);

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

    //fprintf(stream, "{ \"asn1c\" : ");
  
    CAM_t *t = NULL;

    dec_r = uper_decode_complete(NULL, &asn_DEF_CAM, (void **) &t, buffer, buffer_size);

    /* If there is an error, we write "Error" into the json, 
       otherwise, we write the decoded message. 
    */
    int c_error = 0;
    
    if ((dec_r.code != RC_OK) && (dec_r.consumed == 0)) {

      c_error = 1;
      fprintf(stream, "\"Error\"");
    } else {
  
      /* Flush jer output into the stream */
      int jer_er = jer_fprint(stream, &asn_DEF_CAM, t);
      if (jer_er == -1) {
	printf("Error printing the jer message");
	return 1;
      }
    }

    // free the AST message
    ASN_STRUCT_FREE(asn_DEF_CAM, t);

    // need to write the OCaml structure into the code
    // fprintf(stream, ", \"vp\" : ");


    // this stream is for OCaml
    char *comp_stream_buffer = NULL; 
    size_t comp_stream_size = 0;
  
    FILE *comp_stream = open_memstream(&comp_stream_buffer, &comp_stream_size);
    
    // need to call the OCaml code here
    fork_exec_binary("/fuzz_its/verified_format/_build/default/test/test.exe", buffer, buffer_size, comp_stream, 0);
  
    fflush(stream);
    fflush(comp_stream);

    //printf("stream buffer : \n%s", stream_buffer);
    
    int ocaml_error = 0;
    // first we see if OCaml is error
    if (strcmp(comp_stream_buffer, "\"Error\"") == 0) {
      ocaml_error = 1;
    }

    // now we see if they are both error
    int comp_val = 0;
    
    if (c_error == 1) {
      if (ocaml_error == 1) {

      } else {
	comp_val = 1;
      }
    } else {
      if (ocaml_error == 1) {
	comp_val = 1;
      } else {
	// printout the stream
	int final_pos =  remove_spaces(stream_buffer);
	//stream_buffer[final_pos - 1] = '\0';
	//printf("%s\n", (stream_buffer));

	
	/* Now we see if the comp-stream is True or False */
    
      
	if (strcmp(stream_buffer, comp_stream_buffer) == 0) {
	  comp_val = 0;
	} else {
	  comp_val = 1;
	}

      } 
    }


    //printf("verified stream buffer : %s", comp_stream_buffer);
    
    //printf ("\n Compare Value is %d", comp_val);

    fclose(comp_stream);
    free(comp_stream_buffer);

    fclose(stream);
    free(stream_buffer);


    if (comp_val == 1) {
      abort();
      // return 1;
    }
  }
  
  return 0; 
}
