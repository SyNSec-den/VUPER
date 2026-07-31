#include "srsran/asn1/rrc_nr/rrc_nr.h"
#include "srsran/asn1/rrc_nr/ul_dcch_msg.h"
//#include "srsran/support/test_utils.h"
#include <cstdio>
#include <iostream>
#include <stdio.h>

#include "util.h"

using namespace asn1;
using namespace asn1::rrc_nr;


int main () {
  constexpr size_t BUF_SIZE = 4096;  // Adjust as needed
  uint8_t rrc_msg[BUF_SIZE];

  //std::cin.read(reinterpret_cast<char*>(rrc_msg), BUF_SIZE);

  size_t buffer_size;

  buffer_size = fread(rrc_msg, 1, sizeof(rrc_msg), stdin);

  char *comp_stream_buffer = NULL; 
  size_t comp_stream_size = 0;

  // this is the buffer that will be fed into the python comparsion code
  FILE *comp_stream = open_memstream(&comp_stream_buffer, &comp_stream_size);
    
  // need to call the OCaml code here

  fprintf(comp_stream, "{ \"vp\" : ");
  fork_exec_binary("/fuzz/ocaml_test_ul_srs/_build/default/test/test.exe", (char*) rrc_msg, buffer_size, comp_stream, 0);

  fflush(comp_stream);



  //printf("%s\n", comp_stream_buffer);
  
  srsran::span<const uint8_t> byte_span(rrc_msg, buffer_size);
  srsran::byte_buffer pdu    = srsran::byte_buffer::create(byte_span).value();

  cbit_ref           bref(pdu);
  ul_dcch_msg_s     ul_dcch_msg;
  SRSASN_CODE c = ul_dcch_msg.unpack(bref);

  if (c == SRSASN_SUCCESS) {
    json_writer jw;
    ul_dcch_msg.to_json(jw);

    std::string msg_str = jw.to_string();

    // we are doing some trimming for the string
    msg_str.erase(std::remove_if(msg_str.begin(), msg_str.end(), ::isspace), msg_str.end());
    /* if (msg_str.size() >= 31) {
      // Remove the first 31 characters
      msg_str.erase(0, 31);
      msg_str.erase(msg_str.size() - 3, 2);
      }
    */

    fprintf(comp_stream, ", \"srs\" : %s }", msg_str.c_str());
     
  }
  
  else { // (c == SRSASN_ERROR_DECODE_FAIL)
    fprintf(comp_stream, ", \"srs\" : \"Error\" }");
  }

  fflush(comp_stream);
  // the stream that will catch the python output
  char *stream_buffer = NULL; 
  size_t stream_size = 0;

  FILE *stream = open_memstream(&stream_buffer, &stream_size);

  fork_exec_binary("/fuzz/pycrate_dir/pycrate_test/rename_srs.py", comp_stream_buffer, comp_stream_size, stream, 1);

  fflush(stream);
  //printf("%s", stream_buffer);
  if (strcmp(stream_buffer, "True\n") != 0) {
    abort();
  }
  
  fclose(comp_stream);
  free(comp_stream_buffer);
  
  fclose(stream);
  free(stream_buffer);

}
