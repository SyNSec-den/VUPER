/**
 * Copyright 2013-2023 Software Radio Systems Limited
 *
 * This file is part of srsRAN.
 *
 * srsRAN is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of
 * the License, or (at your option) any later version.
 *
 * srsRAN is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * A copy of the GNU Affero General Public License can be found in
 * the LICENSE file in the top-level directory of this distribution
 * and at http://www.gnu.org/licenses/.
 *
 */

#include <getopt.h>
#include <iostream>

#include "srsran/asn1/asn1_utils.h"
#include "srsran/asn1/rrc.h"
#include "util.h"

using namespace std;

using namespace asn1;
using namespace asn1::rrc;


int main(int argc, char** argv)
{
  SRSASN_CODE err_code = SRSASN_ERROR_DECODE_FAIL;

  constexpr size_t BUF_SIZE = 4096;  // Adjust as needed
  uint8_t rrc_msg[BUF_SIZE];
  
  size_t buffer_size;

  buffer_size = fread(rrc_msg, 1, sizeof(rrc_msg), stdin);

 
  char *comp_stream_buffer = NULL; 
  size_t comp_stream_size = 0;

  // this is the buffer that will be fed into the python comparsion code
  FILE *comp_stream = open_memstream(&comp_stream_buffer, &comp_stream_size);
    
  // need to call the OCaml code here

  fprintf(comp_stream, "{ \"vp\" : ");
  fork_exec_binary("/fuzz_lte/verified_format/_build/default/test/test.exe", (char*) rrc_msg, buffer_size, comp_stream, 0);

  fflush(comp_stream);


  asn1::cbit_ref bref(rrc_msg, buffer_size);
  // TODO do other rrc messages and type

  dl_dcch_msg_s dl_dcch_msg;
  err_code = dl_dcch_msg.unpack(bref);
  if (err_code == SRSASN_SUCCESS) {
    //printf("Decoding Success\n");
    json_writer jw;
    dl_dcch_msg.to_json(jw);

    std::string msg_str = jw.to_string();

    msg_str.erase(std::remove_if(msg_str.begin(), msg_str.end(), ::isspace), msg_str.end());
    fprintf(comp_stream, ", \"srs\" : %s }", msg_str.c_str());
  } else {
    fprintf(comp_stream, ", \"srs\" : \"Error\" }");
  }
   
  fflush(comp_stream);
  // the stream that will catch the python output
  char *stream_buffer = NULL; 
  size_t stream_size = 0;

  FILE *stream = open_memstream(&stream_buffer, &stream_size);

  fork_exec_binary("/fuzz_lte/pycrate_test/rename_srs.py", comp_stream_buffer, comp_stream_size, stream, 1);

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
