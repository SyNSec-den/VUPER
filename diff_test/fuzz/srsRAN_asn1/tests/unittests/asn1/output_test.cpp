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
 
  
  srsran::span<const uint8_t> byte_span(rrc_msg, buffer_size);
  srsran::byte_buffer pdu    = srsran::byte_buffer::create(byte_span).value();

  fmt::print("PDU INPUT: {}\n", pdu);
  
  cbit_ref           bref(pdu);
  ul_dcch_msg_s     ul_dcch_msg;
  SRSASN_CODE c = ul_dcch_msg.unpack(bref);

  if (c == SRSASN_SUCCESS) {
    json_writer jw;
    ul_dcch_msg.to_json(jw);

    std::string msg_str = jw.to_string();

    // we are doing some trimming for the string
    //msg_str.erase(std::remove_if(msg_str.begin(), msg_str.end(), ::isspace), msg_str.end());
    /* if (msg_str.size() >= 31) {
      // Remove the first 31 characters
      msg_str.erase(0, 31);
      msg_str.erase(msg_str.size() - 3, 2);
      }
    */

    printf("srs accept: %s\n", msg_str.c_str());

    // here we try to encode the message back into a buffer
    srsran::byte_buffer buffer_enc;
    asn1::bit_ref       bref_enc(buffer_enc);
    SRSASN_CODE c1 =  ul_dcch_msg.pack(bref_enc);

    if (c1 == SRSASN_SUCCESS) {
      fmt::print("PDU: {}\n", buffer_enc);
    } else {
      printf("Fails to encode the unpacked message");
    }
        
    //std::string result = fmt::format("{}", buffer_enc);
    //std::cout << result << std::endl;
  }
  
  else { // (c == SRSASN_ERROR_DECODE_FAIL)
    printf("srs : Error\n");
  }

  return 0;
}
