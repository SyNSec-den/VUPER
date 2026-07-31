#include <iostream>
#include <string>
#include "Foo.hh"


int main() {
  std::string input;

  // Read from stdin (entire line)
  std::getline(std::cin, input);

  // Convert to OCTETSTRING
  OCTETSTRING oct(static_cast<int>(input.size()), reinterpret_cast<const uint8_t*>(input.data()));


  //printf("Encoding: %s\n", (const char*) oct.log());

  try {
    Foo::S1 s1;
    INTEGER myResult = Foo::S1_decoder(oct, s1, ASN_EncDec::CT_PER, PER_UNALIGNED);

    OCTETSTRING out_buf;
    // 0 for compact encoding
    Foo::S1_encoder(s1, out_buf, ASN_EncDec::CT_JSON, 0);

    const unsigned char* data = out_buf;
    printf("Decoding: %s : %s\n",
	   (const char*) oct.log(),
	   (const char*) data);

  } 
  catch (ASN_Error e) {
    printf("%s\n", e.get_message());
  }
  
  return 0;
}
