#include "CAM_PDU_Descriptions.hh"
#include "util.hh"
#include <cstdio>
#include <cstdlib>
#include <cstring>

int main() {
  // Suppress TITAN internal errors — handle them via get_last_error_type()
  TTCN_EncDec::set_error_behavior(TTCN_EncDec::ET_ALL, TTCN_EncDec::EB_IGNORE);

  while (__AFL_LOOP(10000)) {
    char buffer[4096];
    size_t buffer_size = fread(buffer, 1, sizeof(buffer), stdin);

    // --- Call OCaml reference ---
    char *ocaml_buf = NULL;
    size_t ocaml_size = 0;
    FILE *ocaml_stream = open_memstream(&ocaml_buf, &ocaml_size);
    fork_exec_binary("/fuzz_its/verified_format_utf8/_build/default/test/test.exe",
                     buffer, buffer_size, ocaml_stream, 0);
    fflush(ocaml_stream);

    int ocaml_error = (strcmp(ocaml_buf, "\"Error\"") == 0);

    // --- Decode with TITAN ---
    int titan_error = 0;
    char *titan_json = NULL;

    TTCN_EncDec::clear_error();
    TTCN_Buffer dec_buf;
    dec_buf.put_s(buffer_size, (const unsigned char *)buffer);

    CAM__PDU__Descriptions::CAM cam;
    cam.decode(*cam.get_descriptor(), dec_buf, TTCN_EncDec::CT_PER);

    if (TTCN_EncDec::get_last_error_type() != TTCN_EncDec::ET_NONE) {
      titan_error = 1;
    } else {
      // Encode to JSON
      TTCN_EncDec::clear_error();
      TTCN_Buffer json_buf;
      cam.encode(*cam.get_descriptor(), json_buf, TTCN_EncDec::CT_JSON);

      size_t json_len = json_buf.get_len();
      titan_json = (char *)malloc(json_len + 1);
      memcpy(titan_json, json_buf.get_data(), json_len);
      titan_json[json_len] = '\0';
      remove_spaces(titan_json);
      normalize_titan_json(titan_json);
    }

    // --- Compare ---
    int mismatch = 0;
    if (titan_error && ocaml_error) {
      // both fail — OK
    } else if (titan_error != ocaml_error) {
      mismatch = 1;
    } else {
      // both succeeded — compare JSON
      remove_spaces(ocaml_buf);
      if (strcmp(titan_json, ocaml_buf) != 0)
        mismatch = 1;
    }

    free(titan_json);
    fclose(ocaml_stream);
    free(ocaml_buf);

    if (mismatch)
      abort();
  }
  return 0;
}
