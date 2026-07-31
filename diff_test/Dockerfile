# Pinned to a stable tag: the `latest` tag no longer ships the
# custom_mutators/radamsa directory that the mutator build below expects.
# NOTE: confirm this tag matches your validated build environment.
FROM aflplusplus/aflplusplus:v4.30c

# Install dependencies
RUN apt-get update && apt-get install -y \
    clang make cmake python3 opam emacs curl

# Install OPAM
# RUN bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"

# RUN add-apt-repository ppa:avsm/ppa
# RUN apt install opam

# Initialize OPAM
RUN opam init -y --disable-sandboxing
RUN opam update

# OCaml 4.14 is required: fuzz_its/verified_format_utf8/src/FormatTest.ml calls
# String.is_valid_utf_8, which was only added in 4.14. On the old 4.11.2 switch
# that file failed to compile, which silently broke the three ITS harnesses that
# spawn its test.exe (pycrate, asn1tools, rasn) -- rasn in particular treats a
# failed spawn as a decoder disagreement and reports bogus differentials.
#
# No +afl compiler variant is needed. Nothing here fuzzes an OCaml program: the
# verified decoders are only ever run as subprocess oracles by the C, Python and
# Rust harnesses, so they need no AFL instrumentation (hence no afl-persistent).
RUN opam switch create vuper ocaml-base-compiler.4.14.2
RUN opam switch set vuper

# `mtime` is required by fuzz/ocaml_test/test/time_test.exe, otherwise a plain
# `dune build` in that directory fails on a missing mtime.clock.os library.
RUN eval $(opam env --switch=vuper) && \
    opam install -y dune ppx_import base ppx_deriving ppx_deriving_yojson re mtime

# Put the switch on PATH for every `docker exec`, login shell or not.
ENV PATH="/root/.opam/vuper/bin:${PATH}"

# Single quotes are deliberate. With double quotes, $(opam env) expands at image
# BUILD time and bakes a frozen snapshot of one switch into .bashrc; it must be
# evaluated when the shell starts instead.
#
# `ulimit -s unlimited` is required: natively compiling the generated NR/EUTRA
# format modules overflows the default 8 MB stack ("Fatal error: exception
# Stack overflow") in fuzz_lte/verified_format and fuzz/ocaml_test_ul_srs.
RUN printf '%s\n' 'eval $(opam env)' 'ulimit -s unlimited' >> /root/.bashrc

# Rust is already installed in the aflplusplus base image (cargo on PATH at
# /etc/cargo/bin), so no separate rustup install is needed to build the mutator.


RUN pip install pycrate python-afl

RUN apt update && apt install -y libssl-dev libmbedtls-dev libgtest-dev libyaml-cpp-dev

# srsRAN (5G and 4G) build dependencies
RUN apt-get update && apt-get install -y --fix-missing \
    libfftw3-dev \
    libboost-program-options-dev \
    libsctp-dev \
    libconfig-dev \
    libconfig++-dev

# Python packages: srsRAN JSON comparison, plus asn1tools and its disk cache
# for the ITS asn1tool_test harness (which does `import asn1tools`).
RUN pip install diskcache deepdiff asn1tools


# Set environment for AFL++
ENV AFL_SKIP_CPUFREQ=1
ENV AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1

# I also need to go and compile the radsama in AFL++ custom mutators
WORKDIR /AFLplusplus/custom_mutators/radamsa
RUN make


# need to directly copy ASN1fuzzgen into here, 
COPY ./ASN_Coding /AFLplusplus/custom_mutators/

# now we make the ASN library: build the Rust release archive first,
# then link it into the AFL++ custom mutator shared object.
# Both crates depend on ../asnfuzzgen (codecs + codecs_derive), which the COPY
# above brings in, so the build runs entirely in-image.
WORKDIR /AFLplusplus/custom_mutators/asnfuzz-rrc-uper
RUN cargo build --release
RUN make mutator

WORKDIR /AFLplusplus/custom_mutators/asnfuzz-lte-uper
RUN cargo build --release
RUN make mutator


# Point AFL++ at the 5G NR mutator by default. Use ENV (not `RUN export`, which
# does not persist across layers). Override at `afl-fuzz` time with the LTE
# module: /AFLplusplus/custom_mutators/asnfuzz-lte-uper/libasnfuzz_lte_uper.so
ENV AFL_CUSTOM_MUTATOR_LIBRARY="/AFLplusplus/custom_mutators/asnfuzz-rrc-uper/libasnfuzz_rrc_uper.so"



WORKDIR /

RUN mkdir fuzz

# Rust nightly + cargo-afl (for the ITS RASN fuzzer). Installed *after* the
# mutator builds on purpose: prepending /root/.cargo/bin to PATH would shadow
# the base image's cargo, and the mutator crates are known to build with it.
ENV RUSTUP_HOME=/root/.rustup \
    CARGO_HOME=/root/.cargo
ENV PATH="/root/.cargo/bin:${PATH}"
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- -y --default-toolchain nightly --no-modify-path
RUN /root/.cargo/bin/cargo install cargo-afl


# Build C code with AFL++
# RUN AFL_CC=afl-clang-fast make  # or use afl-gcc / afl-clang-lto if needed

# clean up the apt directory
#  && rm -rf /var/lib/apt/lists/*

# Start fuzzing
CMD ["/bin/bash"]
