# Compiler
CC = gcc

# Compiler flags
CFLAGS = -Wall -O2

# Linker flags
LDFLAGS = /AFLplusplus/custom_mutators/asnfuzz-rrc-uper/target/release/libasnfuzz_rrc_uper.a /AFLplusplus/custom_mutators/radamsa/libradamsa.a -ldl -lpthread

# Target executable
TARGET = test

# mutator target
MUT = asn_mutator.c

# Source files
SRCS = test.c

# Object files
OBJS = $(SRCS:.c=.o)

# Default rule
test: $(TARGET)

# rule for mutator
mutator:
	$(CC) $(CFLAGS) -funroll-loops -shared $(MUT) $(LDFLAGS) -fPIC -I ../../include -I ../radamsa/ -o libasnfuzz_rrc_uper.so

# Linking
$(TARGET): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LDFLAGS) -o $(TARGET)

# Compiling source files to object files
%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

# Clean up
clean:
	rm -f $(OBJS) $(TARGET)

.PHONY: all clean
