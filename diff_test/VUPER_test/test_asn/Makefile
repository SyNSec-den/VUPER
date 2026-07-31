# Compiler
CXX = g++

# Compiler Flags
CXXFLAGS = -Wall -Wextra -DTITAN_ASN1ENC -DLINUX -I$(TTCN3_DIR)/include

# Linker Flags
LDFLAGS = -L$(TTCN3_DIR)/lib -lasn1enc -lcrypto

# Source Files
SRCS = Foo.cc main.cc

# Object Files
OBJS = $(SRCS:.cc=.o)

# Output Executable
TARGET = main-test

# Default Rule
all: $(TARGET)

# Compile source files into object files
%.o: %.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@

# Link object files into the final executable
$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LDFLAGS)

# Clean build artifacts
clean:
	rm -f $(TARGET) $(OBJS)
