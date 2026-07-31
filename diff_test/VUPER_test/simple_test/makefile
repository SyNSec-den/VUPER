# makefile to build generated files

include ../asn1c-v790/c/platform.mk

# include directories
OSROOTDIR = ..$(PS)asn1c-v790
LIBDIR  = $(OSROOTDIR)$(PS)c$(RTDIRSFX)$(PS)lib
RTSRCDIR = $(OSROOTDIR)$(PS)rtsrc
RTXSRCDIR = $(OSROOTDIR)$(PS)rtxsrc
PERSRCDIR = $(OSROOTDIR)$(PS)rtpersrc
SRCDIR = .
HFILESDIR = .
HFILES =  \
$(RTSRCDIR)$(PS)asn1type.h \
$(RTXSRCDIR)$(PS)osMacros.h \
$(RTXSRCDIR)$(PS)osSysTypes.h \
$(RTXSRCDIR)$(PS)rtxContext.h \
$(RTXSRCDIR)$(PS)rtxDList.h \
$(RTXSRCDIR)$(PS)rtxExternDefs.h \
$(RTXSRCDIR)$(PS)rtxCommonDefs.h \
$(RTXSRCDIR)$(PS)rtxStack.h \
$(PERSRCDIR)$(PS)asn1per.h

# compiler defs
CFLAGS = -c $(CVARS_) $(CFLAGS_) $(CBLDTYPE_)
IPATHS = -I$(SRCDIR) -I$(OSROOTDIR) -I$(RTSRCDIR) -I$(PERSRCDIR) $(IPATHS_)
LINKOPT = $(LINKOPT_)

# run-time libraries
LIBS = $(LIBDIR)/$(LIBPFX)asn1per$(A) $(LIBDIR)/$(LIBPFX)asn1json$(A) $(LIBDIR)/$(LIBPFX)asn1rt$(A)
LLIBS = $(LLPFX)asn1per$(LLAEXT) $(LLPFX)asn1json$(LLAEXT) $(LLPFX)asn1rt$(LLAEXT) $(LLSYS)
LPATHS = $(LPPFX)$(LIBDIR)

OBJECTS =  \
Foo$(OBJ) main$(OBJ)

ENCOBJECTS =  \
FooEnc$(OBJ)

DECOBJECTS =  \
FooDec$(OBJ)

EXEC = main-test

all : $(EXEC)

$(EXEC): $(OBJECTS) $(ENCOBJECTS) $(DECOBJECTS)
	$(CC)  $(OBJECTS) $(ENCOBJECTS) $(DECOBJECTS) $(LIBS) -o $(EXEC)

# .c -> .obj rules
# common file rules
Foo$(OBJ) : $(SRCDIR)$(PS)Foo.c \
$(HFILESDIR)$(PS)Foo.h \
$(HFILESDIR)$(PS)rtkey.h \
$(HFILES)
	$(CC) $(CFLAGS) -c $(IPATHS) $(SRCDIR)$(PS)Foo.c

# decode file rules
FooDec$(OBJ) : $(SRCDIR)$(PS)FooDec.c \
$(HFILESDIR)$(PS)Foo.h \
$(HFILESDIR)$(PS)rtkey.h \
$(HFILES)
	$(CC) $(CFLAGS) -c $(IPATHS) $(SRCDIR)$(PS)FooDec.c

main$(OBJ) : $(SRCDIR)$(PS)main.c \
$(HFILESDIR)$(PS)Foo.h \
$(HFILESDIR)$(PS)rtkey.h \
$(HFILES)
	$(CC) $(CFLAGS) -c $(IPATHS) $(SRCDIR)$(PS)main.c

# encode file rules
FooEnc$(OBJ) : $(SRCDIR)$(PS)FooEnc.c \
$(HFILESDIR)$(PS)Foo.h \
$(HFILESDIR)$(PS)rtkey.h \
$(HFILES)
	$(CC) $(CFLAGS) -c $(IPATHS) $(SRCDIR)$(PS)FooEnc.c

# .asn -> .c .h rules
$(SRCDIR)/FooEnc.c \
$(SRCDIR)/FooDec.c \
$(SRCDIR)/Foo.c \
$(HFILESDIR)$(PS)Foo.h \
$(HFILESDIR)$(PS)rtkey.h \
\
: .$(PS)test.asn1 $(OSROOTDIR)$(PS)bin$(PS)asn1c$(EXE)
	$(OSROOTDIR)$(PS)bin$(PS)asn1c .$(PS)test.asn1 -c -json -uper -fqtvalue

clean:
	$(RM) FooEnc.c
	$(RM) FooDec.c
	$(RM) Foo.c
	$(RM) $(HFILESDIR)$(PS)Foo.h
	$(RM) $(HFILESDIR)$(PS)rtkey.h
	$(RM) $(HFILESDIR)$(PS)rtkey.h
	$(RM) *$(OBJ)
	$(RM) main-test
	$(RM) *~
	$(RM_MSVC_FILES)
