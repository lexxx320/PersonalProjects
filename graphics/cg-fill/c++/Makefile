#
# Created by gmakemake (Ubuntu Jul 25 2014) on Fri Feb 20 13:40:12 2015
#

#
# Definitions
#

.SUFFIXES:
.SUFFIXES:	.a .o .c .C .cpp .s .S
.c.o:
		$(COMPILE.c) $<
.C.o:
		$(COMPILE.cc) $<
.cpp.o:
		$(COMPILE.cc) $<
.S.s:
		$(CPP) -o $*.s $<
.s.o:
		$(COMPILE.cc) $<
.c.a:
		$(COMPILE.c) -o $% $<
		$(AR) $(ARFLAGS) $@ $%
		$(RM) $%
.C.a:
		$(COMPILE.cc) -o $% $<
		$(AR) $(ARFLAGS) $@ $%
		$(RM) $%
.cpp.a:
		$(COMPILE.cc) -o $% $<
		$(AR) $(ARFLAGS) $@ $%
		$(RM) $%

CC =		gcc
CXX =		g++

RM = rm -f
AR = ar
LINK.c = $(CC) $(CFLAGS) $(CPPFLAGS) $(LDFLAGS)
LINK.cc = $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS)
COMPILE.c = $(CC) $(CFLAGS) $(CPPFLAGS) -c
COMPILE.cc = $(CXX) $(CXXFLAGS) $(CPPFLAGS) -c
CPP = $(CPP) $(CPPFLAGS)
########## Flags from header.mak

#
# This header.mak file will set up all necessary options for compiling
# and linking C++ programs which use SFML on the CS Ubuntu systems.  IT
# WILL NOT WORK CORRECTLY FOR C PROGRAMS.
#
# To use it, place it in the same directory as your source code, and
# run the command
#
#	gmakemake > Makefile
#
# To compile and link your program, just run "make".
#
# If you want to take advantage of GDB's extra debugging features,
# change "-g" in the CFLAGS and LIBFLAGS macro definitions to "-ggdb".
#
INCLUDE =
LIBDIRS =

LDLIBS = -lsfml-graphics -lsfml-window -lsfml-system

CFLAGS = -g $(INCLUDE)
CCFLAGS =  $(CFLAGS)
CXXFLAGS = $(CFLAGS)

LIBFLAGS = -g $(LIBDIRS) $(LDLIBS)
CLIBFLAGS = $(LIBFLAGS)
CCLIBFLAGS = $(LIBFLAGS)

########## End of flags from header.mak


CPP_FILES =	Rasterizer.cpp fillTest.cpp simpleCanvas.cpp
C_FILES =	
PS_FILES =	
S_FILES =	
H_FILES =	Rasterizer.h simpleCanvas.h
SOURCEFILES =	$(H_FILES) $(CPP_FILES) $(C_FILES) $(S_FILES)
.PRECIOUS:	$(SOURCEFILES)
OBJFILES =	Rasterizer.o simpleCanvas.o 

#
# Main targets
#

all:	fillTest 

fillTest:	fillTest.o $(OBJFILES)
	$(CXX) $(CXXFLAGS) -o fillTest fillTest.o $(OBJFILES) $(CCLIBFLAGS)

#
# Dependencies
#

Rasterizer.o:	Rasterizer.h simpleCanvas.h
fillTest.o:	Rasterizer.h simpleCanvas.h
simpleCanvas.o:	simpleCanvas.h

#
# Housekeeping
#

Archive:	archive.tgz

archive.tgz:	$(SOURCEFILES) Makefile
	tar cf - $(SOURCEFILES) Makefile | gzip > archive.tgz

clean:
	-/bin/rm -f $(OBJFILES) fillTest.o core

realclean:        clean
	-/bin/rm -f fillTest 
