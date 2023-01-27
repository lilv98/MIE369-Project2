#================================================================
# A Makefile for the fodt (first-order decision theory) package
# and subpackages.
#
# Author: Scott Sanner
# $Revision: 1.1 $
#================================================================

# environment settings:
JAVAC   = javac -classpath ..:../lib/jtp.jar
JAVADOC = javadoc
JAVA    = java

# project specifics:
#CLASSES      = LShell.class
CLASSES      = 

#
# list of subpackages:
PACKAGES     = add kb

# Explain to make how compiling Java code works...
.SUFFIXES :     .class .java
.java.class :
	$(JAVAC) $<

# some other useful macros we can derive...
SRCS = $(CLASSES:.class=.java)
DOCS = $(CLASSES:.class=.html)

# Typical make targets:
all: $(CLASSES) $(PACKAGES)

docs: ALWAYS_BUILD
	-mkdir docs; \
	$(JAVADOC) -author -d docs $(SRCS) $(PACKAGES)

clean:
	-rm ./*.class ./*~ ./*/*.class ./*/*~ ./*/*/*.class ./*/*/*~

# Packages:
docs: ALWAYS_BUILD
	-mkdir javadoc; \
	$(JAVADOC) -author -d javadoc $(ALL_PACKAGES)

instr: ALWAYS_BUILD
	cd docs; m; m; b; m; ps2pdf project1.ps project1.pdf

add: ALWAYS_BUILD
	cd add; $(MAKE) all

kb: ALWAYS_BUILD
	cd kb; $(MAKE) all

wc: ALWAYS_BUILD
	wc `find . -name "*.java"`

# This is a dummy target that can be used to ensure that a target's
# dependencies are never satisfied.  This is useful because by default, make
# treats the presence of a directory with the same name as the target as an
# up-to-date target.
ALWAYS_BUILD:
