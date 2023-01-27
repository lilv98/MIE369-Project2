#================================================================
# A Makefile for the fodt (first-order decision theory) package
# and subpackages.
#
# Author: Scott Sanner
# $Revision: 1.1 $
#================================================================

# environment settings:
JAVAC   = javac -classpath ../..
JAVADOC = javadoc
JAVA    = java

# project specifics:
CLASSES      = Kb.class

#
# list of subpackages:
#PACKAGES     = prop fol
PACKAGES     = fol

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
	-rm ./*.class ./*~ ./*/*.class ./*/*~

# Packages:
prop: ALWAYS_BUILD
	cd prop; $(MAKE) all

fol: ALWAYS_BUILD
	cd fol; $(MAKE) all

# This is a dummy target that can be used to ensure that a target's
# dependencies are never satisfied.  This is useful because by default, make
# treats the presence of a directory with the same name as the target as an
# up-to-date target.
ALWAYS_BUILD:
