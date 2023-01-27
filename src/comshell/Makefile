#================================================================
# A generic makefile for Java projects, for use with GNU make.
#
# By Scott Sanner
# $Revision: 1.1 $
#================================================================

# environment settings:
JAVAC   = javac -classpath ../
JAVADOC = javadoc
JAVA    = java

# project specifics:
CLASSES      = Command.class CommandInterface.class ComShell.class

#
# uncomment and modify this if you want to build subpackages
PACKAGES     = 

# Explain to make how compiling Java code works...
.SUFFIXES :     .class .java
.java.class :
	$(JAVAC) $<

# Some other useful macros we can derive...
SRCS = $(CLASSES:.class=.java)
DOCS = $(CLASSES:.class=.html)

# Typical make targets:
all: $(CLASSES) $(PACKAGES)

clean:
	-rm *.class

# Packages: No subpackages yet

# This is a dummy target that can be used to ensure that a target's
# dependencies are never satisfied.  This is useful because by default, make
# treats the presence of a directory with the same name as the target as an
# up-to-date target.
ALWAYS_BUILD:
