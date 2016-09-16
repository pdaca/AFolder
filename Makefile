CXX=		g++
DEVFLAGS=	-g -DINFO -DDEBUG
PRODFLAGS=	-DNDEBUG
CXXFLAGS=	-O2 -Wall -Wextra -Wshadow -ansi -pedantic -Wno-unused-parameter -std=c++11 -DTIXML_USE_STL  $(DEVFLAGS) -Weffc++
LDFLAGS= 	-Wall
LDLIBS= 	-lz3 
TARGET=		afolder

SRCS=		common.cc automata.cc scm.cc parikh.cc graph.cc semptiness.cc folds.cc afolder.cc tinyxml/tinystr.cc tinyxml/tinyxml.cc tinyxml/tinyxmlerror.cc tinyxml/tinyxmlparser.cc
OBJS=		$(subst .cc,.o,$(SRCS))

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) $(LDFLAGS) -o $(TARGET) $(OBJS) $(LDLIBS)

%.o: %.cc
	$(CXX) -c $(CXXFLAGS) $< -o $@

clean:
	rm -f $(TARGET) $(OBJS) *~
