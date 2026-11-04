
CXX = g++
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra

SOURCES = $(wildcard *.cpp)
PROGRAMS = $(SOURCES:.cpp=)

all: $(PROGRAMS)

%: %.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f $(PROGRAMS)

.PHONY: all clean
