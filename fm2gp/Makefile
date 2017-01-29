# eop Makefile

CC       = /usr/local/bin/g++
DEBUG    = -O0 -ggdb -pg
//CFLAGS   = -Wall
CFLAGS   = -std=c++1z -fconcepts
CXXFLAGS = $(CFLAGS)
LDFLAGS	 = -g


TARGETS=ch02 ch03 ch04 ch07 ch08 ch10 ch11 ch12 ch13
INCLUDES=

all:$(TARGETS)

ch02: ch02.o
	$(CC) $(LDFLAGS) $^ -o $@

ch02.o: ch02.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch03: ch03.o
	$(CC) $(LDFLAGS) $^ -o $@

ch03.o: ch03.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch04: ch04.o
	$(CC) $(LDFLAGS) $^ -o $@

ch04.o: ch04.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch07: ch07.o
	$(CC) $(LDFLAGS) $^ -o $@

ch07.o: ch07.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch08: ch08.o
	$(CC) $(LDFLAGS) $^ -o $@

ch08.o: ch08.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch10: ch10.o
	$(CC) $(LDFLAGS) $^ -o $@

ch10.o: ch10.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch11: ch11.o
	$(CC) $(LDFLAGS) $^ -o $@

ch11.o: ch11.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch12: ch12.o
	$(CC) $(LDFLAGS) $^ -o $@

ch12.o: ch12.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

ch13: ch13.o
	$(CC) $(LDFLAGS) $^ -o $@

ch13.o: ch13.cpp $(INCLUDES)
	$(CC) $(CXXFLAGS) -c $< -o $@

.PHONY: clean

clean :
	rm ch02 ch03 ch04 ch07 ch08 ch10 ch11 ch12 ch13
	rm -rf *.o

