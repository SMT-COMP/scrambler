CXX = g++ -D_GLIBCXX_USE_CXX11_ABI=0
CXXFLAGS = -g -O3
LDFLAGS = -g -static

OBJECTS = scrambler.o \
	  parser.o \
	  lexer.o

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $<

scrambler: $(OBJECTS)
	$(CXX) $(OBJECTS) $(LDFLAGS) -o $@

scrambler.cpp: parser.cpp

parser.cpp: parser.y lexer.cpp
	bison -o $@ $<

lexer.cpp: lexer.l
	flex --header-file="lexer.h" -o $@ $<

test: scrambler
	test/run_tests.sh

# targets to prepare StarExec preprocessors

SMT-COMP-Scrambler.tgz: scrambler
	cp process.main-track process
	tar -czf SMT-COMP-Scrambler.tgz process scrambler
	rm process

SMT-COMP-Application-Scrambler.tgz: scrambler
	cp process.application-track process
	tar -czf SMT-COMP-Application-Scrambler.tgz process scrambler
	rm process

SMT-COMP-Unsat-Core-Scrambler.tgz: scrambler
	cp process.unsat-core-track process
	tar -czf SMT-COMP-Unsat-Core-Scrambler.tgz process scrambler
	rm process

.PHONY: all clean cleanall

all: scrambler SMT-COMP-Scrambler.tgz SMT-COMP-Application-Scrambler.tgz SMT-COMP-Unsat-Core-Scrambler.tgz

clean:
	rm -f $(OBJECTS) lexer.cpp lexer.h parser.cpp parser.h parser.output

cleanall: clean
	rm -f scrambler SMT-COMP-Scrambler.tgz SMT-COMP-Application-Scrambler.tgz SMT-COMP-Unsat-Core-Scrambler.tgz
