CXX = g++ -D_GLIBCXX_USE_CXX11_ABI=0 -std=c++11
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

SMT-COMP-2020-single-query-scrambler.tar.xz: scrambler
	cp process.single-query-challenge-track process
	tar -cJf $@ process scrambler
	rm process

SMT-COMP-2020-incremental-scrambler.tar.xz: scrambler
	cp process.incremental-track process
	tar -cJf $@ process scrambler
	rm process

SMT-COMP-2020-unsat-core-scrambler.tar.xz: scrambler
	cp process.unsat-core-track process
	tar -cJf $@ process scrambler
	rm process

SMT-COMP-2020-model-validation-scrambler.tar.xz: scrambler
	cp process.model-val-track process
	tar -cJf $@ process scrambler
	rm process

.PHONY: all clean cleanall

all: scrambler SMT-COMP-2020-single-query-scrambler.tar.xz SMT-COMP-2020-incremental-scrambler.tar.xz SMT-COMP-2020-unsat-core-scrambler.tar.xz SMT-COMP-2020-model-validation-scrambler.tar.xz

clean:
	rm -f $(OBJECTS) lexer.cpp lexer.h parser.cpp parser.h parser.output

cleanall: clean
	rm -f scrambler SMT-COMP-2020-single-query-scrambler.tar.xz SMT-COMP-2020-incremental-scrambler.tar.xz SMT-COMP-2020-unsat-core-scrambler.tar.xz SMT-COMP-2020-model-validation-scrambler.tar.xz
