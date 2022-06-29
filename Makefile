YEAR=2022

CXX = g++ -D_GLIBCXX_USE_CXX11_ABI=0 -std=c++11
CXXFLAGS = -g -O3
LDFLAGS = -g

OBJECTS = scrambler.o \
	  parser.o \
	  lexer.o

PREPROCESSORS = \
	SMT-COMP-$(YEAR)-single-query-scrambler.tar.gz \
	SMT-COMP-$(YEAR)-incremental-scrambler.tar.gz \
	SMT-COMP-$(YEAR)-unsat-core-scrambler.tar.gz \
	SMT-COMP-$(YEAR)-model-validation-scrambler.tar.gz \
	SMT-COMP-$(YEAR)-proof-scrambler.tar.gz

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

SMT-COMP-$(YEAR)-single-query-scrambler.tar.gz: scrambler
	cp process.single-query-challenge-track process
	tar -czf $@ process scrambler
	rm process

SMT-COMP-$(YEAR)-incremental-scrambler.tar.gz: scrambler
	cp process.incremental-track process
	tar -czf $@ process scrambler
	rm process

SMT-COMP-$(YEAR)-unsat-core-scrambler.tar.gz: scrambler
	cp process.unsat-core-track process
	tar -czf $@ process scrambler
	rm process

SMT-COMP-$(YEAR)-model-validation-scrambler.tar.gz: scrambler
	cp process.model-val-track process
	tar -czf $@ process scrambler
	rm process

SMT-COMP-$(YEAR)-proof-scrambler.tar.gz: scrambler
	cp process.proof-track process
	tar -czf $@ process scrambler
	rm process

.PHONY: all clean cleanall

all: scrambler $(PREPROCESSORS)

clean:
	rm -f $(OBJECTS) lexer.cpp lexer.h parser.cpp parser.h parser.output

cleanall: clean
	rm -f scrambler $(PREPROCESSORS)

dist: $(PREPROCESSORS)
	cp $(PREPROCESSORS) /dist
