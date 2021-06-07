[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/SMT-COMP/scrambler.svg?branch=master)](https://travis-ci.com/SMT-COMP/scrambler)

SMT-COMP Benchmark Scrambler
===============================================================================

This is the official SMT-COMP benchmark scrambler, used as a pre-processor for
all tracks of SMT-COMP.


## Known limitations

Benchmarks that contain deeply nested terms require a large stack to be
scrambled. (This is caused by the recursive implementation of benchmark
printing, which recurses over each term's parse tree.) The default stack
size of 8192 KB on Linux systems is sufficient for terms with a depth of
about 80,000. Some benchmarks in SMT-LIB do contain more deeply nested
terms. To process such benchmarks, the stack limit needs to be increased
(using, e.g., `ulimit -s 1048576) before the scrambler is invoked. Otherwise,
the scrambler may cause a segmentation fault.


## Usage

#### Single-Query Track and Industry Challenge Track

See [process.single-query-challenge-track](process.single-query-challenge-track).
```
ulimit -s 1048576
./scrambler -seed <seed> < <benchmark>
```

#### Incremental Track

See [process.incremental-track](process.incremental-track).

```
# extract the expected results of check-sat commands and prepend them
# to the scrambled benchmark (in their original order) -- this format
# is expected by the trace executor
grep 'set-info :status' "$1"|sed 's/(set-info :status \(.*\))/\1/'
echo "--- BENCHMARK BEGINS HERE ---"
ulimit -s 1048576
./scrambler -seed <seed> < <benchmark>
```

#### Model-Validation Track

See [process.model-val-track](process.model-val-track).

```
ulimit -s 1048576
./scrambler -seed <seed> -gen-model-val true < <benchmark>
```

#### Unsat-Core Track

See [process.unsat-core-track](process.unsat-core-track).

```
ulimit -s 1048576
./scrambler -seed <seed> -gen-unsat-core true < <benchmark>
```
