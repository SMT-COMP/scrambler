This is the official SMT-COMP benchmark scrambler for SMT-LIB scripts.


KNOWN LIMITATIONS:

1.) Benchmarks that contain deeply nested terms require a large stack
    to be scrambled. (This is caused by the recursive implementation
    of benchmark printing, which recurses over each term's parse
    tree.) The default stack size of 8192 KB on Linux systems is
    sufficient for terms with a depth of about 80,000. Some benchmarks
    in SMT-LIB do contain more deeply nested terms. To process such
    benchmarks, the stack limit needs to be increased (using, e.g.,
    ulimit -s 131072) before the scrambler is invoked. Otherwise, the
    scrambler may cause a segmentation fault.

2.) There is no support for separate namespaces for, e.g., sort and
    function symbols. All names (within the same namespace) must be
    distinct.


Author: Tjark Weber <tjark.weber@it.uu.se> (2015-2018)
Author: Alberto Griggio <griggio@fbk.eu> (2011)

License: MIT

Copyright (C) 2011 Alberto Griggio

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
