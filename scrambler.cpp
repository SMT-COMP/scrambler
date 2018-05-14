/* -*- C++ -*-
 *
 * A simple scrambler for SMT-LIB 2.6 scripts
 *
 * Author: Tjark Weber <tjark.weber@it.uu.se> (2015-2018)
 * Author: Alberto Griggio <griggio@fbk.eu> (2011)
 *
 * Copyright (C) 2011 Alberto Griggio
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include "scrambler.h"
#include <tr1/unordered_map>
#include <tr1/unordered_set>
#include <sstream>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <iostream>
#include <string.h>
#include <iomanip>
#include <fstream>
#include <algorithm>
#include <assert.h>
#include <ctype.h>
#include <stack>

////////////////////////////////////////////////////////////////////////////////

/*
 * pseudo-random number generator
 */
uint64_t seed;
const uint64_t a = 25214903917ULL;
const uint64_t c = 11U;
const uint64_t mask = ~(2ULL << 48);

void set_seed(int s)
{
    seed = s;
}

size_t next_rand_int(size_t upper_bound)
{
    seed = ((seed * a) + c) & mask;
    return (size_t)(seed >> 16U) % upper_bound;
}

////////////////////////////////////////////////////////////////////////////////

/*
 * If set to true, many of the scrambling transformations (e.g., shuffling of
 * assertions, permutation of names, etc.) will not be applied.
 */
bool no_scramble = false;

/*
 * If set to true, the following modifications will be made additionally:
 * 1. The command (set-option :produce-unsat-cores true) will be prepended.
 * 2. A (get-unsat-core) command will be inserted after each (check-sat) command.
 * 3. Each (assert fmla) will be replaced by (assert (! fmla :named freshId))
 *    where freshId is some fresh identifier.
 */
bool generate_unsat_core_benchmark = false;

////////////////////////////////////////////////////////////////////////////////

/*
 * Scrambling of symbols (i.e., names) declared in the benchmark. For
 * details see "Scrambling and Descrambling SMT-LIB Benchmarks" (Tjark
 * Weber; in Tim King and Ruzica Piskac, editors, Proceedings of the
 * 14th International Workshop on Satisfiability Modulo Theories,
 * Coimbra, Portugal, July 1-2, 2016, volume 1617 of CEUR Workshop
 * Proceedings, pages 31-40, July 2016).
 *
 * There are three kinds of names: (1) names declared in the input
 * benchmark (e.g., sort symbols, function symbols, bound variables);
 * (2) name identifiers used during parsing; and (3) uniform names
 * (i.e., x1, x2, ...) used when the scrambled benchmark is printed.
 *
 * Benchmark-declared names are read during parsing and stored in the
 * nodes of the parse tree; specifically, in their symbol field (which
 * is otherwise also used to store SMT-LIB commands, keywords, etc.).
 *
 * In addition, a bijection between benchmark-declared names and name
 * identifiers is built during parsing, and extended whenever a
 * declaration or binder (of a new name) is encountered. Note that
 * name identifiers are not necessarily unique, i.e., they do not
 * resolve shadowing.
 *
 * Finally, when the scrambled benchmark is printed, name identifiers
 * are permuted randomly before they are turned into uniform names.
 */

typedef std::tr1::unordered_map<std::string, uint64_t> Name_ID_Map;

// a map from benchmark-declared symbols to name identifiers
Name_ID_Map name_ids;

// |foo| and foo denote the same symbol in SMT-LIB, hence the need to
// remove |...| quotes before symbol lookups
const char *unquote(const char *n)
{
    if (!n[0] || n[0] != '|') {
        return n;
    }

    static std::string buf;
    buf = n;
    assert(!buf.empty());
    if (buf.size() > 1 && buf[0] == '|' && buf[buf.size()-1] == '|') {
        buf = buf.substr(1, buf.size()-2);
    }
    return buf.c_str();
}

// the next available name id
uint64_t next_name_id = 1;

namespace scrambler {

// declaring a new name
void set_new_name(const char *n)
{
    n = unquote(n);

    if (name_ids.find(n) == name_ids.end()) {
        name_ids[n] = next_name_id;
        ++next_name_id;
    }
}

} // namespace

uint64_t get_name_id(const char *n)
{
    n = unquote(n);

    return name_ids[n];  // 0 if n is not currently in name_ids
}

////////////////////////////////////////////////////////////////////////////////

namespace scrambler {

void node::add_children(const std::vector<node *> *c)
{
    children.insert(children.end(), c->begin(), c->end());
}

} // namespace

////////////////////////////////////////////////////////////////////////////////

/*
 * The main data structure: here the benchmark's commands are added as
 * they are parsed (and removed when they have been printed).
 */
std::vector<scrambler::node *> commands;

namespace scrambler {

void add_node(const char *s, node *n1, node *n2, node *n3, node *n4)
{
    assert(s); // s must be a top-level SMT-LIB command

    node *ret = new node;
    ret->symbol = s;
    ret->is_name = false;
    ret->needs_parens = true;

    if (n1) {
        ret->children.push_back(n1);
    }
    if (n2) {
        ret->children.push_back(n2);
    }
    if (n3) {
        ret->children.push_back(n3);
    }
    if (n4) {
        ret->children.push_back(n4);
    }

    commands.push_back(ret);
}

node *make_node(const char *s, node *n1, node *n2)
{
    node *ret = new node;
    ret->needs_parens = true;
    if (s) {
        ret->symbol = s;
    }
    ret->is_name = false;
    if (n1) {
        ret->children.push_back(n1);
    }
    if (n2) {
        ret->children.push_back(n2);
    }
    if (!ret->symbol.empty() && ret->children.empty()) {
        ret->needs_parens = false;
    }
    return ret;
}

node *make_node(const std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->is_name = false;
    ret->children.assign(v->begin(), v->end());
    return ret;
}

node *make_node(node *n, const std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->is_name = false;
    ret->children.push_back(n);
    ret->children.insert(ret->children.end(), v->begin(), v->end());
    return ret;
}

node *make_name_node(const char* s, node *n1)
{
    node *ret = new node;
    assert(s);
    ret->symbol = s;
    ret->is_name = true;
    ret->needs_parens = false;
    if (n1) {
        ret->children.push_back(n1);
        ret->needs_parens = true;
    }
    return ret;
}   

void del_node(node *n)
{
    for (size_t i = 0; i < n->children.size(); ++i) {
        del_node(n->children[i]);
    }
    delete n;
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

void shuffle_list(std::vector<scrambler::node *> *v, size_t start, size_t end)
{
    if (!no_scramble) {
        size_t n = end - start;
        for (size_t i = n-1; i > 0; --i) {
            std::swap((*v)[i+start], (*v)[next_rand_int(i+1)+start]);
        }
    }
}

namespace scrambler {

void shuffle_list(std::vector<node *> *v)
{
    ::shuffle_list(v, 0, v->size());
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

/*
 * functions that set or depend on the benchmark's logic
 */

std::string logic;

namespace scrambler {

void set_logic(const std::string &l)
{
    // each benchmark contains a single set-logic command
    if (!logic.empty()) {
        std::cerr << "ERROR logic is already set" << std::endl;
        exit(1);
    }

    logic = l;
}

} // scrambler

bool logic_is_dl()  // Difference Logic: IDL, RDL
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("IDL") != std::string::npos || logic.find("RDL") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return (result == 1);
}

bool logic_is_arith()  // Arithmetic: IA, RA, IRA
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("IA") != std::string::npos || logic.find("RA") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return (result == 1);
}

bool logic_is_bv()  // BitVectors (BV)
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("BV") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return result == 1;
}

bool logic_is_fp()  // FloatingPoint (FP)
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("FP") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return result == 1;
}

namespace scrambler {

bool is_commutative(const node *n)
{
    // *n might be a qualified identifier of the form ('as' identifier sort)
    const std::string *symbol = &(n->symbol);
    if (*symbol == "as") {
        assert(n->children.size() > 0);
        symbol = &(n->children[0]->symbol);
    }
    const std::string &s = *symbol;
    assert(!s.empty());

    // Core theory
    if (s == "and" || s == "or" || s == "xor" || s == "distinct") {
        return true;
    }
    if (!logic_is_dl()) {
        if (s == "=") {
            return true;
        }
    }

    // arithmetic (IA, RA, IRA) (but not difference logic)
    if (logic_is_arith()) {
        if (s == "*" || s == "+") {
            return true;
        }
    }

    // BitVectors
    if (logic_is_bv()) {
        if (s == "bvand" || s == "bvor" || s == "bvxor" ||
            s == "bvnand" || s == "bvnor" || s == "bvcomp" ||
            s == "bvadd" || s == "bvmul") {
            return true;
        }
    }

    // FloatingPoint
    if (logic_is_fp()) {
        if (s == "fp.add" || s == "fp.mul" || s == "fp.eq") {
            return true;
        }
    }

    return false;
}

bool flip_antisymm(const node *n, node ** const out_n)
{
    if (no_scramble) {
        return false;
    }

    if (!next_rand_int(2)) {
        return false;
    }

    // *n might be a qualified identifier of the form ('as' identifier sort)
    const std::string *symbol = &(n->symbol);
    if (*symbol == "as") {
        assert(n->children.size() > 0);
        symbol = &(n->children[0]->symbol);
    }
    const std::string &s = *symbol;
    assert(!s.empty());

    // arithmetic (IA, RA, IRA) (but not difference logic)
    if (logic_is_arith()) {
        if (s == "<") {
            *out_n = make_node(">");
            return true;
        } else if (s == ">") {
            *out_n = make_node("<");
            return true;
        } else if (s == "<=") {
            *out_n = make_node(">=");
            return true;
        } else if (s == ">=") {
            *out_n = make_node("<=");
            return true;
        }
    }

    // BitVectors
    if (logic_is_bv()) {
        if (s == "bvslt") {
            *out_n = make_node("bvsgt");
            return true;
        } else if (s == "bvsle") {
            *out_n = make_node("bvsge");
            return true;
        } else if (s == "bvult") {
            *out_n = make_node("bvugt");
            return true;
        } else if (s == "bvule") {
            *out_n = make_node("bvuge");
            return true;
        } else if (s == "bvsgt") {
            *out_n = make_node("bvslt");
            return true;
        } else if (s == "bvsge") {
            *out_n = make_node("bvsle");
            return true;
        } else if (s == "bvugt") {
            *out_n = make_node("bvult");
            return true;
        } else if (s == "bvuge") {
            *out_n = make_node("bvule");
            return true;
        }
    }

    // FloatingPoint
    if (logic_is_fp()) {
        if (s == "fp.leq") {
            *out_n = make_node("fp.geq");
            return true;
        } else if (s == "fp.lt") {
            *out_n = make_node("fp.gt");
            return true;
        } else if (s == "fp.geq") {
            *out_n = make_node("fp.leq");
            return true;
        } else if (s == "fp.gt") {
            *out_n = make_node("fp.lt");
            return true;
        }
    }

    return false;
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

/*
 * (scrambled) printing of benchmarks
 */

// a random permutation of name ids
std::vector<uint64_t> permuted_name_ids;

// uniform names
std::string make_name(uint64_t name_id)
{
    std::ostringstream tmp;
    tmp << "x" << name_id;
    return tmp.str();
}

// annotated assertions (for -generate_unsat_core_benchmark true)
std::string make_annotation_name()
{
    static uint64_t n = 1;
    std::ostringstream tmp;
    tmp << "a" << n;
    ++n;
    return tmp.str();
}

void print_node(std::ostream &out, const scrambler::node *n, bool keep_annotations)
{
    if (!no_scramble && !keep_annotations && n->symbol == "!") {
        print_node(out, n->children[0], keep_annotations);
    } else {
        if (n->needs_parens) {
            out << '(';
        }
        if (!n->symbol.empty()) {
            if (no_scramble || !n->is_name) {
                out << n->symbol;
            } else {
                uint64_t name_id = get_name_id(n->symbol.c_str());
                if (name_id == 0) {
                    out << n->symbol;
                } else {
                    assert(name_id < permuted_name_ids.size());
                    out << make_name(permuted_name_ids[name_id]);
                }
            }
        }
        std::string name;
        if (generate_unsat_core_benchmark && n->symbol == "assert") {
            name = make_annotation_name();
        }
        if (!name.empty()) {
            out << " (!";
        }
        for (size_t i = 0; i < n->children.size(); ++i) {
            if (i > 0 || !n->symbol.empty()) {
                out << ' ';
            }
            print_node(out, n->children[i], keep_annotations);
        }
        if (!name.empty()) {
            out << " :named " << name << ")";
        }
        if (n->needs_parens) {
            out << ')';
        }
        if (generate_unsat_core_benchmark && n->symbol == "check-sat") {
            // insert (get-unsat-core) after each check-sat
            out << std::endl << "(get-unsat-core)";
        }
    }
}

void print_command(std::ostream &out, const scrambler::node *n, bool keep_annotations)
{
    print_node(out, n, keep_annotations);
    out << std::endl;
}

void print_scrambled(std::ostream &out, bool keep_annotations)
{
    if (!no_scramble) {
        // identify consecutive declarations and shuffle them
        for (size_t i = 0; i < commands.size(); ) {
            if (commands[i]->symbol == "declare-fun") {
                size_t j = i+1;
                while (j < commands.size() &&
                       commands[j]->symbol == "declare-fun") {
                    ++j;
                }
                if (j - i > 1) {
                    shuffle_list(&commands, i, j);
                }
                i = j;
            } else {
                ++i;
            }
        }

        // identify consecutive assertions and shuffle them
        for (size_t i = 0; i < commands.size(); ) {
            if (commands[i]->symbol == "assert") {
                size_t j = i+1;
                while (j < commands.size() &&
                       commands[j]->symbol == "assert"){
                    ++j;
                }
                if (j - i > 1) {
                    shuffle_list(&commands, i, j);
                }
                i = j;
            } else {
                ++i;
            }
        }

        // Generate a random permutation of name ids. Note that index
        // 0 is unused in the permuted_name_ids vector (but present to
        // simplify indexing), and index next_name_id is out of range.
        size_t old_size = permuted_name_ids.size();
        assert(old_size <= next_name_id);
        // Since the print_scrambled function may be called multiple
        // times (for different parts of the benchmark), we only need
        // to permute those name ids that have been declared since the
        // last call to print_scrambled.
        if (old_size < next_name_id) {
            permuted_name_ids.reserve(next_name_id);
            for (size_t i = old_size; i < next_name_id; ++i) {
                permuted_name_ids.push_back(i);
                assert(permuted_name_ids[i] == i);
            }
            assert(permuted_name_ids.size() == next_name_id);
            // index 0 must not be shuffled
            if (old_size == 0) {
                old_size = 1;
            }
            // Knuth shuffle
            for (size_t i = old_size; i < next_name_id - 1; ++i) {
                size_t j = i + next_rand_int(next_name_id - i);
                std::swap(permuted_name_ids[i], permuted_name_ids[j]);
            }
        }
    }

    // print all commands
    for (size_t i = 0; i < commands.size(); ++i) {
        print_command(out, commands[i], keep_annotations);
        del_node(commands[i]);
    }
    commands.clear();
}

////////////////////////////////////////////////////////////////////////////////

/*
 * -core
 */

typedef std::tr1::unordered_set<std::string> StringSet;

bool parse_core(std::istream &src, StringSet &out)
{
    std::string name;
    src >> name;
    if (!src || name != "unsat") {
        return false;
    }
    // skip chars until a '(' is found
    char c;
    while (src.get(c) && c != '(') {
        if (!isspace(c)) {
            return false;
        }
    }
    if (!src) {
        return false;
    }
    bool done = false;
    while (src && !done) {
        src >> name;
        if (name.empty()) {
            return false;
        }
        if (name[name.size()-1] == ')') {
            name = name.substr(0, name.size()-1);
            done = true;
        }
        if (!name.empty()) {
            out.insert(name);
        }
    }

    std::vector<std::string> outnames(out.begin(), out.end());
    std::sort(outnames.begin(), outnames.end());

    std::cout << ";; parsed " << outnames.size() << " names:";
    for (size_t i = 0; i < outnames.size(); ++i) {
        std::cout << " " << outnames[i];
    }
    std::cout << std::endl;

    return true;
}

std::string get_named_annot(scrambler::node *root)
{
    std::vector<scrambler::node *> to_process;
    std::tr1::unordered_set<scrambler::node *> seen;

    to_process.push_back(root);
    while (!to_process.empty()) {
        scrambler::node *cur = to_process.back();
        to_process.pop_back();

        if (!seen.insert(cur).second) {
            continue;
        }
        if (cur->symbol == "!") {
            if (cur->children.size() >= 1) {
                to_process.push_back(cur->children[0]);
            }
            if (cur->children.size() >= 2) {
                for (size_t j = 1; j < cur->children.size(); ++j) {
                    scrambler::node *attr = cur->children[j];
                    if (attr->symbol == ":named" &&
                        !attr->children.empty()) {
                        return attr->children[0]->symbol;
                    }
                }
            }
        } else {
            for (size_t j = 0; j < cur->children.size(); ++j) {
                to_process.push_back(cur->children[j]);
            }
        }
    }

    return "";
}

void filter_named(const StringSet &to_keep)
{
    size_t i, k;
    for (i = k = 0; i < commands.size(); ++i) {
        scrambler::node *cur = commands[i];
        bool keep = true;
        if (cur->symbol == "assert") {
            std::string name = get_named_annot(cur);
            if (!name.empty() && to_keep.find(name) == to_keep.end()) {
                keep = false;
            }
        }
        if (keep) {
            commands[k++] = cur;
        }
    }
    commands.resize(k);
}

////////////////////////////////////////////////////////////////////////////////

char *c_strdup(const char *s)
{
    char *ret = (char *)malloc(strlen(s) + 1);
    if (ret == NULL) {
        exit(1);
    }

    strcpy(ret, s);
    return ret;
}

////////////////////////////////////////////////////////////////////////////////

void usage(const char *program)
{
    std::cout << "Syntax: " << program << " [OPTIONS] < INPUT_FILE.smt2\n"
              << "\n"
              << "    -term_annot [true|false]\n"
              << "        controls whether term annotations are printed (default: true)\n"
              << "\n"
              << "    -seed N\n"
              << "        seed value (>= 0) for pseudo-random choices; if 0, no scrambling is\n"
              << "        performed (default: time(0))\n"
              << "\n"
              << "    -core FILE\n"
              << "        print only those (named) assertions whose name is contained in the\n"
              << "        specified FILE (default: print all assertions)\n"
              << "\n"
              << "    -generate_unsat_core_benchmark [true|false]\n"
              << "        controls whether the output is in a format suitable for the unsat-core\n"
              << "        track of SMT-COMP (default: false)\n";
    std::cout.flush();
    exit(1);
}

////////////////////////////////////////////////////////////////////////////////

extern int yyparse();

using namespace scrambler;

int main(int argc, char **argv)
{
    bool keep_annotations = true;

    bool create_core = false;
    std::string core_file;

    set_seed(time(0));

    for (int i = 1; i < argc; ) {
        if (strcmp(argv[i], "-seed") == 0 && i+1 < argc) {
            std::istringstream s(argv[i+1]);
            int x;
            if (s >> x && x >= 0) {
                if (x > 0) {
                    set_seed(x);
                } else {
                    no_scramble = true;
                }
            } else {
                std::cerr << "Invalid value for -seed: " << argv[i+1] << std::endl;
                return 1;
            }
            i += 2;
        } else if (strcmp(argv[i], "-term_annot") == 0 && i+1 < argc) {
            if (strcmp(argv[i+1], "true") == 0) {
                keep_annotations = true;
            } else if (strcmp(argv[i+1], "false") == 0) {
                keep_annotations = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-core") == 0 && i+1 < argc) {
            create_core = true;
            core_file = argv[i+1];
            i += 2;
        } else if (strcmp(argv[i], "-generate_unsat_core_benchmark") == 0 && i+1 < argc) {
            if (strcmp(argv[i+1], "true") == 0) {
                generate_unsat_core_benchmark = true;
            } else if (strcmp(argv[i+1], "false") == 0) {
                generate_unsat_core_benchmark = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else {
            usage(argv[0]);
        }
    }

    StringSet core_names;
    if (create_core) {
        std::ifstream src(core_file.c_str());
        if (!parse_core(src, core_names)) {
            std::cerr << "ERROR parsing core names from " << core_file << std::endl;
            return 1;
        }
    }

    if (generate_unsat_core_benchmark) {
        // prepend SMT-LIB command that enables production of unsat cores
        std::cout << "(set-option :produce-unsat-cores true)" << std::endl;
    }

    while (!std::cin.eof()) {
        yyparse();
        if (!commands.empty() && commands.back()->symbol == "check-sat") {
            if (create_core) {
                filter_named(core_names);
            }
            assert(!commands.empty());
            print_scrambled(std::cout, keep_annotations);
        }
    }

    if (create_core) {
        filter_named(core_names);
    }
    if (!commands.empty()) {
        print_scrambled(std::cout, keep_annotations);
    }

    return 0;
}
