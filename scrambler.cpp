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

namespace scrambler {

namespace {

bool no_scramble = false;

/*
 * If set to true the following modifications will be made additionally:
 * 1. The following command will be prepended:
 *    (set-option :produce-unsat-cores true)
 * 2. A (get-unsat-core) command will be inserted after each (check-sat) command.
 * 3. Each (assert fmla) will be replaced by (assert (! fmla :named freshId))
 *    where freshId is some fresh identifier.
 */
bool generate_unsat_core_benchmark = false;

typedef std::tr1::unordered_map<std::string, std::string> NameMap;
NameMap names;

NameMap permuted_names;

std::stack<NameMap*> shadow_undos;

std::string make_name(int n)
{
    std::ostringstream tmp;
    tmp << "x" << n;
    return tmp.str();
}

std::vector<int> scopes;

std::vector<node *> commands;

uint64_t seed;
const uint64_t a = 25214903917ULL;
const uint64_t c = 11U;
const uint64_t mask = ~(2ULL << 48);


const char *unquote(const char *n)
{
    if (no_scramble || !n[0] || n[0] != '|') {
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


size_t next_rand_int(size_t upper_bound)
{
    seed = ((seed * a) + c) & mask;
    return (size_t)(seed >> 16U) % upper_bound;
}

std::string get_name(const char *n)
{
    std::string sn(unquote(n));
    NameMap::iterator it = names.find(sn);
    if (it != names.end()) {
        return it->second;
    } else {
        return sn;
    }
}


int logic_dl = -1;
bool logic_is_dl()
{
    if (logic_dl == -1) {
        if (commands.size() > 0 && commands[0]->symbol == "set-logic") {
            std::string &logic = commands[0]->children[0]->symbol;
            logic_dl = (logic == "QF_IDL" ||
                        logic == "QF_RDL" ||
                        logic == "QF_UFIDL" ||
                        logic == "UFIDL") ? 1 : 0;
        }
    }
    return logic_dl == 1;
}


} // namespace


int name_idx = 1;

void set_new_name(const char *n)
{
    n = unquote(n);

    if (shadow_undos.empty())
      {
        if (names.count(n) > 0)
          {
            std::cerr << "ERROR duplicate name declaration at top-level: " << n << std::endl;
            exit(1);
          }
      }
    else
      {
        // store current name (for later namespace pop)
        NameMap *shadow_undo = shadow_undos.top();
        if (shadow_undo->count(n) > 0)
          {
            std::cerr << "ERROR duplicate name declaration: " << n << std::endl;
            exit(1);
          }
        (*shadow_undo)[n] = names[n];  // empty string if no current name
      }

    if (no_scramble) {
        names[n] = n;
    } else {
        names[n] = make_name(name_idx++);
    }
}


void push_namespace()
{
    shadow_undos.push(new NameMap());
    scopes.push_back(name_idx);
}


void pop_namespace()
{
    if (scopes.empty()) {
        std::cerr << "ERROR pop command over an empty stack" << std::endl;
        exit(1);
    }

    assert(!shadow_undos.empty());
    NameMap *shadow_undo = shadow_undos.top();
    for (NameMap::iterator it = shadow_undo->begin(); it != shadow_undo->end(); ++it)
      {
        if (it->second.empty())
          {
            names.erase(it->first);
          }
        else
          {
            names[it->first] = it->second;
          }
      }
    shadow_undos.pop();
    delete shadow_undo;

    name_idx = scopes.back();
    scopes.pop_back();
}


void add_node(const char *s, node *n1, node *n2, node *n3, node *n4)
{
    node *ret = new node;
    ret->symbol = get_name(s);
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
        ret->symbol = get_name(s);
    }
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


void del_node(node *n)
{
    for (size_t i = 0; i < n->children.size(); ++i) {
        del_node(n->children[i]);
    }
    delete n;
}


void node::add_children(std::vector<node *> *c)
{
    children.insert(children.end(), c->begin(), c->end());
}


node *make_node(std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->children.assign(v->begin(), v->end());
    return ret;
}


node *make_node(node *n, std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->children.push_back(n);
    ret->children.insert(ret->children.end(), v->begin(), v->end());
    return ret;
}


void set_seed(int s)
{
    seed = s;
}


void shuffle_list(std::vector<node *> *v, size_t start, size_t end)
{
    if (!no_scramble) {
        size_t n = end - start;
        for (size_t i = n-1; i > 0; --i) {
            std::swap((*v)[i+start], (*v)[next_rand_int(i+1)+start]);
        }
    }
}


void shuffle_list(std::vector<node *> *v)
{
    shuffle_list(v, 0, v->size());
}


bool is_commutative(node *n)
{
    std::string *curs = &(n->symbol);
    if (curs->empty() && !n->children.empty()) {
        curs = &(n->children[0]->symbol);
    }
    std::string &s = *curs;
    if (s == "and" || s == "or" || s == "xor" || s == "distinct") {
        return true;
    }
    if (!logic_is_dl()) {
        if (s == "*" || s == "+" || s == "=") {
            return true;
        }
        if (s == "bvand" || s == "bvor" || s == "bvxor" ||
            s == "bvnand" || s == "bvnor" || s == "bvcomp" ||
            s == "bvadd" || s == "bvmul") {
            return true;
        }
    }
    return false;
}


bool flip_antisymm(node *n, node **out_n)
{
    if (no_scramble) {
        return false;
    }

    if (!next_rand_int(2)) {
        return false;
    }

    std::string *curs = &(n->symbol);
    if (curs->empty() && !n->children.empty()) {
        curs = &(n->children[0]->symbol);
    }
    std::string &s = *curs;
    if (!logic_is_dl()) {
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
        } else if (s == "bvslt") {
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
    return false;
}


namespace {

std::string make_annot_name(int n)
{
    std::ostringstream tmp;
    tmp << "y" << n;
    return tmp.str();
}

typedef std::tr1::unordered_set<std::string> StringSet;

std::string get_named_annot(node *root)
{
    std::vector<node *> to_process;
    std::tr1::unordered_set<node *> seen;

    to_process.push_back(root);
    while (!to_process.empty()) {
        node *cur = to_process.back();
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
                    node *attr = cur->children[j];
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


void print_node(std::ostream &out, node *n, bool keep_annotations)
{
    if (!no_scramble && !keep_annotations && n->symbol == "!") {
        print_node(out, n->children[0], keep_annotations);
    } else {
        if (n->needs_parens) {
            out << '(';
        }
        if (!n->symbol.empty()) {
            NameMap::iterator it = permuted_names.find(n->symbol);
            if (it != permuted_names.end()) {
                out << it->second;
            } else {
                out << n->symbol;
            }
        }
        std::string name;
        if (generate_unsat_core_benchmark && n->symbol == "assert") {
            name = make_annot_name(name_idx++);
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
            // append get-unsat-core after check-sat
            out << std::endl << "(get-unsat-core)";
        }
    }
}


void print_command(std::ostream &out, node *n, bool keep_annotations)
{
    print_node(out, n, keep_annotations);
    out << std::endl;
}


void print_scrambled(std::ostream &out, bool keep_annotations)
{
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
            while (j < commands.size() && commands[j]->symbol == "assert"){
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

    // This randomly permutes the top-level names only. A better
    // implementation would permute all names, including those in
    // local scopes (e.g., bound by a "let").

    // Also, this has not been tested together with advanced scrambler
    // features (e.g., named annotations, incremental benchmarks).

    // generate random name permutation, aka Knuth shuffle (note that
    // index 0 is unused, and index name_idx is out of range)
    int permutation[name_idx];
    for (int i=1; i<name_idx; ++i) {
        int j = 1 + next_rand_int(i);
        permutation[i] = permutation[j];
        permutation[j] = i;
    }
    for (int i=1; i<name_idx; ++i) {
      permuted_names[make_name(i)] = make_name(permutation[i]);
    }

    for (size_t i = 0; i < commands.size(); ++i) {
        print_command(out, commands[i], keep_annotations);
        del_node(commands[i]);
    }
    commands.clear();
}


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


void filter_named(const StringSet &to_keep)
{
    size_t i, k;
    for (i = k = 0; i < commands.size(); ++i) {
        node *cur = commands[i];
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


bool parse_names(std::istream &src, StringSet &out)
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

} // namespace

} // namespace scrambler

char *c_strdup(const char *s)
{
    char *ret = (char *)malloc(strlen(s) + 1);
    strcpy(ret, s);
    return ret;
}


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
                std::cerr << "Invalid value for -seed: " << argv[i+1]
                          << std::endl;
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

    StringSet names;
    if (create_core) {
        std::ifstream src(core_file.c_str());
        if (!parse_names(src, names)) {
            std::cout << "ERROR in parsing core names from " << core_file
                      << std::endl;
            return 1;
        }
    }

    if (generate_unsat_core_benchmark) {
        // prepend command that enables production of unsat cores
        std::cout << "(set-option :produce-unsat-cores true)" << std::endl;
    }

    while (!std::cin.eof()) {
        yyparse();
        if (!commands.empty() && commands.back()->symbol == "check-sat") {
            if (create_core) {
                filter_named(names);
            }
            print_scrambled(std::cout, keep_annotations);
        }
    }

    if (create_core) {
        filter_named(names);
    }
    if (!commands.empty()) {
        print_scrambled(std::cout, keep_annotations);
    }

    return 0;
}
