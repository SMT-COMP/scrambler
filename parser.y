/* -*- C++ -*-
 *
 * Bison parser for the SMT-LIB 2.6 command language
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

%{
#include "scrambler.h"
#include "parser.h"
#include "lexer.h"
#include <limits.h>
#include <assert.h>
#include <iostream>
#include <utility>

#define YYMAXDEPTH LONG_MAX
#define YYLTYPE_IS_TRIVIAL 1

void yyerror(const char *s);

using namespace scrambler;

%}

%locations
%debug
%verbose
%defines "parser.h"

%union {
    char *string;
    std::vector<scrambler::node *> *nodelist;
    scrambler::node *curnode;
    std::vector<char> *buf;
    std::pair<char *, scrambler::node *> *binding;
    std::vector< std::pair<char *, scrambler::node *> * > *bindinglist;
};


%token-table

%token <string> NUMERAL
%token <string> DECIMAL
%token <string> HEXADECIMAL
%token <string> BINARY
%token <string> SYMBOL
%token <string> KEYWORD
%token <string> STRING
%token TK_EOF

%token TK_BANG          "!"
%token TK_UNDERSCORE    "_"
%token TK_AS            "as"
%token TK_EXISTS        "exists"
%token TK_FORALL        "forall"
%token TK_LET           "let"
%token TK_MATCH         "match"

%token TK_ASSERT               "assert"
%token TK_CHECK_SAT            "check-sat"
%token TK_DECLARE_CONST        "declare-const"
%token TK_DECLARE_DATATYPE     "declare-datatype"
%token TK_DECLARE_DATATYPES    "declare-datatypes"
%token TK_DECLARE_FUN          "declare-fun"
%token TK_DECLARE_SORT         "declare-sort"
%token TK_DEFINE_FUN           "define-fun"
%token TK_DEFINE_SORT          "define-sort"
%token TK_ECHO                 "echo"
%token TK_EXIT                 "exit"
%token TK_POP                  "pop"
%token TK_PUSH                 "push"
%token TK_SET_INFO             "set-info"
%token TK_SET_LOGIC            "set-logic"

%token TK_PATTERN       ":pattern"
%token TK_NAMED         ":named"

%type <nodelist>    sort_dec_list
%type <curnode>     sort_dec
%type <nodelist>    datatype_dec_list
%type <curnode>     datatype_dec
%type <nodelist>    constructor_dec_list
%type <curnode>     constructor_dec
%type <nodelist>    selector_dec_list
%type <curnode>     selector_dec

%type <curnode>     spec_constant
%type <curnode>     generic_sexpr
%type <nodelist>    generic_sexpr_list

%type <curnode>     index
%type <nodelist>    index_list
%type <curnode>     identifier

%type <curnode>     a_term
%type <curnode>     qual_identifier
%type <nodelist>    term_list
%type <nodelist>    parallel_var_bindings
%type <bindinglist> var_bindings
%type <binding>     var_binding
%type <nodelist>    sorted_var_list
%type <curnode>     sorted_var
%type <nodelist>    match_case_list
%type <curnode>     match_case
%type <curnode>     pattern
%type <nodelist>    symbol_list

%type <curnode>     a_sort
%type <nodelist>    sort_list

%type <curnode>     attribute_value
%type <nodelist>    attribute_list
%type <curnode>     attribute

%destructor { free($$); } NUMERAL DECIMAL HEXADECIMAL BINARY SYMBOL KEYWORD STRING

%destructor { delete $$; } sort_dec_list
%destructor { delete $$; } sort_dec
%destructor { delete $$; } datatype_dec_list
%destructor { delete $$; } datatype_dec
%destructor { delete $$; } constructor_dec_list
%destructor { delete $$; } constructor_dec
%destructor { delete $$; } selector_dec_list
%destructor { delete $$; } selector_dec
%destructor { delete $$; } spec_constant
%destructor { delete $$; } generic_sexpr
%destructor { delete $$; } generic_sexpr_list
%destructor { delete $$; } index
%destructor { delete $$; } index_list
%destructor { delete $$; } identifier
%destructor { delete $$; } a_term
%destructor { delete $$; } qual_identifier
%destructor { delete $$; } term_list
%destructor { delete $$; } parallel_var_bindings
%destructor { delete $$; } var_bindings
%destructor { delete $$; } var_binding
%destructor { delete $$; } sorted_var_list
%destructor { delete $$; } sorted_var
%destructor { delete $$; } match_case_list
%destructor { delete $$; } match_case
%destructor { delete $$; } pattern
%destructor { delete $$; } symbol_list
%destructor { delete $$; } a_sort
%destructor { delete $$; } sort_list
%destructor { delete $$; } attribute_value
%destructor { delete $$; } attribute_list
%destructor { delete $$; } attribute

////////////////////////////////////////////////////////////////////////////////
// commands
////////////////////////////////////////////////////////////////////////////////

%start single_command

%%

single_command : command
  {
      YYACCEPT;
  }
;

command :
  cmd_assert
| cmd_check_sat
| cmd_declare_const
| cmd_declare_datatype
| cmd_declare_datatypes
| cmd_declare_fun
| cmd_declare_sort
| cmd_define_fun
| cmd_define_sort
| cmd_echo
| cmd_exit
| cmd_pop
| cmd_push
| cmd_set_logic
| cmd_set_info
| cmd_error
;

cmd_error :
  {
      YYERROR;
  }
;

cmd_assert :
  '(' TK_ASSERT a_term ')'
  {
      add_node("assert", $3);
  }
;

cmd_check_sat : '(' TK_CHECK_SAT ')'
  {
      add_node("check-sat");
  }
;

cmd_declare_const : '(' TK_DECLARE_CONST SYMBOL a_sort ')'
  {
      set_new_name($3);
      //add_node("declare-const", make_name_node($3), $4);
      add_node("declare-fun", make_name_node($3), make_node(), $4);
      free($3);
  }
;

// (declare-datatype s d) is an abbreviation of (declare-datatypes ((s 0)) (d))
// parametric datatypes are not allowed in SMT-COMP
cmd_declare_datatype : '(' TK_DECLARE_DATATYPE SYMBOL datatype_dec ')'
  {
      set_new_name($3);
      //add_node("declare-datatype", make_name_node($3), $4);
      std::vector<node *> sort_dec_list;
      sort_dec_list.push_back(make_name_node($3, make_node("0")));
      std::vector<node *> datatype_dec_list;
      datatype_dec_list.push_back($4);
      add_node("declare-datatypes", make_node(&sort_dec_list), make_node(&datatype_dec_list));
      free($3);
  }
;

cmd_declare_datatypes : '(' TK_DECLARE_DATATYPES '(' sort_dec_list ')' '(' datatype_dec_list ')' ')'
  {
      add_node("declare-datatypes", make_node($4), make_node($7));
      delete $7;
      delete $4;
  }
;

cmd_declare_fun :
  '(' TK_DECLARE_FUN SYMBOL '(' ')' a_sort ')'
  {
      set_new_name($3);
      add_node("declare-fun", make_name_node($3), make_node(), $6);
      free($3);
  }
| '(' TK_DECLARE_FUN SYMBOL '(' sort_list ')' a_sort ')'
  {
      set_new_name($3);
      add_node("declare-fun", make_name_node($3), make_node($5), $7);
      free($3);
  }
;

cmd_declare_sort : '(' TK_DECLARE_SORT SYMBOL NUMERAL ')'
  {
      if (atoi($4) != 0) {
          yyerror("declare-sort with arity != 0"); // not allowed in SMT-COMP
      }
      set_new_name($3);
      add_node("declare-sort", make_name_node($3), make_node($4));
      free($4);
      free($3);
  }
;

cmd_define_fun :
  '(' TK_DEFINE_FUN SYMBOL '(' ')' a_sort a_term ')'
  {
      set_new_name($3);
      add_node("define-fun", make_name_node($3), make_node(), $6, $7);
      free($3);
  }
| '(' TK_DEFINE_FUN SYMBOL '(' sorted_var_list ')' a_sort a_term ')'
  {
      set_new_name($3);
      add_node("define-fun", make_name_node($3), make_node($5), $7, $8);
      free($3);
      delete $5;
  }
;

cmd_define_sort :
  // only sort definitions with arity 0 are allowed in SMT-COMP
  '(' TK_DEFINE_SORT SYMBOL '(' ')' a_sort ')'
  {
      set_new_name($3);
      add_node("define-sort", make_name_node($3), make_node(), $6);
      free($3);
  }
;

cmd_echo : '(' TK_ECHO STRING ')'
  {
      //add_node("echo", make_node($3));
      free($3);
  }
;

cmd_exit : '(' TK_EXIT ')'
  {
      add_node("exit");
  }
;

cmd_pop : '(' TK_POP NUMERAL ')'
  {
      if (atoi($3) != 1) {
          yyerror("pop with numeral != 1"); // not allowed in SMT-COMP
      }
      add_node("pop", make_node($3));
      free($3);
  }
;

cmd_push : '(' TK_PUSH NUMERAL ')'
  {
      if (atoi($3) != 1) {
          yyerror("push with numeral != 1"); // not allowed in SMT-COMP
      }
      add_node("push", make_node($3));
      free($3);
  }
;

cmd_set_info :
  '(' TK_SET_INFO KEYWORD ')'
  {
      //add_node("set-info", make_node($3));
      free($3);
  }
| '(' TK_SET_INFO KEYWORD attribute_value ')'
  {
      //add_node("set-info", make_node($3), $4);
      /*//*/delete $4;
      free($3);
  }
;

cmd_set_logic : '(' TK_SET_LOGIC SYMBOL ')'
  {
      set_logic($3);
      add_node("set-logic", make_node($3));
      free($3);
  }
;

sort_dec_list :
  sort_dec
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| sort_dec_list sort_dec
  {
      $1->push_back($2);
      $$ = $1;
  }
;

sort_dec : '(' SYMBOL NUMERAL ')'
  {
      if (atoi($3) != 0) {
          yyerror("declare-datatypes contains a sort with arity != 0"); // not allowed in SMT-COMP
      }
      set_new_name($2);
      $$ = make_name_node($2, make_node($3));
      free($3);
      free($2);
  }
;

datatype_dec_list :
  datatype_dec
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| datatype_dec_list datatype_dec
  {
      $1->push_back($2);
      $$ = $1;
  }
;

datatype_dec :  // only non-parametric datatypes are allowed in SMT-COMP
  '(' constructor_dec_list ')'
  {
      shuffle_list($2);
      $$ = make_node($2);
      delete $2;
  }

constructor_dec_list :
  constructor_dec
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| constructor_dec_list constructor_dec
  {
      $1->push_back($2);
      $$ = $1;
  }
;

constructor_dec :
  '(' SYMBOL ')'
  {
      set_new_name($2);
      $$ = make_name_node($2);
      $$->set_parens_needed(true);
      free($2);
  }
| '(' SYMBOL selector_dec_list ')'
  {
      set_new_name($2);
      $$ = make_name_node($2);
      $$->add_children($3);
      $$->set_parens_needed(true);
      delete $3;
      free($2);
  }
;

selector_dec_list :
  selector_dec
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| selector_dec_list selector_dec
  {
      $1->push_back($2);
      $$ = $1;
  }
;

selector_dec : '(' SYMBOL a_sort ')'
  {
      set_new_name($2);
      $$ = make_name_node($2, $3);
      free($2);
  }
;

////////////////////////////////////////////////////////////////////////////////
// terms
////////////////////////////////////////////////////////////////////////////////

a_term :
  spec_constant
  {
      $$ = $1;
  }
| qual_identifier
  {
      $$ = $1;
  }
| '(' qual_identifier term_list ')'
  {
      node *n = $2;
      if (is_commutative($2)) {
          shuffle_list($3);
      } else if (flip_antisymm($2, &n)) {
          std::swap((*($3))[0], (*($3))[1]);
      }
      $$ = make_node(n, $3);
      if (n != $2) {
          del_node($2);
      }
      delete $3;
  }
| '(' TK_LET '(' parallel_var_bindings ')' a_term ')'
  {
      shuffle_list($4);
      $$ = make_node("let", make_node($4), $6);
      delete $4;
  }
| '(' TK_FORALL '(' sorted_var_list ')' a_term ')'
  {
      //shuffle_list($4); DO NOT shuffle as this might affect shadowing
      $$ = make_node("forall", make_node($4), $6);
      delete $4;
  }
| '(' TK_EXISTS '(' sorted_var_list ')' a_term ')'
  {
      //shuffle_list($4); DO NOT shuffle as this might affect shadowing
      $$ = make_node("exists", make_node($4), $6);
      delete $4;
  }
| '(' TK_MATCH a_term '(' match_case_list ')' ')'
  {
      $$ = make_node("match", $3, make_node($5));
      delete $5;
  }
| '(' TK_BANG a_term attribute_list ')'
  {
      $$ = make_node("!", $3);
      $$->add_children($4);
      delete $4;
  }
;

qual_identifier :
  identifier
  {
      $$ = $1;
  }
| '(' TK_AS identifier a_sort ')'
  {
      $$ = make_node("as", $3, $4);
  }
;

term_list :
  a_term
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| term_list a_term
  {
      $1->push_back($2);
      $$ = $1;
  }
;

parallel_var_bindings : var_bindings
  {
      $$ = new std::vector<node *>();
      for (std::vector<std::pair<char *, node *> *>::iterator it = $1->begin(); it != $1->end(); ++it) {
          set_new_name((*it)->first);
          $$->push_back(make_name_node((*it)->first, (*it)->second));
          free((*it)->first);
          delete *it;
      }
      delete $1;
  }
;

var_bindings :
  var_binding
  {
      $$ = new std::vector<std::pair<char *, node *> *>();
      $$->push_back($1);
  }
| var_bindings var_binding
  {
      $$ = $1;
      $$->push_back($2);
  }
;

var_binding : '(' SYMBOL a_term ')'
  {
      $$ = new std::pair<char *, node *>($2, $3);
  }
;

sorted_var_list :
  sorted_var
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| sorted_var_list sorted_var
  {
      $$ = $1;
      $$->push_back($2);
  }
;

sorted_var : '(' SYMBOL a_sort ')'
  {
      set_new_name($2);
      $$ = make_name_node($2, $3);
  }
;

match_case_list :
  match_case
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| match_case_list match_case
  {
      $$ = $1;
      $$->push_back($2);
  }
;

match_case : '(' pattern a_term ')'
  {
      $$ = make_node(NULL, $2, $3);
  }
;

pattern :
  SYMBOL
  {
      set_new_name($1);
      $$ = make_name_node($1);
      free($1);
  }
| '(' SYMBOL symbol_list ')'
  {
      set_new_name($2);
      $$ = make_name_node($2);
      $$->add_children($3);
      $$->set_parens_needed(true);
      delete $3;
      free($2);
  }
;

symbol_list :
  SYMBOL
  {
      $$ = new std::vector<node *>();
      set_new_name($1);
      $$->push_back(make_name_node($1));
      free($1);
  }
| symbol_list SYMBOL
  {
      $$ = $1;
      set_new_name($2);
      $$->push_back(make_name_node($2));
      free($2);
  }
;

////////////////////////////////////////////////////////////////////////////////
// sorts
////////////////////////////////////////////////////////////////////////////////

a_sort :
  identifier
  {
      $$ = $1;
  }
| '(' identifier sort_list ')'
  {
      $$ = make_node($2, $3);
      delete $3;
  }
;

sort_list :
  a_sort
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| sort_list a_sort
  {
      $$ = $1;
      $$->push_back($2);
  }
;

////////////////////////////////////////////////////////////////////////////////
// attributes
////////////////////////////////////////////////////////////////////////////////

attribute_value:
  spec_constant
  {
      $$ = $1;
  }
| SYMBOL
  {
      $$ = make_node($1);
      free($1);
  }
| '(' ')'
  {
      $$ = make_node();
  }
| '(' generic_sexpr_list ')'
  {
      $$ = make_node($2);
      delete $2;
  }
;

attribute_list :
  attribute
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| attribute_list attribute
  {
      $$ = $1;
      $$->push_back($2);
  }
;

// the only predefined term attributes in SMT-LIB are ':named' and
// ':pattern'
attribute :
  TK_NAMED SYMBOL
  {
      // :named terms are not allowed in SMT-COMP; we need to be able
      // to parse :named assertions for the unsat-core track only.
      // Otherwise, make_name_node($2) might be more appropriate here.
      $$ = make_node(":named", make_node($2));
      $$->set_parens_needed(false);
      free($2);
  }
| TK_PATTERN '(' term_list ')'
  {
      $$ = make_node(":pattern", make_node($3));
      $$->set_parens_needed(false);
      delete $3;
  }
;

////////////////////////////////////////////////////////////////////////////////
// identifiers
////////////////////////////////////////////////////////////////////////////////

index :
  NUMERAL
  {
      $$ = make_node($1);
      free($1);
  }
| SYMBOL
  {
      $$ = make_name_node($1);
      free($1);
  }
;

index_list :
  index
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| index_list index
  {
      $$ = $1;
      $$->push_back($2);
  }
;

identifier :
  SYMBOL
  {
      $$ = make_name_node($1);
      free($1);
  }
| '(' TK_UNDERSCORE SYMBOL index_list ')'
  {
      // Since indexed identifiers cannot be declared in a benchmark
      // (but $3 alone could be declared independently), we do not
      // want $3 to be renamed. Example: '(_ is c)' is a tester term
      // for datatype values (where 'is' must not be renamed), but the
      // benchmark might independently declare a (non-indexed)
      // function 'is'. Hence we are *not* using make_name_node($3)
      // here.
      $$ = make_node("_", make_node($3));
      $$->add_children($4);
      delete $4;
      free($3);
  }
;

////////////////////////////////////////////////////////////////////////////////
// s-expressions
////////////////////////////////////////////////////////////////////////////////

spec_constant:
  NUMERAL
  {
      $$ = make_node($1);
      free($1);
  }
| DECIMAL
  {
      $$ = make_node($1);
      free($1);
  }
| HEXADECIMAL
  {
      $$ = make_node($1);
      free($1);
  }
| BINARY
  {
      $$ = make_node($1);
      free($1);
  }
| STRING
  {
      $$ = make_node($1);
      free($1);
  }
;

generic_sexpr :
  spec_constant
  {
      $$ = $1;
  }
| SYMBOL
  {
      $$ = make_node($1);
      free($1);
  }
| KEYWORD
  {
      $$ = make_node($1);
      free($1);
  }
| '(' ')'
  {
      $$ = make_node();
  }
| '(' generic_sexpr_list ')'
  {
      $$ = make_node($2);
      delete $2;
  }
;

generic_sexpr_list :
  generic_sexpr
  {
      $$ = new std::vector<node *>();
      $$->push_back($1);
  }
| generic_sexpr_list generic_sexpr
  {
      $$ = $1;
      $$->push_back($2);
  }
;

////////////////////////////////////////////////////////////////////////////////

%%

void yyerror(const char *s)
{
    std::cerr << "ERROR: " << s << std::endl;
    exit(1);
}
