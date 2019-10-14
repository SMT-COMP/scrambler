/* -*- fundamental -*-
 *
 * Flex-based lexical scanner for the SMT-LIB 2.6 command language
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
#include <iostream>
#include <vector>
#include "parser.h"


#define YY_INPUT(buf,result,max_size) \
  { \
    size_t howmany = 0; \
    char *which = buf; \
    char c; \
    while (howmany < max_size && std::cin.get(c)) { \
        *which = c; \
        ++which; \
        ++howmany; \
        if (c == ')') break; \
    } \
    result = howmany ? howmany : YY_NULL; \
 }

%}
%option noyywrap
%option stack

%x START_STRING
%x START_QUOTEDSYMBOL
%option yylineno

NUMERAL             [0-9]+
DECIMAL             [0-9]+\.[0-9]+
HEXADECIMAL         #x[0-9a-fA-F]+
BINARY              #b[0-1]+
SYMBOL              [a-zA-Z0-9._+\-*=%/?!$_~&^<>@]+
KEYWORD             :[a-zA-Z0-9._+\-*=%/?!$_~&^<>@]+

%%
";"[^\n]*\n      { ; }
\n               { ; }
\r               { ; }
[ \t]            { ; }

"("              |
")"              { return yytext[0]; }

"!"              { return TK_BANG; }
"_"              { return TK_UNDERSCORE; }
"as"             { return TK_AS; }
"exists"         { return TK_EXISTS; }
"forall"         { return TK_FORALL; }
"let"            { return TK_LET; }
"match"          { return TK_MATCH; }

"assert"         { return TK_ASSERT; }
"check-sat"      { return TK_CHECK_SAT; }
"declare-const"  { return TK_DECLARE_CONST; }
"declare-datatype"   { return TK_DECLARE_DATATYPE; }
"declare-datatypes"  { return TK_DECLARE_DATATYPES; }
"declare-fun"    { return TK_DECLARE_FUN; }
"declare-sort"   { return TK_DECLARE_SORT; }
"define-fun"     { return TK_DEFINE_FUN; }
"define-sort"    { return TK_DEFINE_SORT; }
"echo"           { return TK_ECHO; }
"exit"           { return TK_EXIT; }
"pop"            { return TK_POP; }
"push"           { return TK_PUSH; }
"reset"          { return TK_RESET; }
"set-info"       { return TK_SET_INFO; }
"set-logic"      { return TK_SET_LOGIC; }
"set-option"     { return TK_SET_OPTION; }
"get-unsat-core" { return TK_GET_UNSAT_CORE; }

":pattern"     { return TK_PATTERN; }
":named"       { return TK_NAMED; }

":qid"         { return TK_QID; }
":no-pattern"  { return TK_NOPATTERN; }
":skolemid"    { return TK_SKOLEMID; }
":lblpos"      { return TK_LBLPOS; }
":lblneg"      { return TK_LBLNEG; }
":weight"      { return TK_WEIGHT; }

{NUMERAL}      { yylval.string = c_strdup(yytext); return NUMERAL; }
{DECIMAL}      { yylval.string = c_strdup(yytext); return DECIMAL; }
{HEXADECIMAL}  { yylval.string = c_strdup(yytext); return HEXADECIMAL; }
{BINARY}       { yylval.string = c_strdup(yytext); return BINARY; }

{SYMBOL}       { yylval.string = c_strdup(yytext); return SYMBOL; }
{KEYWORD}      { yylval.string = c_strdup(yytext); return KEYWORD; }

\"              { yylval.buf = new std::vector<char>();
                  yylval.buf->push_back('"');
                  BEGIN(START_STRING); }
<START_STRING>{
  \"\"          { yylval.buf->push_back('"');
                  yylval.buf->push_back('"'); }
  [^\"]         { yylval.buf->push_back(yytext[0]); }
  \"            { yylval.buf->push_back('"');
                  yylval.buf->push_back('\0');
                  char *s = c_strdup(&(yylval.buf->front()));
                  delete yylval.buf;
                  yylval.buf = NULL;
                  yylval.string = s;
                  BEGIN(INITIAL); return STRING; }
}

\|              { yylval.buf = new std::vector<char>();
                  yylval.buf->push_back('|');
                  BEGIN(START_QUOTEDSYMBOL); }
<START_QUOTEDSYMBOL>{
  [^|]        { yylval.buf->push_back(yytext[0]); }
  \|          { yylval.buf->push_back('|');
                yylval.buf->push_back('\0');
                char *s = c_strdup(&(yylval.buf->front()));
                delete yylval.buf;
                yylval.buf = NULL;
                yylval.string = s;
                BEGIN(INITIAL); return SYMBOL; }
}

%%
