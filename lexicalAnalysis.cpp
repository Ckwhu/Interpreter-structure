#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,

  tok_VARIABLE = -2,
  tok_INTEGER = -3,
  tok_TEXT = -4,
  tok_ASSIGN_SYMBOL = -5,
  tok_FUNC = -6,
  tok_PRINT = -7,
  tok_RETURN = -8,
  tok_CONTINUE = -9,
  tok_IF = -10,
  tok_THEN = -11,
  tok_ELSE = -12,
  tok_FI = -13,
  tok_WHILE = -14,
  tok_DO = -15,
  tok_DONE = -16,
  tok_VAR = -17,

};

static std::string IdentifierStr; // Filled in if tok_identifier
static double NumVal;             // Filled in if tok_integer
static std::string StrVal;        // Filled in if tok_text

/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = getchar();

    // skip any comment.
  if (LastChar == '/') {
    if (LastChar = getchar() == '/') {
      while (LastChar != '\n')
        LastChar = getchar();
      gettok();
    }
  }

  if (LastChar == ':') {//assign_symbol
    std::string temp;
    temp = LastChar;
    LastChar = getchar();
    if (LastChar == '=') {
      LastChar = getchar();
      return tok_ASSIGN_SYMBOL;
    }
  }

  if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
    IdentifierStr = LastChar;
    while (isalnum((LastChar = getchar())))
      IdentifierStr += LastChar;

    if (IdentifierStr == "FUNC")
      return tok_FUNC;
    if (IdentifierStr == "PRINT")
      return tok_PRINT;
    if (IdentifierStr == "RETURN")
      return tok_RETURN;
    if (IdentifierStr == "CONTINUE")
      return tok_CONTINUE;
    if (IdentifierStr == "IF")
      return tok_IF;
    if (IdentifierStr == "THEN")
      return tok_THEN;
    if (IdentifierStr == "ELSE")
      return tok_ELSE;
    if (IdentifierStr == "FI")
      return tok_FI;
    if (IdentifierStr == "WHILE")
      return tok_WHILE;
    if (IdentifierStr == "DO")
      return tok_DO;
    if (IdentifierStr == "DONE")
      return tok_DONE;
    if (IdentifierStr == "VAR")
      return tok_VAR;
    return tok_VARIABLE;
  }

  if (isdigit(LastChar)) { // Number: [0-9]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar));

    NumVal = strtod(NumStr.c_str(), nullptr);
    return tok_INTEGER;
  }

  if (LastChar == '\"') {
    std::string textStr;
    LastChar=getchar();
    do {
      textStr += LastChar;
      LastChar = getchar();
    } while (LastChar != '\"');
    StrVal = textStr;
    LastChar=getchar();
    return tok_TEXT;
  }

  if (LastChar == '#') {
    // Comment until end of line.
    do
      LastChar = getchar();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF)
      return gettok();
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
}
int main() {
  int tok;
  while (1) {
    tok = gettok();
    printf("%d\n",tok);
  }
}
