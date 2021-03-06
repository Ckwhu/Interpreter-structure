#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <stdio.h>
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

  if (LastChar == ':') { // assign_symbol
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
    LastChar = getchar();
    do {
      textStr += LastChar;
      LastChar = getchar();
    } while (LastChar != '\"');
    StrVal = textStr;
    LastChar = getchar();
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

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

namespace {

/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() = default;
  virtual void print()=0;
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double Val) : Val(Val) {}
  void print() { std::cout << "解析到数值，数值为：" << Val << "\n"; }
};



/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(const std::string &Name) : Name(Name) {}
  const std::string &getName() const { return Name; }
  void print() { std::cout << "解析到变量，变量名为：" << Name << "\n"; }
};

/// TextExprAST -Expression class for text literals
class TextExprAST : public ExprAST {
  std::string Str;

public:
  TextExprAST(std::string s) : Str(s) {}
  void print() { std::cout << "解析到字符串，字符串为：" << Str << "\n"; }
};

/// VarExprAST - Expression class for var/in
class VarExprAST : public ExprAST {
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
  std::unique_ptr<ExprAST> Body;

public:
  VarExprAST(
      std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames,
      std::unique_ptr<ExprAST> Body)
      : VarNames(std::move(VarNames)), Body(std::move(Body)) {}
  void print() { std::cout << "解析到变量定义"<<"\n"; }
};

/// AssignVariableExprAST statement expression class for referencing assignment
/// ,like a:=100
// class AssignVariableExprAST : public ExprAST {
//  std::string Name;
//  ExprAST *expr;
//
//  public:
//  AssignVariableExprAST(const std::string &Name, ExprAST
//  *expr):Name(Name),expr(expr){};
//};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
  void print() {
    std::cout << "解析二元表达式,左部为：";
    LHS->print();
    std::cout << "\n"<<"运算符为"<<Op<<"\n";
    std::cout << "右部为：";
    RHS->print();
    std::cout << "\n";
  }
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}
  void print() {
    std::cout << "解析到调用,调用名为：" << Callee;
    std::cout << "参数为：";
    for (int i = 0; i < Args.size(); i++) {
      Args[i]->print();
    }
  }
};

/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, Then, Else;

public:
  IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
            std::unique_ptr<ExprAST> Else)
      : Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}
  void print() {
    std::cout << "解析到if语句,条件为：";
    Cond->print();
    std::cout << "Then语句为：";
    Then->print();
    std::cout << "Else语句为：";
    Else->print();
  }
};

/// whileExprAST - Expression class for while
class WhileExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, DO;

public:
  WhileExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> DO)
      : Cond(std::move(Cond)), DO(std::move(DO)) {}
  void print() { std::cout << "解析到while语句，条件为："; 
  Cond->print();
    std::cout << "DO为：";
  DO->print();
  }
};

/// PrintExprAST
class PrintExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> printConts;

public:
  PrintExprAST(std::vector<std::unique_ptr<ExprAST>> printConts)
      : printConts(std::move(printConts)) {}
  void print() { std::cout << "解析到print语句，打印的内容为：";
    for (int i = 0; i < printConts.size(); i++) {
      printConts[i]->print();
    }
  }
};

/// ReturnExprAST
class ReturnExprAST : public ExprAST {
  std::unique_ptr<ExprAST> returnCont;

public:
  ReturnExprAST(std::unique_ptr<ExprAST> returnCont)
      : returnCont(std::move(returnCont)) {}
  void print() {
    std::cout << "解析到return语句，打印的内容为：";
    returnCont->print();
  }
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;

public:
  PrototypeAST(const std::string &Name, std::vector<std::string> Args)
      : Name(Name), Args(std::move(Args)) {}

  const std::string &getName() const { return Name; }
  void print() {
    std::cout << "解析到函数原型,函数名为：" << Name << "参数列表为:";
    for (int i = 0; i < Args.size(); i++) {
      std::cout << Args[i] << " ";
    }
    std::cout << "\n";
  }
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}
  void print() { std::cout << "解析到函数，函数原型为：";
    Proto->print();
    std::cout << "函数体为：";
    Body->print();
    std::cout << "\n";
  }
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() { return CurTok = gettok(); }

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
  fprintf(stderr, "Error: %s\n", Str);
  return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
  LogError(Str);
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto Result = llvm::make_unique<NumberExprAST>(NumVal);
  getNextToken(); // consume the number
  //Result->print();
  return std::move(Result);
}

/// textexpr ::=text
static std::unique_ptr<ExprAST> ParseTextExpr() {
  auto TextResult = llvm::make_unique<TextExprAST>(StrVal);
  getNextToken();
  TextResult->print();
  return std::move(TextResult);
}

/// var a,b,c
static std::unique_ptr<ExprAST> ParseVarExpr() {
  getNextToken(); // eat the var.

  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;

  // At least one variable name is required.
  if (CurTok != tok_VARIABLE)
    return LogError("expected identifier after var");

  while (true) {
    std::string Name = IdentifierStr;
    getNextToken(); // eat identifier.

    // Read the optional initializer.
    std::unique_ptr<ExprAST> Init = nullptr;
    if (CurTok == tok_ASSIGN_SYMBOL) {
      getNextToken(); // eat the '：='.
      Init = ParseExpression();
      if (!Init)
        return nullptr;
    }

    VarNames.push_back(std::make_pair(Name, std::move(Init)));

    // End of var list, exit loop.
    if (CurTok != ',')
      break;
    getNextToken(); // eat the ','.

    if (CurTok != tok_VARIABLE)
      return LogError("expected identifier list after var");
  }

  // At this point, we have to have 'in'.
  // if (CurTok != tok_in)
  // return LogError("expected 'in' keyword after 'var'");
  // getNextToken(); // eat 'in'.

  // auto Body = ParseExpression();
  // if (!Body)
  //  return nullptr;
  auto Body = nullptr;
  //std::cout << "解析到变量定义";
  llvm::make_unique<VarExprAST>(std::move(VarNames), std::move(Body))->print();
  return llvm::make_unique<VarExprAST>(std::move(VarNames), std::move(Body));
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); // eat (.
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken(); // eat ).
  return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;

  getNextToken(); // eat identifier.

  // Parse assignment_statement	: VARIABLE ASSIGN_SYMBOL expression
  // if (CurTok == tok_ASSIGN_SYMBOL) {
  //  getNextToken(); // eat  tok_ASSIGN_SYMBOL
  //  return llvm::make_unique<AssignVariableExprAST>(IdName,ParseExpression());
  //}

  if (CurTok != '(') // Simple variable ref.
  {
    //std::cout << "解析到变量" << IdName << "\n";
    return llvm::make_unique<VariableExprAST>(IdName);
  }

  // Call.
  getNextToken(); // eat (
  std::vector<std::unique_ptr<ExprAST>> Args;
  if (CurTok != ')') {
    while (true) {
      if (auto Arg = ParseExpression())
        Args.push_back(std::move(Arg));
      else
        return nullptr;

      if (CurTok == ')')
        break;

      if (CurTok != ',')
        return LogError("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }
  // Eat the ')'.
  getNextToken();

  return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}


/// ifexpr ::= 'if' expression 'then' expression 'else' expression
 static std::unique_ptr<ExprAST> ParseIfExpr() {
  getNextToken(); // eat the if.

  // condition.
  auto Cond = ParseExpression();
  if (!Cond)
    return nullptr;

  if (CurTok != tok_THEN)
    return LogError("expected then");
  getNextToken(); // eat the then

  auto Then = ParseExpression();
  if (!Then)
    return nullptr;

  if ((CurTok != tok_ELSE) && (CurTok != tok_FI))
    return LogError("expected else or fi");

  if (CurTok == tok_FI) {
    getNextToken();
    return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
                                        std::move(nullptr));
  }

  getNextToken();

  auto Else = ParseExpression();
  if (!Else)
    return nullptr;

  if (CurTok == tok_FI) {
    llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
                                 std::move(Else))
        ->print();
    return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
                                        std::move(Else));
  }
   
  else
    return LogError("expected fi");
}

/// while_statement	: WHILE expression DO statement DONE
 static std::unique_ptr<ExprAST> ParseWhileExpr() {
  getNextToken(); // eat the while.

  // condition.
  auto Cond = ParseExpression();
  if (!Cond)
    return nullptr;

  if (CurTok != tok_DO)
    return LogError("expected DO");
  getNextToken(); // eat the DO

  auto Do = ParseExpression();//这里可能会出问题，表达式可能没有被完全解析
  if (!Do)
    return nullptr;

  if (CurTok != tok_DONE)
    return LogError("expected DONE");

  llvm::make_unique<WhileExprAST>(std::move(Cond), std::move(Do))->print();
  return llvm::make_unique<WhileExprAST>(std::move(Cond), std::move(Do));
}

/// print_item	: expression| TEXT
 static std::unique_ptr<ExprAST> ParsePrintExpr() {
  getNextToken(); // eat print
  std::vector<std::unique_ptr<ExprAST>> printConts;
  auto printCont = ParseExpression();
  printConts.push_back(std::move(printCont));
  while (CurTok == ',') {
    getNextToken(); // eat ,
       auto printCont = ParseExpression();
       printConts.push_back(std::move(printCont));
     }
  llvm::make_unique<PrintExprAST>(std::move(printConts))->print();
  return llvm::make_unique<PrintExprAST>(std::move(printConts));
};

/// return_statement: RETURN expression
 static std::unique_ptr<ExprAST> ParseReturnExpr() {
  getNextToken(); // eat print
  auto returnCont = ParseExpression();
  llvm::make_unique<ReturnExprAST>(std::move(returnCont))->print();
  return llvm::make_unique<ReturnExprAST>(std::move(returnCont));
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
  switch (CurTok) {
  default:
    return LogError("unknown token when expecting an expression");
  case tok_VARIABLE:
    return ParseIdentifierExpr();
  case tok_INTEGER:
    return ParseNumberExpr();
  case tok_TEXT:
    return ParseTextExpr();
  case tok_VAR:
    return ParseVarExpr();
  case tok_CONTINUE:
    //这个还不知道怎么写
  case tok_IF:
    return ParseIfExpr();
  case tok_WHILE:
    return ParseWhileExpr();
  case tok_PRINT:
    return ParsePrintExpr();
  case tok_RETURN:
    return ParseReturnExpr();
  case '(':
    return ParseParenExpr();
  }
}

/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                              std::unique_ptr<ExprAST> LHS) {
  // If this is a binop, find its precedence.
  while (true) {
    int TokPrec = GetTokPrecedence();

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec) {
      //LHS->print();
      return LHS;
    }

    // Okay, we know this is a binop.
    int BinOp = CurTok;
    getNextToken(); // eat binop

    // Parse the primary expression after the binary operator.
    auto RHS = ParsePrimary();
    if (!RHS)
      return nullptr;

    // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
      if (!RHS)
        return nullptr;
    }

    // Merge LHS/RHS.
    LHS =
        llvm::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
    LHS->print();
  }
}

/// expression
///   ::= primary binoprhs
///
static std::unique_ptr<ExprAST> ParseExpression() {
  auto LHS = ParsePrimary();
  if (!LHS)
    return nullptr;
  return ParseBinOpRHS(0, std::move(LHS));
}

/// statement
static std::unique_ptr<ExprAST> ParseStatement() {}

/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_VARIABLE)
    return LogErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  getNextToken();

  if (CurTok != '(')
    return LogErrorP("Expected '(' in prototype");

  std::vector<std::string> ArgNames;
  while (true) {
    CurTok = getNextToken();
    if (CurTok == tok_VARIABLE)
      ArgNames.push_back(IdentifierStr);
    else if (CurTok == 44)
      continue;
    else
      break;
  }

  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  // success.
  getNextToken(); // eat ')'.

 /* std::cout << "parsing FUNC";
  std::cout << "FUNC name is:" << FnName << " ";
  std::cout << "parameter list is:";
  for (int i = 0; i < ArgNames.size(); i++)
    std::cout << ArgNames[i] << " ";*/

  return llvm::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

/// definition ::= 'FUNC' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken(); // eat FUNC.
  auto Proto = ParsePrototype();
  if (!Proto)
    return nullptr;
  getNextToken(); // eat'{'.
  if (auto E = ParseExpression()) {
    llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E))->print();
    return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
   
  return nullptr;
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  if (auto E = ParseExpression()) {
    // Make an anonymous proto.
    auto Proto = llvm::make_unique<PrototypeAST>("__anon_expr",
                                                 std::vector<std::string>());
    return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing
//===----------------------------------------------------------------------===//

static void HandleDefinition() {
  if (ParseDefinition()) {
    fprintf(stderr, "Parsed a function definition.\n");
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (ParseTopLevelExpr()) {
    fprintf(stderr, "Parsed a top-level expr\n");
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
  while (true) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case ';': // ignore top-level semicolons.
      getNextToken();
      break;
    case tok_FUNC:
      HandleDefinition();
      break;
    default:
      HandleTopLevelExpression();
      break;
    }
  }
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40; // highest.

  // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextToken();

  // Run the main "interpreter loop" now.
  MainLoop();

  return 0;
}
