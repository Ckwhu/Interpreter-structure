#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Utils.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <initializer_list>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::orc;
using namespace llvm::sys;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,
  // primary
  tok_VARIABLE = -2,
  tok_INTEGER = -3,
  tok_TEXT = -4,
  tok_ASSIGN_SYMBOL = -5,
  // command
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
static double NumVal;             // Filled in if tok_number
static std::string StrVal;        // Filled in if tok_text

// debug
namespace {
class PrototypeAST;
class ExprAST;
} // namespace

struct DebugInfo {
  DICompileUnit *TheCU;
  DIType *DblTy;
  std::vector<DIScope *> LexicalBlocks;

  void emitLocation(ExprAST *AST);
  DIType *getDoubleTy();
} KSDbgInfo;

struct SourceLocation {
  int Line;
  int Col;
};
static SourceLocation CurLoc;
static SourceLocation LexLoc = {1, 0};

static int advance() {
  int LastChar = getchar();

  if (LastChar == '\n' || LastChar == '\r') {
    LexLoc.Line++;
    LexLoc.Col = 0;
  } else
    LexLoc.Col++;
  return LastChar;
}

/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = advance();

  // skip any comment.
  if (LastChar == '/') {
    if (LastChar = advance() == '/') {
      do {
        LastChar = advance();
      } while (LastChar != '\n' && LastChar != '\r' && LastChar != EOF);
      if (LastChar != EOF)
        return gettok();
    }
  }

  if (LastChar == ':') { // assign_symbol
    std::string temp;
    temp = LastChar;
    LastChar = advance();
    if (LastChar == '=') {
      LastChar = advance();
      return tok_ASSIGN_SYMBOL;
    }
  }

  if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
    IdentifierStr = LastChar;
    while (isalnum((LastChar = advance()))) {
      IdentifierStr += LastChar;
    }
    if (IdentifierStr == "FUNC" || IdentifierStr == "func")
      return tok_FUNC;
    if (IdentifierStr == "PRINT" || IdentifierStr == "print")
      return tok_PRINT;
    if (IdentifierStr == "RETURN" || IdentifierStr == "return")
      return tok_RETURN;
    if (IdentifierStr == "CONTINUE" || IdentifierStr == "continue")
      return tok_CONTINUE;
    if (IdentifierStr == "IF" || IdentifierStr == "if")
      return tok_IF;
    if (IdentifierStr == "THEN" || IdentifierStr == "then")
      return tok_THEN;
    if (IdentifierStr == "ELSE" || IdentifierStr == "else")
      return tok_ELSE;
    if (IdentifierStr == "FI" || IdentifierStr == "fi")
      return tok_FI;
    if (IdentifierStr == "WHILE" || IdentifierStr == "while")
      return tok_WHILE;
    if (IdentifierStr == "DO" || IdentifierStr == "do")
      return tok_DO;
    if (IdentifierStr == "DONE" || IdentifierStr == "done")
      return tok_DONE;
    if (IdentifierStr == "VAR" || IdentifierStr == "var")
      return tok_VAR;
    return tok_VARIABLE;
  }

  if (isdigit(LastChar)) { // Number: [0-9]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = advance();
    } while (isdigit(LastChar));

    NumVal = strtod(NumStr.c_str(), nullptr);
    return tok_INTEGER;
  }
  ////转义字符需要实现
  if (LastChar == '\"') {
    std::string textStr;
    LastChar = advance();
    do {
      textStr += LastChar;
      LastChar = advance();
    } while (LastChar != '\"');
    StrVal = textStr;
    LastChar = advance();
    return tok_TEXT;
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = advance();
  return ThisChar;
}

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

namespace {

raw_ostream &indent(raw_ostream &O, int size) {
  return O << std::string(size, ' ');
}

/// ExprAST - Base class for all expression nodes.
class ExprAST {
  SourceLocation Loc;

public:
  ExprAST(SourceLocation Loc = CurLoc) : Loc(Loc) {}
  virtual ~ExprAST() {}
  virtual Value *codegen() = 0;
  int getLine() const { return Loc.Line; }
  int getCol() const { return Loc.Col; }
  virtual raw_ostream &dump(raw_ostream &out, int ind) {
    return out << ':' << getLine() << ':' << getCol() << '\n';
  }
};

// StatementExprAST - Expression class for Statement
class StatementExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> States;

public:
  StatementExprAST(std::vector<std::unique_ptr<ExprAST>> States)
      : States(std::move(States)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "statement", ind);
    for (const auto &s : States)
      s->dump(indent(out, ind), ind + 1);
    return out;
  }
  Value *codegen();
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double Val) : Val(Val) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    return ExprAST::dump(out << Val, ind);
  }
  Value *codegen();
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(SourceLocation Loc, const std::string &Name)
      : ExprAST(Loc), Name(Name) {}
  const std::string &getName() const { return Name; }
  raw_ostream &dump(raw_ostream &out, int ind) override {
    return ExprAST::dump(out << Name, ind);
  }
  Value *codegen();
};

/// TextExprAST -Expression class for text literals
class TextExprAST : public ExprAST {
  std::string Str;

public:
  TextExprAST(std::string s) : Str(s) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    return ExprAST::dump(out << Str, ind);
  }
  Value *codegen();
};

/// VarExprAST - Expression class for var/in
class VarExprAST : public ExprAST {
  std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames;
  // std::unique_ptr<exprast> body;

public:
  VarExprAST(
      std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> VarNames,
      std::unique_ptr<ExprAST> Body)
      : VarNames(std::move(VarNames)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "var", ind);
    for (const auto &NamedVar : VarNames)
      NamedVar.second->dump(indent(out, ind) << NamedVar.first << ':', ind + 1);
    return out;
  }
  Value *codegen();
};

/// AssignVariableExprAST statement expression class for referencing assignment
/// ,like a:=100
class AssignExprAST : public ExprAST {
  std::string name;
  std::unique_ptr<ExprAST> expr;

public:
  AssignExprAST(const std::string name, std::unique_ptr<ExprAST> expr)
      : name(std::move(name)), expr(std::move(expr)){};
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "assign:" << name, ind);
    expr->dump(indent(out, ind) << "expr:", ind + 1);
    return out;
  }
  Value *codegen();
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(SourceLocation Loc, char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : ExprAST(Loc), Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "binary" << Op, ind);
    LHS->dump(indent(out, ind) << "LHS:", ind + 1);
    RHS->dump(indent(out, ind) << "RHS:", ind + 1);
    return out;
  }
  Value *codegen();
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(SourceLocation Loc, const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : ExprAST(Loc), Callee(Callee), Args(std::move(Args)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "call " << Callee, ind);
    for (const auto &Arg : Args)
      Arg->dump(indent(out, ind + 1), ind + 1);
    return out;
  }
  Value *codegen();
};

/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, Then, Else;

public:
  IfExprAST(SourceLocation Loc, std::unique_ptr<ExprAST> Cond,
            std::unique_ptr<ExprAST> Then, std::unique_ptr<ExprAST> Else)
      : ExprAST(Loc), Cond(std::move(Cond)), Then(std::move(Then)),
        Else(std::move(Else)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "if", ind);
    Cond->dump(indent(out, ind) << "Cond:", ind + 1);
    Then->dump(indent(out, ind) << "Then:", ind + 1);
    Else->dump(indent(out, ind) << "Else:", ind + 1);
    return out;
  }
  Value *codegen();
};

/// whileExprAST - Expression class for while
class WhileExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, DO;

public:
  WhileExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> DO)
      : Cond(std::move(Cond)), DO(std::move(DO)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "if", ind);
    Cond->dump(indent(out, ind) << "Cond:", ind + 1);
    DO->dump(indent(out, ind) << "Then:", ind + 1);
    return out;
  }
  Value *codegen();
};

/// PrintExprAST
class PrintExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  PrintExprAST(std::vector<std::unique_ptr<ExprAST>> returnConts)
      : Args(std::move(returnConts)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "print", ind);
    for (const auto &Arg : Args)
      Arg->dump(indent(out, ind + 1), ind + 1);
    return out;
  }
  Value *codegen();
};

/// ReturnExprAST
class ReturnExprAST : public ExprAST {
  std::unique_ptr<ExprAST> returnCont;

public:
  ReturnExprAST(std::unique_ptr<ExprAST> returnCont)
      : returnCont(std::move(returnCont)) {}
  raw_ostream &dump(raw_ostream &out, int ind) override {
    ExprAST::dump(out << "print", ind);
    returnCont->dump(indent(out, ind + 1), ind + 1);
    return out;
  }
  Value *codegen();
};

/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
  int Line;

public:
  PrototypeAST(SourceLocation Loc, const std::string &Name,
               std::vector<std::string> Args)
      : Name(Name), Args(std::move(Args)), Line(Loc.Line) {}

  const std::string &getName() const { return Name; }
  Function *codegen();
  int getLine() const { return Line; }
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  std::unique_ptr<PrototypeAST> Proto;
  std::unique_ptr<ExprAST> Body;

public:
  FunctionAST(std::unique_ptr<PrototypeAST> Proto,
              std::unique_ptr<ExprAST> Body)
      : Proto(std::move(Proto)), Body(std::move(Body)) {}
  Function *codegen();
  raw_ostream &dump(raw_ostream &out, int ind) {
    indent(out, ind) << "FunctionAST\n";
    ++ind;
    indent(out, ind) << "Body:";
    return Body ? Body->dump(out, ind) : out << "null\n";
  }
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok = ';';
static int getNextToken() { return CurTok = gettok(); }

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

//// Code Generation  变量准备   ////

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
// static std::map<std::string, Value *> NamedValues;
static std::map<std::string, AllocaInst *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

//// Code Generation  变量准备 END  ////

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
static std::unique_ptr<ExprAST> ParseStatement();

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
  auto Result = llvm::make_unique<NumberExprAST>(NumVal);
  getNextToken(); // consume the number
  return std::move(Result);
}

/// textexpr ::=text
static std::unique_ptr<ExprAST> ParseTextExpr() {
  auto TextResult = llvm::make_unique<TextExprAST>(StrVal);
  getNextToken();
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
      getNextToken(); // eat the ':='.

      Init = ParseExpression();
      if (!Init) {
        std::cout << "Expression Excepted" << std::endl;
      }
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

  /*auto Body = ParseExpression();
  if (!Body)
    return nullptr;*/
  std::cout << "解析到变量定义表达式" << std::endl;
  return llvm::make_unique<VarExprAST>(std::move(VarNames), nullptr);
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
  SourceLocation LitLoc = CurLoc;

  getNextToken(); // eat identifier.

  // Parse assignment_statement	: VARIABLE ASSIGN_SYMBOL expression
  if (CurTok == tok_ASSIGN_SYMBOL) {
    getNextToken(); // eat  tok_ASSIGN_SYMBOL
    auto expr = ParseExpression();
    if (!expr)
      return LogError("Expression excepted");
    std::cout << "解析到赋值语句" << std::endl;
    return llvm::make_unique<AssignExprAST>(std::move(IdName), std::move(expr));
  }

  if (CurTok != '(') // Simple variable ref.
  {
    std::cout << "解析到变量" << IdName << "\n";
    return llvm::make_unique<VariableExprAST>(LitLoc, IdName);
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

  std::cout << "解析到函数调用,调用函数为：" << IdName << "参数为：";
  for (size_t j = 0; j < Args.size(); j++) {
    std::cout << Args[j] << ",";
  }
  std::cout << std::endl;

  // Eat the ')'.
  getNextToken();

  return llvm::make_unique<CallExprAST>(LitLoc, IdName, std::move(Args));
}

/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static std::unique_ptr<ExprAST> ParseIfExpr() {
  SourceLocation IfLoc = CurLoc;
  getNextToken(); // eat the if.

  // condition.
  auto Cond = ParseExpression();
  if (!Cond)
    return nullptr;

  if (CurTok != tok_THEN)
    return LogError("expected then");
  getNextToken(); // eat the then

  std::unique_ptr<ExprAST> Then; // define then

  if (CurTok != '{') {
    Then = ParseExpression();
  } else {
    getNextToken(); // eat '{'
    Then = ParseStatement();
  }
  if (!Then)
    return nullptr;

  if ((CurTok != tok_ELSE) && (CurTok != tok_FI))
    return LogError("expected else or fi");

  if (CurTok == tok_FI) {
    getNextToken(); // eat fi
    return llvm::make_unique<IfExprAST>(IfLoc, std::move(Cond), std::move(Then),
                                        std::move(nullptr));
  }

  getNextToken(); // eat else

  std::unique_ptr<ExprAST> Else; // define then

  if (CurTok != '{') {
    Else = ParseExpression();
  } else {
    getNextToken(); // eat '{'
    Else = ParseStatement();
  }
  if (!Else)
    return nullptr;

  if (CurTok == tok_FI) {
    getNextToken();
    return llvm::make_unique<IfExprAST>(IfLoc, std::move(Cond), std::move(Then),
                                        std::move(Else));
  } else
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

  std::unique_ptr<ExprAST> Do = nullptr;

  if (CurTok != '{') {
    Do = ParseExpression();
  } else {
    getNextToken();
    Do = ParseStatement();
  }
  if (!Do)
    return nullptr;

  if (CurTok != tok_DONE)
    return LogError("expected DONE");
  getNextToken();
  return llvm::make_unique<WhileExprAST>(std::move(Cond), std::move(Do));
}

/// print_item	: expression| TEXT
static std::unique_ptr<ExprAST> ParsePrintExpr() {
  getNextToken(); // eat print
  std::vector<std::unique_ptr<ExprAST>> Args;
  std::string str = "";
  Args.push_back(nullptr);
  do {
    switch (CurTok) {
    case tok_TEXT:
      str += StrVal;
      getNextToken(); //手动读取到下一个符号
      break;
    case tok_INTEGER:
    case tok_VARIABLE:
      Args.push_back(std::move(ParseExpression()));
      str += "%lf";
      break;
    }
  } while (CurTok == ',' ? getNextToken(), true : false);
  Args[0] = llvm::make_unique<TextExprAST>(str);
  return llvm::make_unique<PrintExprAST>(std::move(Args));
};

/// return_statement: RETURN expression
static std::unique_ptr<ExprAST> ParseReturnExpr() {
  getNextToken(); // eat return
  auto returnCont = ParseExpression();
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
    if (TokPrec < ExprPrec)
      return LHS;

    // Okay, we know this is a binop.
    int BinOp = CurTok;
    SourceLocation BinLoc = CurLoc;
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
    LHS = llvm::make_unique<BinaryExprAST>(BinLoc, BinOp, std::move(LHS),
                                           std::move(RHS));
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
static std::unique_ptr<ExprAST> ParseStatement() {
  std::vector<std::unique_ptr<ExprAST>> states;
  do {
    auto E = ParseExpression();
    states.push_back(std::move(E));
  } while (CurTok != '}');
  getNextToken(); // eat '}'
  return llvm::make_unique<StatementExprAST>(std::move(states));
}

/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_VARIABLE)
    return LogErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  SourceLocation FnLoc = CurLoc;
  getNextToken();

  if (CurTok != '(')
    return LogErrorP("Expected '(' in prototype");

  std::vector<std::string> ArgNames;
  while (true) {
    CurTok = getNextToken();
    if (CurTok == tok_VARIABLE)
      ArgNames.push_back(IdentifierStr);
    else if (CurTok == ',')
      continue;
    else
      break;
  }

  if (CurTok != ')')
    return LogErrorP("Expected ')' in prototype");

  // success.
  getNextToken(); // eat ')'.

  std::cout << "parsing FUNC, ";
  std::cout << "FUNC name is: " << FnName << " ";
  std::cout << "parameter list is:";
  for (unsigned i = 0; i < ArgNames.size(); i++)
    std::cout << ArgNames[i] << " ";
  std::cout << std::endl;

  return llvm::make_unique<PrototypeAST>(FnLoc, FnName, std::move(ArgNames));
}

/// definition ::= 'FUNC' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken(); // eat FUNC.
  auto Proto = ParsePrototype();
  if (!Proto)
    return nullptr;
  getNextToken(); // eat'{'.
  if (auto E = ParseStatement()) {
    return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  SourceLocation FnLoc = CurLoc;
  if (auto E = ParseExpression()) {
    // Make an anonymous proto.
    auto Proto = llvm::make_unique<PrototypeAST>(FnLoc, "__anon_expr",
                                                 std::vector<std::string>());
    return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
  }
  return nullptr;
}

/// external ::= 'extern' prototype
static std::unique_ptr<PrototypeAST> ParseExtern() {
  getNextToken(); // eat extern.
  return ParsePrototype();
}
//===----------------------------------------------------------------------===//
// Debug Info Support
//===----------------------------------------------------------------------===//

static std::unique_ptr<DIBuilder> DBuilder; //协助调试元数据

DIType *DebugInfo::getDoubleTy() {
  if (DblTy)
    return DblTy;

  DblTy = DBuilder->createBasicType("double", 64, dwarf::DW_ATE_float);
  return DblTy;
}

void DebugInfo::emitLocation(ExprAST *AST) {
  if (!AST)
    return Builder.SetCurrentDebugLocation(DebugLoc());
  DIScope *Scope;
  if (LexicalBlocks.empty())
    Scope = TheCU;
  else
    Scope = LexicalBlocks.back();
  Builder.SetCurrentDebugLocation(
      DebugLoc::get(AST->getLine(), AST->getCol(), Scope));
}

static DISubroutineType *CreateFunctionType(unsigned NumArgs, DIFile *Unit) {
  SmallVector<Metadata *, 8> EltTys;
  DIType *DblTy = KSDbgInfo.getDoubleTy();

  // Add the result type.
  EltTys.push_back(DblTy);

  for (unsigned i = 0, e = NumArgs; i != e; ++i)
    EltTys.push_back(DblTy);

  return DBuilder->createSubroutineType(DBuilder->getOrCreateTypeArray(EltTys));
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

bool isreturn = false;

//辅助函数  分配内存
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const std::string &VarName) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
                   TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(Type::getDoubleTy(TheContext), 0, VarName.c_str());
}

Value *LogErrorV(const char *Str) {
  LogError(Str);
  return nullptr;
}

Function *getFunction(std::string Name) {
  // First, see if the function has already been added to the current module.
  if (auto *F = TheModule->getFunction(Name))
    return F;

  // If not, check whether we can codegen the declaration from some existing
  // prototype.
  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end())
    return FI->second->codegen();

  // If no existing prototype exists, return null.
  return nullptr;
}

Value *StatementExprAST::codegen() {
  if (States.size() == 0)
    return nullptr;
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  for (unsigned i = 0; i < States.size(); i++) {
    if (Value *RetVal = States[i]->codegen()) {
      /*BasicBlock *stateBB =
          BasicBlock::Create(TheContext, "statement", TheFunction);
      Builder.SetInsertPoint(stateBB);*/
    }
  }
  // Builder.CreateRetVoid();
  return ConstantFP::get(TheContext, APFloat(0.0));
}

Value *NumberExprAST::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Undefined variable name");
  return Builder.CreateLoad(V, Name.c_str());
  // return V;
}
// TODO
Value *TextExprAST::codegen() { return Builder.CreateGlobalStringPtr(Str); }
// TODO  语句   已在堆栈上分配内存，已测试，暂无问题
Value *VarExprAST::codegen() {
  if (VarNames.size() == 0)
    return nullptr;
  for (unsigned i = 0; i < VarNames.size(); i++) {
    NamedValues[VarNames[i].first] = CreateEntryBlockAlloca(
        Builder.GetInsertBlock()->getParent(), VarNames[i].first);
    if (!VarNames[i].second) { //默认值为零
      Builder.CreateStore(NumberExprAST(0.0).codegen(),
                          NamedValues[VarNames[i].first]);
      // ConstantFP::get(TheContext, APFloat(0.0));
    } else {
      Builder.CreateStore(VarNames[i].second->codegen(),
                          NamedValues[VarNames[i].first]);
      // Builder.CreateAlloca(Type::getDoubleTy(TheContext),NamedValues[VarNames[i].first]);
    }
  }
  return Constant::getNullValue(Type::getDoubleTy(TheContext));
}

// TODO
Value *AssignExprAST::codegen() {
  Value *V = NamedValues[name];
  if (!V)
    return LogErrorV("Undefined variable name");
  /*V = expr->codegen();
  NamedValues[name] = V;*/
  return Builder.CreateStore(expr->codegen(), NamedValues[name]);
  // return V;
}

Value *BinaryExprAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  if (!L || !R)
    return nullptr;

  switch (Op) {
  case '+':
    return Builder.CreateFAdd(L, R, "addtmp");
  case '-':
    return Builder.CreateFSub(L, R, "subtmp");
  case '*':
    return Builder.CreateFMul(L, R, "multmp");
  case '/':
    return Builder.CreateFDiv(L, R, "divmp");
  case '<':
    L = Builder.CreateFCmpULT(L, R, "cmptmp");
    // Convert bool 0/1 to double 0.0 or 1.0
    return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
  default:
    return LogErrorV("invalid binary operator");
  }
}
//语句
Value *CallExprAST::codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = getFunction(Callee);
  if (!CalleeF)
    return LogErrorV("Unknown function referenced");

  // If argument mismatch error.
  if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect # arguments passed");

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }
  return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}
//待完善  语句
Value *IfExprAST::codegen() {
  Value *CondV = Cond->codegen();
  int isReturn = 0;
  if (!CondV)
    return nullptr;

  // Convert condition to a bool by comparing non-equal to 0.0.
  CondV = Builder.CreateFCmpONE(
      CondV, ConstantFP::get(TheContext, APFloat(0.0)), "ifcond");

  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  // Create blocks for the then and else cases.  Insert the 'then' block at the
  // end of the function.
  BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
  BasicBlock *ElseBB = BasicBlock::Create(TheContext, "else");
  BasicBlock *MergeBB = BasicBlock::Create(TheContext, "ifcont");

  Builder.CreateCondBr(CondV, ThenBB, ElseBB);

  // Emit then value.
  Builder.SetInsertPoint(ThenBB);

  Value *ThenV = Then->codegen();
  if (!ThenV)
    return nullptr;

  if (isreturn) {
    isreturn = false;
    isReturn++;
  } else
    Builder.CreateBr(MergeBB);
  // Codegen of 'Then' can change the current block, update ThenBB for the PHI.
  ThenBB = Builder.GetInsertBlock();

  // Emit else block.
  TheFunction->getBasicBlockList().push_back(ElseBB);
  Builder.SetInsertPoint(ElseBB);

  Value *ElseV = NULL;
  if (Else) {
    ElseV = Else->codegen();
    if (!ElseV)
      return nullptr;
  }

  if (isreturn) {
    isreturn = false;
    isReturn++;
  } else
    Builder.CreateBr(MergeBB);
  // Codegen of 'Else' can change the current block, update ElseBB for the PHI.
  ElseBB = Builder.GetInsertBlock();

  // Emit merge block.
  if (isReturn != 2) {
    TheFunction->getBasicBlockList().push_back(MergeBB);
    Builder.SetInsertPoint(MergeBB);
    //PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 2, "iftmp");

    /*PN->addIncoming(ThenV, ThenBB);
    if (ElseV)
          PN->addIncoming(ElseV, ElseBB);*/
  }
  return Constant::getNullValue(Type::getDoubleTy(TheContext)); //返回空值
}
// TODO  语句
Value *WhileExprAST::codegen() {
  // Emit the start code first, without 'variable' in scope.
  /*Value *StartVal = Start->codegen();
  if (!StartVal)
    return nullptr;*/

  // Make the new basic block for the loop header, inserting after current
  // block.
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *PreheaderBB = Builder.GetInsertBlock();
  BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop", TheFunction);

  // Insert an explicit fall through from the current block to the LoopBB.
  Builder.CreateBr(LoopBB);

  // Start insertion in LoopBB.
  Builder.SetInsertPoint(LoopBB);

  // Start the PHI node with an entry for Start.
  /*PHINode *Variable =
      Builder.CreatePHI(Type::getDoubleTy(TheContext), 2, VarName);
  Variable->addIncoming(StartVal, PreheaderBB);*/

  // Within the loop, the variable is defined equal to the PHI node.  If it
  // shadows an existing variable, we have to restore it, so save it now.
 /* Value *OldVal = NamedValues[VarName];
  NamedValues[VarName] = Variable;*/

  // Emit the body of the loop.  This, like any other expr, can change the
  // current BB.  Note that we ignore the value computed by the body, but don't
  // allow an error.
  if (!DO->codegen())
    return nullptr;

  // Emit the step value.
  //Value *StepVal = nullptr;
  //if (Step) {
  //  StepVal = Step->codegen();
  //  if (!StepVal)
  //    return nullptr;
  //} else {
  //  // If not specified, use 1.0.
  //  StepVal = ConstantFP::get(TheContext, APFloat(1.0));
  //}

  //Value *NextVar = Builder.CreateFAdd(Variable, StepVal, "nextvar");

  // Compute the end condition.
  Value *CondV = Cond->codegen();
  if (!CondV)
    return nullptr;

  // Convert condition to a bool by comparing non-equal to 0.0.
  CondV = Builder.CreateFCmpONE(
      CondV, ConstantFP::get(TheContext, APFloat(0.0)), "loopcond");

  // Create the "after loop" block and insert it.
  BasicBlock *LoopEndBB = Builder.GetInsertBlock();
  BasicBlock *AfterBB =
      BasicBlock::Create(TheContext, "afterloop", TheFunction);

  // Insert the conditional branch into the end of LoopEndBB.
  Builder.CreateCondBr(CondV, LoopBB, AfterBB);

  // Any new code will be inserted in AfterBB.
  Builder.SetInsertPoint(AfterBB);

  // Add a new entry to the PHI node for the backedge.
  //Variable->addIncoming(NextVar, LoopEndBB);

  //// Restore the unshadowed variable.
  //if (OldVal)
  //  NamedValues[VarName] = OldVal;
  //else
  //  NamedValues.erase(VarName);

  // for expr always returns 0.0.
  return Constant::getNullValue(Type::getDoubleTy(TheContext));


  //Function *TheFunction = Builder.GetInsertBlock()->getParent();
  //int isReturn = 0;
  //// Create blocks for the then and else cases.  Insert the 'then' block at the
  //// end of the function.
  //BasicBlock *WhileBB = BasicBlock::Create(TheContext, "while", TheFunction);
  //Builder.SetInsertPoint(WhileBB);

  //Value *CondV = Cond->codegen();
  //if (!CondV)
  //  return nullptr;
  //// Convert condition to a bool by comparing non-equal to 0.0.
  //CondV = Builder.CreateFCmpONE(
  //    CondV, ConstantFP::get(TheContext, APFloat(0.0)), "whilecond");

  //BasicBlock *DoBB = BasicBlock::Create(TheContext, "do", TheFunction);
  //BasicBlock *DoneBB = BasicBlock::Create(TheContext, "done");
  //BasicBlock *EntryBB = BasicBlock::Create(TheContext, "entry");

  //Builder.CreateCondBr(CondV, DoBB, DoneBB);

  //// Emit then value.
  //Builder.SetInsertPoint(DoBB);

  //Value *DoV = DO->codegen();
  //if (!DoV)
  //  return nullptr;

  //Builder.CreateBr(WhileBB);
  //// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
  //DoBB = Builder.GetInsertBlock();

  //// Emit else block.
  //TheFunction->getBasicBlockList().push_back(DoneBB);
  //Builder.SetInsertPoint(DoneBB);

  ///*Value *ElseV = Else->codegen();
  //if (!ElseV)
  //  return nullptr;*/

  //if(!isreturn) Builder.CreateBr(EntryBB);
  //// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
  //DoneBB = Builder.GetInsertBlock();

  //// Emit merge block.
  //if (!isreturn) {
  //  TheFunction->getBasicBlockList().push_back(EntryBB);
  //  Builder.SetInsertPoint(EntryBB);
  //} else
  //  isreturn = false;
  //// PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 1,
  //// "whiletmp");

  //// PN->addIncoming(DoV, DoBB);
  //// PN->addIncoming(ElseV, ElseBB);
  return Constant::getNullValue(Type::getDoubleTy(TheContext));
}

llvm::Function *get_printf() {
  const char *fun_name = "printf";
  llvm::Function *func = TheModule->getFunction(fun_name);
  if (func == nullptr) {
    llvm::FunctionType *func_type = llvm::FunctionType::get(
        llvm::Type::getInt32Ty(TheModule->getContext()),
        {llvm::Type::getInt8PtrTy(TheModule->getContext())}, true);
    func = llvm::Function::Create(func_type, llvm::GlobalValue::ExternalLinkage,
                                  fun_name, TheModule.get());
  }
  return func;
}

//待完善  语句
Value *PrintExprAST::codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = get_printf();
  if (!CalleeF)
    return LogErrorV("Unknown function referenced on [PRINT]");

  // If argument mismatch error.
  /*if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect # arguments passed");*/

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }

  // std::initializer_list<Value *> lArgs;
  auto str = Args[0]->codegen();
  return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}
// TODO
Value *ReturnExprAST::codegen() {
  isreturn = true;
  return Builder.CreateRet(returnCont->codegen());
}

Function *PrototypeAST::codegen() {
  // Make the function type:  double(double,double) etc.
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(TheContext));
  FunctionType *FT =
      FunctionType::get(Type::getDoubleTy(TheContext), Doubles, false);

  Function *F =
      Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  // Set names for all arguments.
  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Args[Idx++]);

  return F;
}

Function *FunctionAST::codegen() {
  // First, check for an existing function from a previous 'extern' declaration.
  auto &P = *Proto;
  FunctionProtos[Proto->getName()] = std::move(Proto);
  Function *TheFunction = getFunction(P.getName());
  // Function *TheFunction = TheModule->getFunction(Proto->getName());

  if (!TheFunction)
    TheFunction = Proto->codegen();

  if (!TheFunction)
    return nullptr;

  // Create a new basic block to start insertion into.
  BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
  Builder.SetInsertPoint(BB);

  // Create a subprogram DIE for this function.
  DIFile *Unit = DBuilder->createFile(KSDbgInfo.TheCU->getFilename(),
                                      KSDbgInfo.TheCU->getDirectory());

  DIScope *FContext = Unit;
  unsigned LineNo = P.getLine();
  unsigned ScopeLine = LineNo;
  DISubprogram *SP = DBuilder->createFunction(
      FContext, P.getName(), StringRef(), Unit, LineNo,
      CreateFunctionType(TheFunction->arg_size(), Unit),
      false /* internal linkage */, true /* definition */, ScopeLine,
      DINode::FlagPrototyped, false);
  TheFunction->setSubprogram(SP);

  // Push the current scope.
  KSDbgInfo.LexicalBlocks.push_back(SP);

  // Unset the location for the prologue emission (leading instructions with no
  // location in a function are considered part of the prologue and the debugger
  // will run past them when breaking on a function)
  KSDbgInfo.emitLocation(nullptr);

  NamedValues.clear(); //*****2018/11/21*****//

  // Record the function arguments in the NamedValues map.
  // NamedValues.clear();
  for (auto &Arg : TheFunction->args()) {
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());
    Builder.CreateStore(&Arg, Alloca);
    NamedValues[Arg.getName()] = Alloca;
    // NamedValues[Arg.getName()] = &Arg;
  }

  if (Value *RetVal = Body->codegen()) {
    // Finish off the function.
    // Builder.CreateRet(RetVal);

    // Validate the generated code, checking for consistency.
    verifyFunction(*TheFunction);

    // Optimize the function.
    TheFPM->run(*TheFunction);

    TheFunction->viewCFG();
    return TheFunction;
  }

  // Error reading body, remove function.
  TheFunction->eraseFromParent();
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void InitializeModuleAndPassManager() {
  // Open a new module.
  TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
  auto dl = TheJIT->getTargetMachine().createDataLayout();
  TheModule->setDataLayout(dl);

  // Create a new pass manager attached to it.
  TheFPM = llvm::make_unique<legacy::FunctionPassManager>(TheModule.get());

  // Promote allocas to registers.  优化内存分配
  TheFPM->add(createPromoteMemoryToRegisterPass());
  // Do simple "peephole" optimizations and bit-twiddling optzns.
  TheFPM->add(createInstructionCombiningPass());
  // Reassociate expressions.
  TheFPM->add(createReassociatePass());
  // Eliminate Common SubExpressions.
  TheFPM->add(createGVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  TheFPM->add(createCFGSimplificationPass());

  TheFPM->doInitialization();
}

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
    if (auto *FnIR = FnAST->codegen()) {
      std::cout << "\n\n\n******中间代码生成******\n\n" << std::endl;
      fprintf(stderr, "Read function definition:");
      FnIR->print(errs());
      fprintf(stderr, "\n");
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleExtern() {
  if (auto ProtoAST = ParseExtern()) {
    if (auto *FnIR = ProtoAST->codegen()) {
      fprintf(stderr, "Read extern: ");
      FnIR->print(errs());
      fprintf(stderr, "\n");
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (auto FnAST = ParseTopLevelExpr()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read top-level expression:");
      FnIR->print(errs());
      fprintf(stderr, "\n");
      // JIT the module containing the anonymous expression, keeping a handle so
      // we can free it later.
      auto H = TheJIT->addModule(std::move(TheModule));
      InitializeModuleAndPassManager();

      // Search the JIT for the __anon_expr symbol.
      auto ExprSymbol = TheJIT->findSymbol("__anon_expr");
      assert(ExprSymbol && "Function not found");

      // Get the symbol's address and cast it to the right type (takes no
      // arguments, returns a double) so we can call it as a native function.
      double (*FP)() =
          (double (*)())(intptr_t)cantFail(ExprSymbol.getAddress());
      fprintf(stderr, "Evaluated to %f\n", FP());

      // Delete the anonymous expression module from the JIT.
      TheJIT->removeModule(H);
    }
    /*   if (auto *FnIR = FnAST->codegen()) {
         fprintf(stderr, "Read top-level expression:");
         FnIR->print(errs());
         fprintf(stderr, "\n");
       }*/
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
    case '$':
    case tok_eof:
      return;
    case ';': // ignore top-level semicolons.
      getNextToken();
      break;
    case tok_FUNC:
      HandleDefinition();
      break;
      /* case tok_extern:
         handleextern();
         break;*/
    default:
      // HandleTopLevelExpression();
      getNextToken();
      break;
    }
    /*getNextToken();*/
  }
}

//===----------------------------------------------------------------------===//
// "Library" functions that can be "extern'd" from user code.
//===----------------------------------------------------------------------===//

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X) {
  fputc((char)X, stderr);
  return 0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" DLLEXPORT double printd(double X) {
  fprintf(stderr, "%f\n", X);
  return 0;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;
  BinopPrecedence['/'] = 40; // highest.

  // Make the module, which holds all the code.
  // TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
  TheJIT = llvm::make_unique<KaleidoscopeJIT>();
  InitializeModuleAndPassManager();

  // Construct the DIBuilder, we do this here because we need the module.
  DBuilder = llvm::make_unique<DIBuilder>(*TheModule);

  // Create the compile unit for the module.
  // Currently down as "fib.ks" as a filename since we're redirecting stdin
  // but we'd like actual source locations.
  KSDbgInfo.TheCU = DBuilder->createCompileUnit(
      dwarf::DW_LANG_C, DBuilder->createFile("fib.ks", "."), "VSL Compiler", 0,
      "", 0);
  // Run the main "interpreter loop" now.
  MainLoop();

  // Initialize the target registry etc.
  /*InitializeAllTargetInfos();
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmParsers();
  InitializeAllAsmPrinters();*/

  auto TargetTriple = sys::getDefaultTargetTriple();
  TheModule->setTargetTriple(TargetTriple);

  std::string Error;
  auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);

  // Print an error and exit if we couldn't find the requested target.
  // This generally occurs if we've forgotten to initialise the
  // TargetRegistry or we have a bogus target triple.
  if (!Target) {
    errs() << Error;
    return 1;
  }

  auto CPU = "generic";
  auto Features = "";

  TargetOptions opt;
  auto RM = Optional<Reloc::Model>();
  auto TheTargetMachine =
      Target->createTargetMachine(TargetTriple, CPU, Features, opt, RM);

  TheModule->setDataLayout(TheTargetMachine->createDataLayout());

  auto Filename = "output.o";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }

  legacy::PassManager pass;
  auto FileType = TargetMachine::CGFT_ObjectFile;

  if (TheTargetMachine->addPassesToEmitFile(pass, dest, nullptr, FileType)) {
    errs() << "TheTargetMachine can't emit a file of this type";
    return 1;
  }

  pass.run(*TheModule);
  dest.flush();

  outs() << "Wrote " << Filename << "\n";

  // Finalize the debug info.
  DBuilder->finalize();
  // Print out all of the generated code.
  TheModule->print(errs(), nullptr);

  return 0;
}
