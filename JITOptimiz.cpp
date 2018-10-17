#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;

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

/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = getchar();

  // skip any comment.
  if (LastChar == '/') {
    if (LastChar = getchar() == '/') {
      do {
        LastChar = getchar();
      } while (LastChar != '\n' && LastChar != '\r' && LastChar != EOF);
      if (LastChar != EOF)
        return gettok();
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
    while (isalnum((LastChar = getchar()))) {
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
      LastChar = getchar();
    } while (isdigit(LastChar));

    NumVal = strtod(NumStr.c_str(), nullptr);
    return tok_INTEGER;
  }
  ////转义字符需要实现
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
  virtual Value *codegen() = 0;
};

// StatementExprAST - Expression class for Statement
class StatementExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> States;

public:
  StatementExprAST(std::vector<std::unique_ptr<ExprAST>> States)
      : States(std::move(States)) {}
  Value *codegen();
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;

public:
  NumberExprAST(double Val) : Val(Val) {}
  Value *codegen();
};

/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;

public:
  VariableExprAST(const std::string &Name) : Name(Name) {}
  const std::string &getName() const { return Name; }
  Value *codegen();
};

/// TextExprAST -Expression class for text literals
class TextExprAST : public ExprAST {
  std::string Str;

public:
  TextExprAST(std::string s) : Str(s) {}
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
  Value *codegen();
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  std::unique_ptr<ExprAST> LHS, RHS;

public:
  BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
      : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
  Value *codegen();
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  CallExprAST(const std::string &Callee,
              std::vector<std::unique_ptr<ExprAST>> Args)
      : Callee(Callee), Args(std::move(Args)) {}
  Value *codegen();
};

/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, Then, Else;

public:
  IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
            std::unique_ptr<ExprAST> Else)
      : Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}
  Value *codegen();
};

/// whileExprAST - Expression class for while
class WhileExprAST : public ExprAST {
  std::unique_ptr<ExprAST> Cond, DO;

public:
  WhileExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> DO)
      : Cond(std::move(Cond)), DO(std::move(DO)) {}
  Value *codegen();
};

/// PrintExprAST
class PrintExprAST : public ExprAST {
  std::vector<std::unique_ptr<ExprAST>> Args;

public:
  PrintExprAST(std::vector<std::unique_ptr<ExprAST>> returnConts)
      : Args(std::move(returnConts)) {}
  Value *codegen();
};

/// ReturnExprAST
class ReturnExprAST : public ExprAST {
  std::unique_ptr<ExprAST> returnCont;

public:
  ReturnExprAST(std::unique_ptr<ExprAST> returnCont)
      : returnCont(std::move(returnCont)) {}
  Value *codegen();
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
  Function *codegen();
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

//// Code Generation  变量准备   ////

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<KaleidoscopeJIT>
    TheJIT; //这个地方要改，改成我们编译的语言！！！
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

  std::cout << "解析到函数调用,调用函数为：" << IdName << "参数为：";
  for (int j = 0; j < Args.size(); j++) {
    std::cout << Args[j] << ",";
  }
  std::cout << std::endl;

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
    getNextToken();
    return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
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

  auto Do = ParseExpression();
  if (!Do)
    return nullptr;

  if (CurTok != tok_DONE)
    return LogError("expected DONE");

  return llvm::make_unique<WhileExprAST>(std::move(Cond), std::move(Do));
}

/// print_item	: expression| TEXT
static std::unique_ptr<ExprAST> ParsePrintExpr() {
  getNextToken(); // eat print
  auto printCont = ParseExpression();
  return nullptr; // llvm::make_unique<PrintExprAST>(std::move(printCont));
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

  return llvm::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
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
  if (auto E = ParseExpression()) {
    // Make an anonymous proto.
    auto Proto = llvm::make_unique<PrototypeAST>("__anon_expr",
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
// Code Generation
//===----------------------------------------------------------------------===//

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
  Builder.CreateRetVoid();
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
  return V;
}
// TODO
Value *TextExprAST::codegen() { return nullptr; }
// TODO  语句
Value *VarExprAST::codegen() {
  if (VarNames.size() == 0)
    return nullptr;
  for (unsigned i = 0; i < VarNames.size(); i++) {
    if (!VarNames[i].second)
      NamedValues[VarNames[i].first] =
          ConstantFP::get(TheContext, APFloat(0.0));
    else
      NamedValues[VarNames[i].first] = std::move(VarNames[i].second->codegen());
    // Builder.CreateAlloca(Type::getDoubleTy(TheContext),NamedValues[VarNames[i].first]);
  }
  return ConstantFP::get(TheContext, APFloat(0.0));
}

// TODO
Value *AssignExprAST::codegen() {
  Value *V = NamedValues[name];
  if (!V)
    return LogErrorV("Undefined variable name");
  V = expr->codegen();
  NamedValues[name] = V;
  return V;
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

  Builder.CreateBr(MergeBB);
  // Codegen of 'Then' can change the current block, update ThenBB for the PHI.
  ThenBB = Builder.GetInsertBlock();

  // Emit else block.
  TheFunction->getBasicBlockList().push_back(ElseBB);
  Builder.SetInsertPoint(ElseBB);

  Value *ElseV = Else->codegen();
  if (!ElseV)
    return nullptr;

  Builder.CreateBr(MergeBB);
  // Codegen of 'Else' can change the current block, update ElseBB for the PHI.
  ElseBB = Builder.GetInsertBlock();

  // Emit merge block.
  TheFunction->getBasicBlockList().push_back(MergeBB);
  Builder.SetInsertPoint(MergeBB);
  PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 2, "iftmp");

  PN->addIncoming(ThenV, ThenBB);
  PN->addIncoming(ElseV, ElseBB);
  return PN;
}
// TODO  语句
Value *WhileExprAST::codegen() { 
  Value *CondV = Cond->codegen();
  if (!CondV)
    return nullptr;

  // Convert condition to a bool by comparing non-equal to 0.0.
  CondV = Builder.CreateFCmpONE(
      CondV, ConstantFP::get(TheContext, APFloat(0.0)), "whilecond");

  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  // Create blocks for the then and else cases.  Insert the 'then' block at the
  // end of the function.
  BasicBlock *WhileBB = BasicBlock::Create(TheContext, "while", TheFunction);
  Builder.SetInsertPoint(WhileBB);

  BasicBlock *DoBB = BasicBlock::Create(TheContext, "do", TheFunction);
  BasicBlock *DoneBB = BasicBlock::Create(TheContext, "done");
  BasicBlock *EntryBB = BasicBlock::Create(TheContext, "entry");

  Builder.CreateCondBr(CondV, DoBB, DoneBB);

  // Emit then value.
  Builder.SetInsertPoint(DoBB);

  Value *DoV = DO->codegen();
  if (!DoV)
    return nullptr;

  Builder.CreateBr(WhileBB);
  // Codegen of 'Then' can change the current block, update ThenBB for the PHI.
  DoBB = Builder.GetInsertBlock();

  // Emit else block.
  TheFunction->getBasicBlockList().push_back(DoneBB);
  Builder.SetInsertPoint(DoneBB);

  /*Value *ElseV = Else->codegen();
  if (!ElseV)
    return nullptr;*/

  Builder.CreateBr(EntryBB);
  // Codegen of 'Else' can change the current block, update ElseBB for the PHI.
  DoneBB = Builder.GetInsertBlock();

  // Emit merge block.
  TheFunction->getBasicBlockList().push_back(EntryBB);
  Builder.SetInsertPoint(EntryBB);
  PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 1, "whiletmp");

  PN->addIncoming(DoV, DoBB);
  // PN->addIncoming(ElseV, ElseBB);
  return PN;
}
//待完善  语句
Value *PrintExprAST::codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = TheModule->getFunction("PRINT");
  if (!CalleeF)
    return LogErrorV("Unknown function referenced on [PRINT]");

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
// TODO
Value *ReturnExprAST::codegen() {
  Builder.CreateRet(returnCont->codegen());
  return nullptr;
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

  // Record the function arguments in the NamedValues map.
  // NamedValues.clear();
  for (auto &Arg : TheFunction->args())
    NamedValues[Arg.getName()] = &Arg;

  if (Value *RetVal = Body->codegen()) {
    // Finish off the function.
    Builder.CreateRet(RetVal);

    // Validate the generated code, checking for consistency.
    verifyFunction(*TheFunction);

    // Optimize the function.
    TheFPM->run(*TheFunction);
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
    std::cout << "\n\n\n******中间代码生成******\n\n" << std::endl;
    if (auto *FnIR = FnAST->codegen()) {
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
    getNextToken();
    switch (CurTok) {
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
      HandleTopLevelExpression();
      break;
    }
  }
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
  TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
  TheJIT = llvm::make_unique<KaleidoscopeJIT>();
  InitializeModuleAndPassManager();
  // Run the main "interpreter loop" now.
  MainLoop();

  // Print out all of the generated code.
  TheModule->print(errs(), nullptr);

  return 0;
}
