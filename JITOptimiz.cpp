#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;

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

  /*auto Body = ParseExpression();
  if (!Body)
    return nullptr;*/
  std::cout << "解析到变量定义表达式";
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
  // if (CurTok == tok_ASSIGN_SYMBOL) {
  //  getNextToken(); // eat  tok_ASSIGN_SYMBOL
  //  return llvm::make_unique<AssignVariableExprAST>(IdName,ParseExpression());
  //}

  if (CurTok != '(') // Simple variable ref.
  {
    std::cout << "解析到变量" << IdName << "\n";
    std::unique_ptr<VariableExprAST> varPtr =
        llvm::make_unique<VariableExprAST>(IdName);
    NamedValues[IdName] = NumberExprAST(0.0).codegen();
    return varPtr;
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

  /* std::cout << "解析到函数调用,调用函数为：" << IdName << "参数为：";
   for (int j = 0; j < Args.size(); j++) {
     std::cout << Args[j] << " ";
   }
   std::cout << "\n";
 */
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

  if (CurTok == tok_FI)
    return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
                                        std::move(Else));
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
  getNextToken(); // eat print
  std::vector<std::unique_ptr<ExprAST>> returnConts;
  while (CurTok != ',') {
    auto returnCont = ParseExpression();
    returnConts.push_back(std::move(returnCont));
  }
  return nullptr; // llvm::make_unique<ReturnExprAST>(std::move(returnConts),nullptr);
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
  if (auto E = ParseExpression()) {
    getNextToken();
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

Value *NumberExprAST::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Unknown variable name");
  return V;
}
// TODO
Value *TextExprAST::codegen() { return nullptr; }
// TODO
Value *VarExprAST::codegen() {
  for (unsigned i = 0; i < VarNames.size(); i++)
    VarNames[i].second->codegen();
  Value *V = NamedValues["1"];
  if (!V)
    return LogErrorV("Unknown variable name");
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

Value *CallExprAST::codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = TheModule->getFunction(Callee);
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
//待完善
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
// TODO
Value *WhileExprAST::codegen() { return nullptr; }
//待完善
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
  returnCont->codegen();
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
  Function *TheFunction = TheModule->getFunction(Proto->getName());

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

    return TheFunction;
  }

  // Error reading body, remove function.
  TheFunction->eraseFromParent();
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void HandleDefinition() {
  if (auto FnAST = ParseDefinition()) {
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
    }
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
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;
  BinopPrecedence['/'] = 40; // highest.

  // Make the module, which holds all the code.
  TheModule = llvm::make_unique<Module>("my cool jit", TheContext);

  // Run the main "interpreter loop" now.
  MainLoop();

  // Print out all of the generated code.
  TheModule->print(errs(), nullptr);

  return 0;
}
