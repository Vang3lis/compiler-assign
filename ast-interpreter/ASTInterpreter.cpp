//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool --------------===//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/EvaluatedExprVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

#include "Environment.h"

class InterpreterVisitor : 
   public EvaluatedExprVisitor<InterpreterVisitor> {
public:
   explicit InterpreterVisitor(const ASTContext &context, Environment * env)
   : EvaluatedExprVisitor(context), mEnv(env) {}
   virtual ~InterpreterVisitor() {}

   virtual void VisitBinaryOperator (BinaryOperator * bop) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(bop);
	   mEnv->binop(bop);
   }
   virtual void VisitUnaryOperator(UnaryOperator * uop) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(uop);
	   mEnv->unaryop(uop);
   }
   virtual void VisitDeclRefExpr(DeclRefExpr * expr) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(expr);
	   mEnv->declref(expr);
   }
   virtual void VisitCastExpr(CastExpr * expr) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(expr);
	   mEnv->cast(expr);
   }
   virtual void VisitCallExpr(CallExpr * call) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(call);
	   mEnv->call(call);
	   FunctionDecl *fdecl = call->getDirectCallee();
	   if(fdecl)
	   {
		   // call user-define func
		   // TODO: handle global var
		   if(!fdecl->getName().equals("GET") &&
				!fdecl->getName().equals("PRINT") && 
				!fdecl->getName().equals("MALLOC") &&
				!fdecl->getName().equals("FREE"))
		   {
			   Visit(fdecl->getBody());
			   bool hasret = false;
			   int64_t retval = -1;
			   if(mEnv->getCurrentStack()->hasRetVal())
			   {
				   hasret = true;
				   retval = mEnv->getCurrentStack()->getRetVal();
				   mEnv->popStack();
				   mEnv->getCurrentStack()->bindStmt(call, retval);
			   }
			   else 
				   mEnv->popStack();
		   }

	   }
   }
   virtual void VisitDeclStmt(DeclStmt * declstmt) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(declstmt);
	   mEnv->decl(declstmt);
   }
   virtual void VisitIfStmt(IfStmt * ifstmt) {
	   // no mEnv->handle? setPC?
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   Expr *condition = ifstmt->getCond();
	   if(mEnv->getExpr(condition))
	   {
		   Visit(ifstmt->getThen());
	   }
	   else {
		   if(ifstmt->getElse())
		   {
			   Visit(ifstmt->getElse());
		   }
	   }
   }
   virtual void VisitWhileStmt(WhileStmt * wstmt) {
	   // no mEnv->handle?
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   Expr* condition = wstmt->getCond();
	   while(mEnv->getExpr(condition))
	   {
		   Visit(wstmt->getBody());
	   }
   }
   virtual void VisitForStmt(ForStmt * fstmt) {
	   // no mEnv->handle?
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   Stmt* finit = fstmt->getInit();
	   Stmt* finc = fstmt->getInc();
	   if(finit)
			Visit(finit);
	   Expr* condition = fstmt->getCond();
	   for(;mEnv->getExpr(condition); Visit(finc))
	   {
		   Visit(fstmt->getBody());
	   }
   }
   virtual void VisitIntegerLiteral(IntegerLiteral *intlt) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(intlt);
	   mEnv->intlt(intlt);
   }
   virtual void VisitCharacterLiteral(CharacterLiteral *charlt) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(charlt);
	   mEnv->chlt(charlt);
   }
   virtual void VisitReturnStmt(ReturnStmt *rstmt) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(rstmt);
	   mEnv->rstmt(rstmt);
   }
   virtual void VisitArraySubscriptExpr(ArraySubscriptExpr *ase) {
	   VisitStmt(ase);
	   mEnv->arrayse(ase);
   }
   virtual void VisitUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr * uette) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(uette);
	   mEnv->unaryOrtt(uette);
   }
   virtual void VisitParenExpr(ParenExpr * pe) {
	   if(mEnv->getCurrentStack()->isRetState())
		   return;
	   VisitStmt(pe);
	   mEnv->parene(pe);
   }
 
private:
   Environment * mEnv;
};

class InterpreterConsumer : public ASTConsumer {
public:
   explicit InterpreterConsumer(const ASTContext& context) : mEnv(),
   	   mVisitor(context, &mEnv) {
   }
   virtual ~InterpreterConsumer() {}

   /*
	ParseAST(Sema &S)
	{
		...
		ASTConsumer *Consumer = &S.getASTConsumer();
		std::unique_ptr<Parse> ParseOP(
			new Parse(S.getPreprocessor(), S, SkipFunctionBodies));
		Parse &P = *ParseOP.get();
		...
		for(bool AtEOF = P.ParseFirstTopLevelDecl(ADecl); !AtEOF; 
			AtEOF = P.ParseTopLevelDecl(ADecl)){
			if (ADecl && !Consumer->HandleTopLevelDecl(ADecl.get()))
				return;
		}
		for (Decl *D : S.WeakTopLevelDecls())
			Consumer->HandleTopLevelDecl(DeclGroupRef(D));

		Consumer->HandleTranslationUnit(S.getASTContext());
		...
	}
	*/
   virtual void HandleTranslationUnit(clang::ASTContext &Context) {
	   TranslationUnitDecl * decl = Context.getTranslationUnitDecl();
	   mEnv.init(decl);

	   FunctionDecl * entry = mEnv.getEntry();
	   mVisitor.VisitStmt(entry->getBody());
  }
private:
   Environment mEnv;
   InterpreterVisitor mVisitor;
};

class InterpreterClassAction : public ASTFrontendAction {
public: 
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new InterpreterConsumer(Compiler.getASTContext()));
  }
};

int main (int argc, char ** argv) {
   if (argc > 1) {
       clang::tooling::runToolOnCode(std::unique_ptr<clang::FrontendAction>(new InterpreterClassAction), argv[1]);
   }
}
