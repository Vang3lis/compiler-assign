//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool --------------===//
//===----------------------------------------------------------------------===//
#include <stdio.h>
#include <utility>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

class StackFrame {
   /// StackFrame maps Variable Declaration to Value
   /// Which are either integer or addresses (also represented using an Integer value)
   std::map<Decl*, int64_t> mVars;
   std::map<Stmt*, int64_t> mExprs;
   /// The current stmt
   Stmt * mPC;
   bool mretflag = false;
   int64_t mretval;
public:
   StackFrame() : mVars(), mExprs(), mPC() {
   }

   void bindDecl(Decl* decl, int64_t val) {
      mVars[decl] = val;
   }    
   int64_t getDeclVal(Decl * decl) {
      assert (mVars.find(decl) != mVars.end());
      return mVars.find(decl)->second;
   }
   void bindStmt(Stmt * stmt, int64_t val) {
	   mExprs[stmt] = val;
   }
   int64_t getStmtVal(Stmt * stmt) {
	   assert (mExprs.find(stmt) != mExprs.end());
	   return mExprs[stmt];
   }
   void setPC(Stmt * stmt) {
	   mPC = stmt;
   }
   Stmt * getPC() {
	   return mPC;
   }
   bool declExits(Decl * decl)
   {
	   return mVars.find(decl) != mVars.end();
   }
   bool exprExits(Stmt * stmt)
   {
	   return mExprs.find(stmt) != mExprs.end();
   }
   void setRetVal(int64_t val)
   {
	   mretflag = true;
	   mretval = val;
   }
   bool hasRetVal()
   {
	   return mretflag;
   }
   int64_t getRetVal()
   {
	   return mretval; 
   }
   bool isRetState()
   {
	   return mretflag;
   }
};

/// Heap maps address to a value
class Heap {
	// addr->size 
	std::map<int64_t, int64_t> mChunks;
	// offset->value int8_t
	std::map<int64_t, int8_t> mContents;
public:
	Heap(): mChunks(), mContents(){}
	int64_t Malloc(int64_t size)
	{
		int64_t *ptr = (int64_t *) std::malloc(size);
		
		mChunks.insert(std::make_pair((int64_t)ptr, size));
		for(int64_t i = 0; i < size; i++)
			mContents.insert(std::make_pair((int64_t)(ptr+1), 0));
		return (int64_t)ptr;
	}
	void Free(int64_t addr)
	{
		assert(mChunks.find(addr) != mChunks.end());
		int64_t * ptr = (int64_t *)addr;
		int64_t size = mChunks.find(addr)->second;
		mChunks.erase(mChunks.find(addr));

		for(int64_t i = 0; i < size; i++)
		{
			assert(mContents.find((int64_t)(ptr+i)) != mContents.end());
			mContents.erase((int64_t)(ptr+i));
		}
		std::free(ptr);
	}

	void UpdateInt8(int64_t addr, int8_t val)
	{
		assert(mContents.find(addr) != mContents.end());
		mContents[addr] = val;
	}
	void UpdateInt64(int64_t addr, int64_t val)
	{
		for(int i = 0; i < 8; i++)
		{
			UpdateInt8(addr, val&0xff);
			val >>= 8;
		}
	}
	int8_t GetInt8(int64_t addr)
	{
		assert(mContents.find(addr) != mContents.end());
		return mContents.find(addr)->second;
	}
	int64_t GetInt64(int64_t addr)
	{
		int64_t val = 0;
		for(int i = 0; i < 8; i++)
			val += (GetInt8(addr+i))<<(i*8);
		return val;
	}
};

class Environment {
   std::vector<StackFrame> mStack;

   FunctionDecl * mFree;				/// Declartions to the built-in functions
   FunctionDecl * mMalloc;
   FunctionDecl * mInput;
   FunctionDecl * mOutput;

   FunctionDecl * mEntry;
public:
   /// Get the declartions to the built-in functions
   Environment() : mStack(), mFree(NULL), mMalloc(NULL), mInput(NULL), mOutput(NULL), mEntry(NULL) {
   }

   void popStack() {
	   mStack.pop_back();
   }
   StackFrame* getCurrentStack() {
	   return &(mStack.back()); 
   }
   int64_t getStackDeclVal(Decl * decl) {
	   StackFrame globalStack = mStack.front();
	   StackFrame currentStack = mStack.back();
	   if(currentStack.declExits(decl))
		   return currentStack.getDeclVal(decl);
	   else
		   return globalStack.getDeclVal(decl);
   }

   /// Initialize the Environment
   void init(TranslationUnitDecl * unit) {
	   mStack.push_back(StackFrame());
	   for (TranslationUnitDecl::decl_iterator i =unit->decls_begin(), e = unit->decls_end(); i != e; ++ i) {
		   if (FunctionDecl * fdecl = dyn_cast<FunctionDecl>(*i) ) {
			   if (fdecl->getName().equals("FREE")) mFree = fdecl;
			   else if (fdecl->getName().equals("MALLOC")) mMalloc = fdecl;
			   else if (fdecl->getName().equals("GET")) mInput = fdecl;
			   else if (fdecl->getName().equals("PRINT")) mOutput = fdecl;
			   else if (fdecl->getName().equals("main")) mEntry = fdecl;
		   }
		   else {
			   if(VarDecl *vardecl = dyn_cast<VarDecl>(*i))
			   {
				   // global var
				   if(vardecl->getType().getTypePtr()->isIntegerType() || 
						   vardecl->getType().getTypePtr()->isCharType() || 
						   vardecl->getType().getTypePtr()->isPointerType())
				   {
					   if(vardecl->hasInit())
							mStack.back().bindDecl(vardecl, getExpr(vardecl->getInit()));
					   else
							mStack.back().bindDecl(vardecl, 0);    
				   }
			   }
		   }
	   }
	   mStack.push_back(StackFrame());
   }

   FunctionDecl * getEntry() {
	   return mEntry;
   }

   /// !TODO Support comparison operation
   void binop(BinaryOperator *bop) {
	   Expr * left = bop->getLHS();
	   Expr * right = bop->getRHS();

	   if (bop->isAssignmentOp()) {
		   if (DeclRefExpr * declexpr = dyn_cast<DeclRefExpr>(left)) {
			   int64_t val = mStack.back().getStmtVal(right);
			   mStack.back().bindStmt(left, val);
			   Decl * decl = declexpr->getFoundDecl();
			   mStack.back().bindDecl(decl, val);
		   } else if (auto arrayse = dyn_cast<ArraySubscriptExpr>(left)) {
			   if(auto drf = dyn_cast<DeclRefExpr>(arrayse->getLHS()->IgnoreImpCasts()))
			   {
				   Decl * decl = drf->getFoundDecl();
				   if(VarDecl * vardecl = dyn_cast<VarDecl>(decl))
				   {
					   if(auto array = dyn_cast<ConstantArrayType>(vardecl->getType().getTypePtr()))
					   {
						   void * ptr = (void *)mStack.back().getStmtVal(arrayse->getBase());
						   int idx = mStack.back().getStmtVal(arrayse->getIdx());
						   int64_t val = mStack.back().getStmtVal(right);
						   printf("%p: %d %ld\n", ptr, idx, val);
						   if (array->getElementType().getTypePtr()->isIntegerType())
							   *((int64_t *)ptr+idx) = val;
						   else if (array->getElementType().getTypePtr()->isCharType())
							   *((char *)ptr+idx) = (char)val;
						   else
							   *((int64_t *)ptr+idx) = val;
					   }
					   else {
						   /* char *a;
							* a = (char*)malloc(2*sizeof(char));
							* a[0] = 1;
							* a[1] = 2;
							* */
						   // TODO: find the above case belonging to which type
						   void * ptr = (void *)mStack.back().getStmtVal(arrayse->getBase());
						   int idx = mStack.back().getStmtVal(arrayse->getIdx());
						   int64_t val = mStack.back().getStmtVal(right);
						   printf("%p: %d %ld\n", ptr, idx, val);
						   *((int64_t *)ptr+idx) = val;
					   }
					   /*
					   if(vardecl->getType()->isIntegerType())
						   puts("int");
					   else if(vardecl->getType()->isCharType())
						   puts("char");
					   else if(vardecl->getType()->isPointerType())
						   puts("pointer");
					   else 
						   puts("unkown");
						*/
				   }
			   }
		   } else if (auto unaryop = dyn_cast<UnaryOperator>(left)) {
			   int64_t ptr = mStack.back().getStmtVal(unaryop->getSubExpr());
			   int64_t val = mStack.back().getStmtVal(right);
			   *(int64_t *)ptr = val;
		   } else {
		   }
	   }
	   // add op 
	   else {
			int64_t op = bop->getOpcode();
			int64_t result = 0;
			
			switch(op)
			{
				// + - * / < > == default
				case BO_Add:
					if(left->getType().getTypePtr()->isPointerType())
					{
						int64_t ptr = mStack.back().getStmtVal(left);
						result = ptr + 8 * getExpr(right);
					}
					else 
						result = getExpr(left) + getExpr(right);
					break;
				case BO_Sub:
						result = getExpr(left) - getExpr(right);
					break;
				case BO_Mul:
					result = getExpr(left) * getExpr(right);
					break;
				case BO_Div:
					if(getExpr(right) == 0)
					{
						llvm::errs() << "div 0 errs\n";
						exit(0);
					}
					result = getExpr(left) / getExpr(right);
					break;
				case BO_LT:
					result = getExpr(left) < getExpr(right);
					break;
				case BO_GT:
					result = getExpr(left) > getExpr(right);
					break;
				case BO_EQ:
					result = getExpr(left)==getExpr(right);
					break;
				default:
					llvm::errs() << "can not process this Op\n";
					exit(0);
					break;
			}
			// if(mStack.back().exprExits(bop))
			mStack.back().bindStmt(bop, result);
	   }
   }

   void unaryop(UnaryOperator * uop) {
	   Expr* expr = uop->getSubExpr();
	   switch(uop->getOpcode())
	   {
		   case UO_Minus:
			   mStack.back().bindStmt(uop, -1*(getExpr(expr)));
			   break;
		   case UO_Plus:
			   mStack.back().bindStmt(uop, getExpr(expr));
			   break;
		   case UO_Deref:
			   mStack.back().bindStmt(uop, *(int64_t*)getExpr(expr));
			   // mStack.back().bindStmt(uop, *(int64_t*)mStack.back().getStmtVal(expr));
			   break;
		   default:
			   llvm::errs() << "can not process this UOp\n";
			   exit(0);
			   break;
	   }
   }

   void decl(DeclStmt * declstmt) {
	   for (DeclStmt::decl_iterator it = declstmt->decl_begin(), ie = declstmt->decl_end();
			   it != ie; ++ it) {
		   Decl * decl = *it;
		   if (VarDecl * vardecl = dyn_cast<VarDecl>(decl)) {
			   if(vardecl->getType().getTypePtr()->isIntegerType() || 
					   vardecl->getType().getTypePtr()->isCharType() || 
					   vardecl->getType().getTypePtr()->isPointerType()) {
				   if(vardecl->hasInit())
				   {
					   // mStack.back().bindDecl(vardecl, getExpr(vardecl->getInit()));
					   int64_t value = mStack.back().getStmtVal(vardecl->getInit());
					   mStack.back().bindDecl(vardecl, value);
				   }
				   else
					   mStack.back().bindDecl(vardecl, 0);
			   } 
			   else if(vardecl->getType().getTypePtr()->isConstantArrayType()) {
				   auto carray = dyn_cast<ConstantArrayType>(vardecl->getType().getTypePtr());
				   int64_t size = carray->getSize().getSExtValue();
				   // QualType
				   // the element type of the array
				   auto element = carray->getElementType();
				   if(element.getTypePtr()->isIntegerType()){
					   int64_t *var_array = new int64_t[size];
					   for(int i = 0; i < size; i++)
						   var_array[i] = 0;
					   mStack.back().bindDecl(vardecl, (int64_t)var_array);
				   } else if(element.getTypePtr()->isCharType()) {
					   char *var_array = new char[size];
					   for(int i = 0; i < size; i++)
						   var_array[i] = 0;
					   mStack.back().bindDecl(vardecl, (int64_t)var_array);
				   } else if(element.getTypePtr()->isPointerType()) {
					   int64_t **var_array = new int64_t *[size];
					   for(int i = 0; i < size; i++)
						   var_array[i] = 0;
					   mStack.back().bindDecl(vardecl, (int64_t)var_array);
				   } else {
					   exit(0);
				   }
			   }
		   }
	   }
   }
   void declref(DeclRefExpr * declref) {
	   mStack.back().setPC(declref);
	   if (declref->getType()->isIntegerType() ||
			   declref->getType()->isCharType() || 
			   declref->getType()->isPointerType()) { 
		   Decl * decl = declref->getFoundDecl();
		   int64_t val = getStackDeclVal(decl);
		   mStack.back().bindStmt(declref, val);
	   } else if (declref->getType()->isArrayType()) {
		   Decl * decl = declref->getFoundDecl();
		   int64_t val = getStackDeclVal(decl);
		   mStack.back().bindStmt(declref, val);
	   } else {
	   }
   }

   void cast(CastExpr * castexpr) {
	   mStack.back().setPC(castexpr);
	   if (castexpr->getType()->isIntegerType()) {
		   Expr * expr = castexpr->getSubExpr();
		   int64_t val = mStack.back().getStmtVal(expr);
		   mStack.back().bindStmt(castexpr, val);
	   } else if (castexpr->getType()->isPointerType()) {
		   if ( castexpr->getCastKind() == CK_LValueToRValue || 
				   castexpr->getCastKind() == CK_ArrayToPointerDecay || 
				   castexpr->getCastKind() == CK_PointerToIntegral || 
				   castexpr->getCastKind() == CK_BitCast)
		   {
			   Expr * expr = castexpr->getSubExpr();
			   int64_t val = mStack.back().getStmtVal(expr);
			   mStack.back().bindStmt(castexpr, val);
		   }
	   }
	   else { 
	   }
   }

   /// !TODO Support Function Call
   void call(CallExpr * callexpr) {
	   mStack.back().setPC(callexpr);
	   int64_t val = 0;
	   FunctionDecl * callee = callexpr->getDirectCallee();
	   if (callee == mInput) {
		   llvm::errs() << "Please Input an Integer Value : ";
		   scanf("%ld", &val);
		   mStack.back().bindStmt(callexpr, val);
	   } else if (callee == mOutput) {
		   Expr * decl = callexpr->getArg(0);
		   val = mStack.back().getStmtVal(decl);
		   /*if(auto array = dyn_cast<ArraySubscriptExpr>(decl->IgnoreImpCasts()))
		   {
			   llvm::errs() << *(int64_t*)val << "\n";
		   }
		   else {
			   llvm::errs() << val << "\n";
		   }*/
		   llvm::errs() << val << "\n";
	   } else if (callee == mMalloc) {
		   // int64_t size = getExpr(callexpr->getArg(0));
		   int64_t size = mStack.back().getStmtVal(callexpr->getArg(0));
		   int64_t *ptr = (int64_t *)std::malloc(size);
		   mStack.back().bindStmt(callexpr, (int64_t)ptr);
	   } else if (callee == mFree) {
		   std::free((int64_t *)getExpr(callexpr->getArg(0)));
	   }
	   else {
		   std::vector<int64_t> args;
		   for(auto item = callexpr->arg_begin(), end = callexpr->arg_end();
				   item != end; item += 1)
			   args.push_back(getExpr(*item));
		   mStack.push_back(StackFrame());
		   int64_t idx = 0;
		   for(auto item = callee->param_begin(), end = callee->param_end();
				   item != end; item += 1, idx += 1 )
			   mStack.back().bindDecl(*item, args[idx]);
	   }
   }

   void intlt(IntegerLiteral * intlt) {
	   // llvm::APint intlt->getValue()
	   mStack.back().bindStmt(intlt, intlt->getValue().getSExtValue());
   }

   void chlt(CharacterLiteral * charlt) {
	   mStack.back().bindStmt(charlt, charlt->getValue());
   }

   void rstmt(ReturnStmt * rstmt) {
	   int64_t value = mStack.back().getStmtVal(rstmt->getRetValue());
	   mStack.back().setRetVal(value);
   }

   void arrayse(ArraySubscriptExpr * ase) {
	   int64_t *array = (int64_t *)mStack.back().getStmtVal(ase->getBase());
	   int idx = mStack.back().getStmtVal(ase->getIdx());
	   mStack.back().bindStmt(ase, array[idx]);
   }

   void unaryOrtt(UnaryExprOrTypeTraitExpr * uette) {
	   if(auto sizeofexpr = dyn_cast<UnaryExprOrTypeTraitExpr>(uette))
	   {
		   if (sizeofexpr->getKind() == UETT_SizeOf)
		   {
			   if(sizeofexpr->getArgumentType()->isIntegerType() || 
					   sizeofexpr->getArgumentType()->isPointerType())
				   mStack.back().bindStmt(uette, 8);
		   }
	   }
   }

   void parene(ParenExpr * pe) {
	   Expr * expr = pe->getSubExpr();
	   int64_t value = mStack.back().getStmtVal(expr);
	   mStack.back().bindStmt(pe, value);
   }

   int64_t getExpr(Expr* expr)
   {
	   expr = expr->IgnoreImpCasts();
	   if(auto intlt = dyn_cast<IntegerLiteral>(expr))
		   return intlt->getValue().getSExtValue();
	   else if(auto charlt = dyn_cast<CharacterLiteral>(expr))
		   return charlt->getValue();
	   else if(auto declref = dyn_cast<DeclRefExpr>(expr))
		   return getStackDeclVal(declref->getDecl());
	   else if(auto bop = dyn_cast<BinaryOperator>(expr)) {
		   binop(bop);
		   return mStack.back().getStmtVal(bop);
	   }
	   else if(auto uop = dyn_cast<UnaryOperator>(expr)) {
		   unaryop(uop);
		   return mStack.back().getStmtVal(uop);
	   }
	   else if(auto call = dyn_cast<CallExpr>(expr))
		   return mStack.back().getStmtVal(call);
	   else 
	   {
		   return mStack.back().getStmtVal(expr);
	   }
   }
};


