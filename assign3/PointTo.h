//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "Dataflow.h"
using namespace llvm;

using ValueSet = std::unordered_set<Value *>;
using FunctionSet = std::unordered_set<Function *>;
using PointToMap = std::unordered_map<Value*, ValueSet>;


struct CallInstCmp
{
	bool operator()(const CallInst *lhs, const CallInst *rhs)
	{
		return (lhs->getDebugLoc().getLine() < rhs->getDebugLoc().getLine());
	}
};

struct PointToState {
   // map: value:{ value, value, struct_base_value ... }  no struct
   PointToMap pt;
   // map: struct_base_value:{ struct } 
   PointToMap field_pt;
   bool init_flag = false;
   PointToState() : pt(), field_pt() {}
   PointToState(const PointToState & other)
           : pt(other.pt), field_pt(other.field_pt) {}

   bool operator == (const PointToState & other) const {
	   return (pt == other.pt) && (field_pt == other.field_pt);
   }

   bool operator != (const PointToState & other) const {
	   return (pt != other.pt) || (field_pt != other.field_pt);
   }

   PointToState &operator = (const PointToState & other) {
	   pt = other.pt;
	   field_pt = other.field_pt;
	   return *this;
   }
};

inline raw_ostream &operator<<(raw_ostream &out, const PointToMap &pt)
{
	out << "{ ";
	for(auto i = pt.begin(), e = pt.end(); i != e; i++)
	{
		out << i->first->getName() << " " << i->first << " -> ";
		out << "( ";
		for(auto si = i->second.begin(), se = i->second.end(); si != se; si++)
		{
			if(si != i->second.begin())
				errs() << ", ";
			out << (*si)->getName() << " " << (*si);
		}
		out << " ) | ";
	}
	out << "}";
	return out;
}

inline raw_ostream &operator<<(raw_ostream &out, const PointToState &state) 
{
	out << "pt  : " << state.pt << "\n";
	out << "fpt : " << state.field_pt << "\n";
	return out;
}
	
class PointToVisitor : public DataflowVisitor<struct PointToState> {
public:
   FunctionSet func_set;
   // ci -> callee set
   std::map<CallInst *, FunctionSet, CallInstCmp> call_return;
   // result[callinst] -> in state(PASS ALL PT/FPT TO CALLEE) | out state (PASS ALL BACK + RETVAL)
   DataflowInstResult<PointToState>::Type *instresult;
   //
   DataflowBBResult<PointToState>::Type *bbresult;

   PointToVisitor(): func_set(), call_return(), instresult(), bbresult() {}

   // merge(dest, src) => dest 
   void merge(PointToState * dest, const PointToState & src) override {
	   // dest map value->{} = dest map value->A{} or src map value->B{}
	   for(auto pti = src.pt.begin(), pte = src.pt.end();
			   pti != pte; pti++)
	   {
		   dest->pt[pti->first].insert(pti->second.begin(), pti->second.end());
	   }
	   // dest map value=>{} = dest map value=>A{} or src map value=>B{}
	   for(auto fpti = src.field_pt.begin(), fpte = src.field_pt.end();
			   fpti != fpte; fpti++)
	   {
		   dest->field_pt[fpti->first].insert(fpti->second.begin(), fpti->second.end());
	   }
   }

   // Instructions are in the <llvm/IR/Instructions.h>
   void compDFVal(Instruction *inst, PointToState * state) override {
	   // errs() << "op:\n";
	   // for(auto io = inst->op_begin(), ie = inst->op_end(); io != ie; io++)
		   // errs() << *io << "\n";
	   // errs() << "user:\n";
	   // for(auto iu = inst->user_begin(), ie = inst->user_end(); iu != ie; iu++)
		   // iu->dump();
	   // errs() << "\n";
	   // errs() << *inst->getOperandList() << "\n";

	   if(isa<IntrinsicInst>(inst))
	   {
		   // MemCpyInst: wrap the llvm.memcpy intrinsic
		   if(auto *mci = dyn_cast<MemCpyInst>(inst))
			   handleMemCpyInst(mci, state);
	   }
	   else if(auto *phi = dyn_cast<PHINode>(inst))
		   handlePHINode(phi, state);


	   // StoreInst: store to memory
	   else if(auto *si = dyn_cast<StoreInst>(inst))
		   handleStoreInst(si, state);


	   // LoadInst: read from memory
	   else if(auto *li = dyn_cast<LoadInst>(inst))
		   handleLoadInst(li, state);

	   else if(auto *gep = dyn_cast<GetElementPtrInst>(inst))
		   handleGetElementPtrInst(gep, state);

	   // CallInst: a function call
	   else if(auto *ci = dyn_cast<CallInst>(inst))
		   handleCallInst(ci, state);
	   else if(auto *ri = dyn_cast<ReturnInst>(inst))
		   handleReturnInst(ri, state);

	   // BitCastInst: a no-op cast from one type to another
	   // else if(auto *bci = dyn_cast<BitCastInst>(inst))
		   // handleBitCastInst(bci, state);
	   else {
		   // errs() << "TODO: support more IR \n";
		   // inst->dump();
	   }
	   // errs() << "state:\n" << *state << "\n";
   }

   void handleMemCpyInst(MemCpyInst *mci, PointToState *state)
   {
	   // llvm/IR/IntrinsicInst.h MemCpyInst 
	   // BaseCL: getArgOperand(): return the arguments to the instruction
	   // errs() << "handleMemCpyInst\n";

	   auto *bci_dst = dyn_cast<BitCastInst>(mci->getArgOperand(0));
	   auto *bci_src = dyn_cast<BitCastInst>(mci->getArgOperand(1));

	   if(!bci_dst || !bci_src)
		   return;

	   Value *dst = bci_dst->getOperand(0);
	   Value *src = bci_src->getOperand(0);
	
	   ValueSet src_pt = state->pt[src];
	   ValueSet src_fpt = state->field_pt[src];

	   // dst pt/fpt = src pt/fpt
	   state->pt[dst].clear();
	   state->pt[dst].insert(src_pt.begin(), src_pt.end());
	   state->field_pt[dst].clear();
	   state->field_pt[dst].insert(src_fpt.begin(), src_fpt.end());
   }

   void handlePHINode(PHINode *phi, PointToState *state)
   {
	   // errs() << "handlePHINode\n";

	   state->pt[phi].clear();
	   for(Value *value: phi->incoming_values())
	   {
		   if(isa<ConstantPointerNull>(value))
			   continue;
		   if(isa<Function>(value))
			   state->pt[phi].insert(value);
		   else {
			   if(!state->pt.count(value))
				   state->pt[phi].insert(value);
			   else {
				   ValueSet add_set = state->pt[value];
				   state->pt[phi].insert(add_set.begin(), add_set.end());
			   }
		   }
	   }
   }

   void handleStoreInst(StoreInst *si, PointToState *state)
   {
	   // getOperand(0): getValueOperand()
	   // getOperand(1): getPointerOperand()

	   // errs() << "handleStoreInst\n";
	   // getchar();

	   // errs() << *si->getValueOperand() << "|" << *si->getPointerOperand() << "\n";
	   Value *ptr_value = si->getValueOperand();
	   Value *ptr_addr = si->getPointerOperand();

	   // errs() << "value | addr \n";
	   // errs() << ptr_value->getName() << " " << ptr_value << "\n";
	   // errs() << ptr_addr->getName() << " " << ptr_addr << "\n";

	   ValueSet overwrite_pt;

	   if(state->pt[ptr_value].empty())
	   {
		   // if(ptr_value->hasName())
		   state->pt.erase(ptr_value);
		   overwrite_pt.insert(ptr_value);
	   }
	   else{
		   ValueSet pts = state->pt[ptr_value];
		   overwrite_pt.insert(pts.begin(), pts.end());
	   }
		  
	   // for(auto i = overwrite_pt.begin(), e = overwrite_pt.end(); i != e; i++)
		   // errs() << (*i)->getName() << " " << *i << "\n";
	   // errs() << "end\n";

	   if(auto *gep = dyn_cast<GetElementPtrInst>(ptr_addr))
	   {
		   // errs() << "TODO Store: support pointer addr is GetElementPtrInst\n";
		   // getchar();

		   if(state->pt[gep->getPointerOperand()].empty())
		   {
			   state->pt.erase(gep->getPointerOperand());
			   state->field_pt[gep->getPointerOperand()].clear();
			   state->field_pt[gep->getPointerOperand()].insert(overwrite_pt.begin(),
															overwrite_pt.end());
		   }
		   else {
			   // find all base fpt
			   ValueSet base_fpt_set = state->pt[gep->getPointerOperand()];

			   for(auto bfpt_i = base_fpt_set.begin(), bfpt_e = base_fpt_set.end();
					   bfpt_i != bfpt_e; bfpt_i++)
			   {
				   Value *bfpt = *bfpt_i;
				   state->field_pt[bfpt].clear();
				   state->field_pt[bfpt].insert(overwrite_pt.begin(), overwrite_pt.end());
			   }
		   }
	   }
	   else {
		   state->pt[ptr_addr].clear();
		   state->pt[ptr_addr].insert(overwrite_pt.begin(), overwrite_pt.end());
	   }
   }

   void handleLoadInst(LoadInst *li, PointToState *state)
   {
	   // getOperand(0): getPointerOperand()
	   
	   // errs() << "handleLoadInst\n";

	   // errs() << *li->getPointerOperand() << "\n";
	   Value *ptr_addr = li->getPointerOperand();

	   state->pt[li].clear();
	   if(auto gep = dyn_cast<GetElementPtrInst>(ptr_addr))
	   {
		   // errs() << "TODO Load: support pointer addr is GetElementPtrInst\n";
		   // getchar();

		   if(state->pt[gep->getPointerOperand()].empty())
		   {
			   state->pt.erase(gep->getPointerOperand());
			   ValueSet content_pt = state->field_pt[gep->getPointerOperand()];
			   state->pt[li].insert(content_pt.begin(), content_pt.end());
		   }
		   else {
			   ValueSet base_fpt_set = state->pt[gep->getPointerOperand()];
			   for(auto bfpt_i = base_fpt_set.begin(), bfpt_e = base_fpt_set.end();
					   bfpt_i != bfpt_e; bfpt_i++)
			   {
				   Value *bfpt = *bfpt_i;
				   ValueSet content_pt = state->field_pt[bfpt];
				   state->pt[li].insert(content_pt.begin(), content_pt.end());
			   }
		   }
	   }
	   else {
		   ValueSet add_pt = state->pt[ptr_addr];
		   state->pt[li].insert(add_pt.begin(), add_pt.end());
	   }
   }

   void handleGetElementPtrInst(GetElementPtrInst *gep, PointToState *state)
   {
	   // getOperand(0): getPointerOperand()

	   // errs() << "handleGetElementPtrInst\n";
	   // getchar();

	   // overwrite 
	   state->pt[gep].clear();
	   if(state->pt[gep->getPointerOperand()].empty())
	   {
		   state->pt.erase(gep->getPointerOperand()); 
		   state->pt[gep].insert(gep->getPointerOperand());
	   }
	   else
		   state->pt[gep].insert(state->pt[gep->getPointerOperand()].begin(),
								state->pt[gep->getPointerOperand()].end());
   }

   // in_state  ----handle----> out_state
   // state merge instresult[ci] instate
   // state is divided into two parts: arg_map part | except arg_map part
   // 1. arg_map part ---caller_arg map to callee_arg---> add into callee first node
   // 2. except arg_map part merge with instresult[ci] outstate
   // 
   // so:
   // Step 1: state merge instresult[ci] instate
   // Step 2: for callee: transform argument (MUST PASS ALL THE PT/FPT !!!!!)
   // Step 3: state merge instresult[ci] outstate
   void handleCallInst(CallInst *ci, PointToState *state)
   {
	   // llvm/IR/InstrTypes.h CallBase: CallInst InvokeInst
	   // All call-like instructions are required to use a common operand layout:
	   // - Zero or more arguments to the call,
	   // - Zero or more operand bundles with zero or more operand inputs each bundle,
	   // - Zero or more subclass controlled operands
	   // - The called function.
	   // 
	   // arg_begin() arg_end()
	   // getNumArgOperands()
	   // getArgOperand(unsigned i)
	   // getCalledFunction()
	   // getCalledOperand()
	   // 
	   // at /usr/local/llvm/include/llvm/IR/InstrTypes.h:1298
	   // 1296   // DEPRECATED: This routine will be removed in favor of `getCalledOperand` in
	   // 1297   // the near future.
	   // 1298   Value *getCalledValue() const { return getCalledOperand();  }
	   //
	   // errs() << "handleCallInst\n";

	   FunctionSet callee_set = getFunctions(ci->getCalledOperand(), state);

	   // call_return[ci].clear();
	   // if insert the same, will be not able to insert
	   call_return[ci].insert(callee_set.begin(), callee_set.end());

	   // if the function is declaration, it will be handled in normal cfg
	   if(ci->getCalledFunction() && ci->getCalledFunction()->isDeclaration())
		   return;

	   // Step 1:
	   PointToState initval;
	   // initalize the result[ci]
	   instresult->insert(std::make_pair(ci, std::make_pair(initval, initval)));

	   PointToState old_instate = (*instresult)[ci].first;
	   merge(&old_instate, *state);

	   // Step 2:
	   for(auto i = callee_set.begin(), e = callee_set.end(); i != e; i++)
	   {
		   Function *callee = *i;
		   // errs() << callee->getName() << "\n";
		   if(callee->isDeclaration())
			   continue;

		   PointToState tmp_state = *state;
		   // caller arg => callee arg
		   std::map<Value *, Argument *> arg_map;
		   unsigned int arg_num = ci->getNumArgOperands();
		   for(unsigned int arg_i = 0; arg_i < arg_num; arg_i++)
		   {
			   Value *caller_arg = ci->getArgOperand(arg_i);
			   if(!caller_arg->getType()->isPointerTy())
				   continue;

			   Argument *callee_arg = callee->arg_begin() + arg_i;
			   arg_map.insert(std::make_pair(caller_arg, callee_arg));
			   // errs() << "arg map: " << caller_arg->getName() << " > " << callee_arg->getName() << "\n";
		   }

		

		   // errs() << tmp_state << "\n";
		   // errs() << "transform in arg\n";
		   // traverse tmp_state: replace caller_arg_1 (caller_arg_0->{ caller_arg_1 }) with callee_arg
		   for(auto arg_map_i = arg_map.begin(), arg_map_e = arg_map.end();
				   arg_map_i != arg_map_e; arg_map_i++)
		   {
			   Value *caller_arg = arg_map_i->first;
			   Argument *callee_arg = arg_map_i->second;

			   for(auto pi = tmp_state.pt.begin(), pe = tmp_state.pt.end();
					   pi != pe; pi++)
			   {
				   if(pi->second.count(caller_arg) && !isa<Function>(caller_arg))
				   {

					   pi->second.erase(caller_arg);
					   pi->second.insert(callee_arg);
				   }
			   }

			   for(auto fpi = tmp_state.field_pt.begin(), fpe = tmp_state.field_pt.end();
					   fpi != fpe; fpi++)
			   {
				   if(fpi->second.count(caller_arg) && !isa<Function>(caller_arg))
				   {
					   fpi->second.erase(caller_arg);
					   fpi->second.insert(callee_arg);
				   }
			   }
		   }
		   // errs() << tmp_state << "\n";

		   // callee_state: transform caller_arg (caller_arg->{}) to callee_arg
		   for(auto arg_map_i = arg_map.begin(), arg_map_e = arg_map.end(); 
				   arg_map_i != arg_map_e; arg_map_i++)
		   {
			   Value *caller_arg = arg_map_i->first;
			   Argument *callee_arg = arg_map_i->second;
			   if(tmp_state.pt.count(caller_arg))
			   {
				  // callee_node_in.pt[callee_arg].clear();
				  ValueSet tmp_fp_vs = tmp_state.pt[caller_arg];
				  tmp_state.pt.erase(caller_arg);
				  tmp_state.pt[callee_arg].insert(tmp_fp_vs.begin(), tmp_fp_vs.end());
			   }

			   if(tmp_state.field_pt.count(caller_arg))
			   {
				   ValueSet tmp_ftp_vs = tmp_state.field_pt[caller_arg];
				   tmp_state.field_pt.erase(caller_arg);
				   tmp_state.field_pt[callee_arg].insert(tmp_ftp_vs.begin(), tmp_ftp_vs.end());
			   }
		   }
		   for(auto arg_map_i = arg_map.begin(), arg_map_e = arg_map.end();
				   arg_map_i != arg_map_e; arg_map_i++)
		   {
			   // foo(plus, %0, %1) => foo(%ptr, %a, %b)
			   if(isa<Function>(arg_map_i->first))
				   tmp_state.pt[arg_map_i->second].insert(arg_map_i->first);
		   }

		   PointToState &callee_node_in = (*bbresult)[&*callee->begin()].first;
		   PointToState old_callee_node_in = callee_node_in;
		   
		   merge(&callee_node_in, tmp_state);
		   // stop dataflow
		   if(old_callee_node_in != callee_node_in)
		   {
			   func_set.insert(callee);
			   // errs() << "callinst add into list : " << callee->getName() << "\n";
		   }
		   // errs() << callee_node_in << "\n";

	   }

	   // Step 3:
	   // instresult[ci] outstate overwrite state's pt/fpt
	   *state = (*instresult)[ci].second;

   }

   void handleReturnInst(ReturnInst *ri, PointToState *state)
   {
	   // errs() << "handleReturnInst\n";
	   // errs() << *state << "\n";

	   Function *callee = ri->getFunction();
	   for(auto cri = call_return.begin(), cre = call_return.end(); 
			   cri != cre; cri++)
	   {
		   PointToState tmp_state = *state;
		   // call_return: CallInst : FunctionSet
		   if(cri->second.count(callee))
		   {
			   CallInst *ci = cri->first;
			   Function *caller = ci->getFunction();

			   std::map<Argument *, Value *> reverse_arg_map;
			   unsigned int arg_num = ci->getNumArgOperands();
			   for(unsigned int arg_i = 0; arg_i < arg_num; arg_i++)
			   {
				   Value *caller_arg = ci->getArgOperand(arg_i);
				   if(!caller_arg->getType()->isPointerTy())
					   continue;

				   Argument *callee_arg = callee->arg_begin() + arg_i;
				   reverse_arg_map.insert(std::make_pair(callee_arg, caller_arg));
			   }

			   // edit ri-> TO ci->
			   if(ri->getReturnValue() && ri->getReturnValue()->getType()->isPointerTy())
			   {
				   ValueSet tmp_retval_vs = tmp_state.pt[ri->getReturnValue()];  
				   tmp_state.pt.erase(ri->getReturnValue());
				   tmp_state.pt[ci].insert(tmp_retval_vs.begin(), tmp_retval_vs.end());
			   }

			   // PASS BACK PT/FPT
			   for(auto arg_map_i = reverse_arg_map.begin(), arg_map_e = reverse_arg_map.end();
					   arg_map_i != arg_map_e; arg_map_i++)
			   {
				   Argument *callee_arg = arg_map_i->first;
				   Value *caller_arg = arg_map_i->second;

				   for(auto pi = tmp_state.pt.begin(), pe = tmp_state.pt.end();
						   pi != pe; pi++)
				   {
					   if(pi->second.count(callee_arg) && !isa<Function>(callee_arg))
					   {
						   pi->second.erase(callee_arg);
						   pi->second.insert(caller_arg);
					   }
				   }

				   for(auto fpi = tmp_state.field_pt.begin(), fpe = tmp_state.pt.end();
						   fpi != fpe; fpi++)
				   {
					   if(fpi->second.count(callee_arg) && !isa<Function>(callee_arg))
					   {
						   fpi->second.erase(callee_arg);
						   fpi->second.insert(caller_arg);
					   }
				   }
			   }

			   for(auto arg_map_i = reverse_arg_map.begin(), arg_map_e = reverse_arg_map.end(); 
					   arg_map_i != arg_map_e; arg_map_i++)
			   {
				   Argument *callee_arg = arg_map_i->first;
				   Value *caller_arg = arg_map_i->second;
				   if(tmp_state.pt.count((Value *)callee_arg))
				   {
					   ValueSet tmp_pt_vs = tmp_state.pt[(Value *)callee_arg];
					   tmp_state.pt.erase((Value *)callee_arg);
					   tmp_state.pt[caller_arg].insert(tmp_pt_vs.begin(), tmp_pt_vs.end());
				   }
				   if(tmp_state.field_pt.count((Value *)callee_arg))
				   {
					   ValueSet tmp_fpt_vs = tmp_state.field_pt[(Value *)callee_arg];
					   tmp_state.field_pt.erase((Value *)callee_arg);
					   tmp_state.field_pt[caller_arg].insert(tmp_fpt_vs.begin(), tmp_fpt_vs.end());
				   }
			   }
			   
			   PointToState caller_callinst_out = (*instresult)[ci].second;

			   merge(&caller_callinst_out, tmp_state);
			   
			   if((*instresult)[ci].second != caller_callinst_out)
			   {
				   (*instresult)[ci].second = caller_callinst_out;
				   // errs() << "returninst add into list << ";
				   // errs() << caller->getName() << "\n";
				   // errs() << caller_callinst_out << "\n";
				   func_set.insert(caller);
			   }
		   }
		   // getchar();
	   }
   }


   /*
   void handleBitCastInst(BitCastInst *bci, PointToState *state)
   {
	   errs() << "handleBitCastInst\n";
   }
   */

   FunctionSet getFunctions(Value *value, PointToState *state)
   {
	   FunctionSet func;
	   ValueSet worklist;

	   if(auto *F = dyn_cast<Function>(value))
	   {
		   func.insert(F);
		   return func;
	   }

	   // funcptr in the state->pt 
	   if(state->pt.count(value))
		   worklist.insert(state->pt[value].begin(), state->pt[value].end());

	   while(!worklist.empty())
	   {
		   Value *vi = *worklist.begin();

		   worklist.erase(worklist.begin());
		   if(auto *F = dyn_cast<Function>(vi))
			   func.insert(F);
		   else 
			   worklist.insert(state->pt[vi].begin(), state->pt[vi].end());
	   }

	   return func;
   }
};


class PointToPass : public ModulePass {
private:
   // unordered_set {func, ...}
   FunctionSet pass_func_set;
   // map: basicblock->[in_state, out_state]
   DataflowBBResult<PointToState>::Type result;

public:

   static char ID;
   PointToPass() : ModulePass(ID), pass_func_set(), result(){} 

   bool runOnModule(Module &M) override {
	   PointToVisitor pt_visitor;

	   DataflowInstResult<PointToState>::Type instresult;
	   pt_visitor.bbresult = &result;
	   pt_visitor.instresult = &instresult;

	   // M.dump();
	   // getchar();

	   for(auto &F : M)
	   {
		   // llvm::errs() << F.getName() << "\n"; 
		   // name startwith "llvm.xxxx"
		   if(F.isIntrinsic())
			   continue;
		   pass_func_set.insert(&F);
	   }

	   while(!pass_func_set.empty())
	   {
		   PointToState init_state;

		   Function *f = *(pass_func_set.begin());
		   pass_func_set.erase(pass_func_set.begin());
		   
		   // llvm::errs() << "[*] Doing: " << f->getName() << "\n";
		   compForwardDataflow(f, &pt_visitor, &result, init_state);
		   // llvm::errs() << "[*] Done:  " << f->getName() << "\n";

		   pass_func_set.insert(pt_visitor.func_set.begin(), pt_visitor.func_set.end());
		   pt_visitor.func_set.clear();
	   }
	   dumpCall(pt_visitor.call_return);

	   return false;
   }

private:
   void dumpCall(const std::map<CallInst *, FunctionSet, CallInstCmp> &call_return)
   {
	   for(auto i = call_return.begin(), e = call_return.end(); i != e; i++)
	   {
		   errs() << i->first->getDebugLoc().getLine() << " : ";
		   FunctionSet func_set = i->second;
		   for(auto func_i = func_set.begin(), func_e = func_set.end(); 
				   func_i != func_e; func_i++)
		   {
			   if(func_i != func_set.begin())
				   errs() << ", ";
			   errs() << (*func_i)->getName();
		   }
		   errs() << "\n";
	   }
   }
};


char PointToPass::ID = 0;
