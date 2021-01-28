/************************************************************************
 *
 * @file Dataflow.h
 *
 * General dataflow framework
 *
 ***********************************************************************/

#ifndef _DATAFLOW_H_
#define _DATAFLOW_H_

#include <llvm/Support/raw_ostream.h>
#include <map>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <set>
#include <utility>

// #include "PointToState.h"

using namespace llvm;

// Instruction -> <in state, outstate>
template <class T>
struct DataflowInstResult
{
	typedef typename std::map<Instruction *, std::pair<T, T>> Type;
};

///Base dataflow visitor class, defines the dataflow function

template <class T>
class DataflowVisitor {
public:
    virtual ~DataflowVisitor() { }

    /// Dataflow Function invoked for each basic block 
    /// 
    /// @block the Basic Block
    /// @dfval the input dataflow value
    /// @isforward true to compute dfval forward, otherwise backward
	/*virtual void compDFVal(BasicBlock *block, typename DataflowInstResult<T>::Type *dfval, bool isforward) {
		// forward
		if (isforward == true) {
		   for (BasicBlock::iterator ii=block->begin(), ie=block->end(); 
				ii!=ie; ++ii) {
				Instruction * inst = &*ii;
				compDFVal(inst, dfval);
		   }
		} 
		// backward
		else {
		   
		   for (BasicBlock::reverse_iterator ii=block->rbegin(), ie=block->rend();
				ii != ie; ++ii) {
				Instruction * inst = &*ii;
				compDFVal(inst, dfval);
		   }
		   
		}
	}*/
	virtual void compDFVal(BasicBlock *block, T *state, bool isforward)
	{
		// forward
		if(isforward == true)
		{
			for(BasicBlock::iterator ii = block->begin(), ie = block->end();
					ii != ie; ii++)
			{
				Instruction *inst = &*ii;
				// inst->dump();
				compDFVal(inst, state);
			}
		}
		// backward
		else {
			for(BasicBlock::reverse_iterator ii = block->rbegin(), ie = block->rend();
					ii != ie; ii++)
			{
				Instruction *inst = &*ii;
				compDFVal(inst, state);
			}		
		}
	}

    ///
    /// Dataflow Function invoked for each instruction
    ///
    /// @inst the Instruction
    /// @dfval the input dataflow value
    /// @return true if dfval changed
    // virtual void compDFVal(Instruction *inst, typename DataflowInstResult<T>::Type *dfval ) = 0;
	virtual void compDFVal(Instruction *inst, T *state) = 0;

    ///
    /// Merge of two dfvals, dest will be ther merged result
    /// @return true if dest changed
    ///
    virtual void merge( T *dest, const T &src ) = 0;
};

///
/// Dummy class to provide a typedef for the detailed result set
/// For each basicblock, we compute its input dataflow val and its output dataflow val
///
template<class T>
struct DataflowBBResult {
    typedef typename std::map<BasicBlock *, std::pair<T, T> > Type;
};

/// 
/// Compute a forward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval the Initial dataflow value
template<class T>
void compForwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowBBResult<T>::Type *result,
    const T & initval) {

	// worklist { basicblock }
	std::set<BasicBlock *> worklist;

	// Initialize the worklist with all blocks
	for(auto bi = fn->begin(), be = fn->end(); bi != be; bi++)
	{
		BasicBlock *bb = &*bi;
		// if bb not in result: insert the initval
		// else: will not insert into map 
		result->insert(std::make_pair(bb, std::make_pair(initval, initval)));
		worklist.insert(bb);
	}

	// ITeratively compute the dataflow result
	while(!worklist.empty())
	{
		// errs() << "          ***MERGE***         \n";
		BasicBlock *bb = *worklist.begin();
		// errs() << ">>>>>>>>>>>>>>>>>> current node:" << bb->getName() << "\n";
		worklist.erase(worklist.begin());

		// Merge all PRED NODE out state 
		T bb_instate = (*result)[bb].first;
		T tmp_bb_instate = bb_instate;
		// errs() << bb_instate << "\n";
		for(auto pi = pred_begin(bb), pe = pred_end(bb); pi != pe; pi++)
		{
			BasicBlock *pred_node = *pi;
			// errs() << "pred node:" << pred_node->getName() << "\n";
			// errs() << (*result)[pred_node].second << "\n";
			visitor->merge(&bb_instate, (*result)[pred_node].second);
		}
		// errs() << "*********************************\n";
		
		// if first handle -> comDFVal
		// elif merge node pred out state not change => basicblock will not into worklist
		// if(tmp_bb_instate == bb_instate)
			// continue;

		(*result)[bb].first = bb_instate;
		T old_bb_outstate = (*result)[bb].second;

		T tmp_state = bb_instate;
		// handle node via dataflow analysis (forward)
		visitor->compDFVal(bb, &tmp_state, true);
		
		if(old_bb_outstate == tmp_state)
			continue;
		
		(*result)[bb].second = tmp_state;
		
		// errs() << "\n\n";
		// errs() << "in: " << (*result)[bb].first << "\n";
		// errs() << "out: " << (*result)[bb].second << "\n";
		// errs() << "add succ: "; 
		// add the succ node into worklist
		for(auto si = succ_begin(bb), se = succ_end(bb); si != se; si++)
		{
			worklist.insert(*si);
			// errs() << si->getName() << "\n";
		}
		// errs() << "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n";
	}

    return;
}
/// 
/// Compute a backward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval The initial dataflow value
/*
template<class T>
void compBackwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowResult<T>::Type *result,
    const T &initval) {

    std::set<BasicBlock *> worklist;

    // Initialize the worklist with all exit blocks
    for (Function::iterator bi = fn->begin(); bi != fn->end(); ++bi) {
        BasicBlock * bb = &*bi;
        result->insert(std::make_pair(bb, std::make_pair(initval, initval)));
        worklist.insert(bb);
    }

    // Iteratively compute the dataflow result
    while (!worklist.empty()) {
        BasicBlock *bb = *worklist.begin();
        worklist.erase(worklist.begin());

        // Merge all incoming value
        T bbexitval = (*result)[bb].second;
        for (auto si = succ_begin(bb), se = succ_end(bb); si != se; si++) {
            BasicBlock *succ = *si;
            visitor->merge(&bbexitval, (*result)[succ].first);
        }

        (*result)[bb].second = bbexitval;
        visitor->compDFVal(bb, &bbexitval, false);

        // If outgoing value changed, propagate it along the CFG
        if (bbexitval == (*result)[bb].first) continue;
        (*result)[bb].first = bbexitval;

        for (pred_iterator pi = pred_begin(bb), pe = pred_end(bb); pi != pe; pi++) {
            worklist.insert(*pi);
        }
    }
}
*/

template<class T>
void printDataflowResult(raw_ostream &out,
                         const typename DataflowBBResult<T>::Type &dfresult) {
    for ( typename DataflowBBResult<T>::Type::const_iterator it = dfresult.begin();
            it != dfresult.end(); ++it ) {
        if (it->first == NULL) out << "*";
        else it->first->dump();
        out << "\n\tin : "
            << it->second.first 
            << "\n\tout :  "
            << it->second.second
            << "\n";
    }
}







#endif /* !_DATAFLOW_H_ */
