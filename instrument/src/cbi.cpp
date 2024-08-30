#include "Util/SVFUtil.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/LLVMModule.h"
#include "Graphs/SVFG.h"
#include "Graphs/ICFG.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "llvm/IR/CFG.h"
#include <fstream>
#include <sstream>
#include <ctime>

#include <stack>
#include <regex>

#include "Graphs/VFG.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVF-LLVM/ICFGBuilder.h"
#include "Util/Options.h"
#include "SVFIR/PAGBuilderFromFile.h"
#include "SABER/SaberSVFGBuilder.h"

using namespace SVF;
using namespace llvm;
using namespace std;

#define MAP_SIZE_POW2       16
#define MAP_SIZE            (1 << MAP_SIZE_POW2)
#define AFL_R(x) (random() % (x))
#define SUF_NUM             500 
#define SUF_NUM_CFG         50000 
#define PRE_NUM_CFG         50000
#define TARGETS_NUM         10 
#define TARGETS_NUM_ORIG         32 

static llvm::cl::opt<std::string> InputFilename(cl::Positional,
        llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));
static llvm::cl::opt<std::string> TargetsFile("targets", llvm::cl::desc("specify targes file"), llvm::cl::Required);


std::set<const BasicBlock*> targets_llvm_bb;
std::set<const BasicBlock*> targets_DT_bb;
std::set<const BasicBlock*> targets_DT_bb_orig;
int targets_DT_bb_num = TARGETS_NUM;
int targets_DT_bb_num_orig = TARGETS_NUM;
std::set<const Function*> targets_llvm_func;
std::map<const Function *, std::set<const BasicBlock *>> targets_llvm_func_bbs;
std::map<const BasicBlock *, const BasicBlock *> origBB2DTBB;
SVFModule* svfModule;
SVFG *svfg;
ICFG* icfg;
Module* M;
LLVMContext* C;


std::list<const VFGNode *> VFGNodes;
std::map<uint32_t,std::set<const BasicBlock*>> targets_pre_cfg_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_cfg_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_data_bb;
std::map<uint32_t,std::set<const BasicBlock*>> targets_suf_data_bb_target;
std::map<const BasicBlock *,uint32_t> BB_IDs;
std::map<uint32_t,double> BBID2dis;
std::set<uint32_t> test;
std::set<const BasicBlock*> all_pre_cfg_bb;
std::set<const BasicBlock*> all_suf_cfg_bb;
std::set<const BasicBlock*> all_suf_data_bb;
uint32_t test_dfs=0;

std::map<const ICFGNode *, double > preNodeMap;
std::map<NodeID, std::map<const ICFGNode *, double >> targetID2preNodeMap;
std::map<const BasicBlock *, double > preNodeMapBB;
std::map<NodeID, std::map<const BasicBlock *, double >> targetID2preNodeMapBB;
std::map<const BasicBlock *, double > HMpreNodeMapBB;


std::string getDebugInfo(BasicBlock* bb) {
	for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
		Instruction* inst = &(*it);
		std::string str=LLVMUtil::getSourceLoc(inst);
		if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos)
			return str;
	}
	return "{ }";
}

void instrument_orig() {
	ofstream outfile4("bbinfo.txt", std::ios::out | std::ios::app);
	uint32_t bb_id = 0;

  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
			BasicBlock* bb = &*(bit);

      const BasicBlock *constbb = (const BasicBlock *)bb;
      if(getDebugInfo(bb).find("/usr/") == string::npos ){
        outfile4 << bb_id << getDebugInfo(bb) << std::endl;
        if(BB_IDs.find(constbb) == BB_IDs.end()){
          BB_IDs[constbb] = bb_id;
          bb_id++;
        }
      }
    }
	}
	outfile4.close();
}

void instrument() {
	ofstream outfile("distance.txt", std::ios::out | std::ios::app);
	ofstream outfile2("functions.txt", std::ios::out | std::ios::app);
	ofstream outfile3("targets.txt", std::ios::out | std::ios::app);
	ofstream outfile5("targets_id.txt", std::ios::out | std::ios::app);
	ofstream outfile7("targets_id_orig.txt", std::ios::out | std::ios::app);
	uint32_t bb_id = 0;
	uint32_t target_id = 0;
	uint32_t target_id_orig = 0;
  uint32_t target_id_orig_toomany = 0;

  IntegerType *Int8Ty = IntegerType::getInt8Ty(*C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);

	GlobalVariable *AFLMapPtr = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
    });

  IntegerType *LargestType = Int64Ty;
  ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
  ConstantInt *MapTargetLoc = ConstantInt::get(LargestType, MAP_SIZE + 24);
  ConstantInt *MapCrashLoc = ConstantInt::get(LargestType, MAP_SIZE + 56);
  ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
  ConstantInt *One = ConstantInt::get(LargestType, 1);

  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
			BasicBlock* bb = &*(bit);
      const BasicBlock *constbb = (const BasicBlock *)bb;
      bb_id=BB_IDs[constbb];
        BasicBlock::iterator IP = bb->getFirstInsertionPt();
        llvm::IRBuilder<> IRB(&(*IP));

				/* Load SHM pointer */

				LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
				MapPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        const BasicBlock *tempBB = (const BasicBlock *)bb;
        llvm::Value* value = llvm::ConstantInt::get(LargestType, 0);
        if( !target_id_orig_toomany && targets_DT_bb_orig.count(tempBB)){
          Value *MapTargetPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapTargetLoc), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapTargetPtr);
          MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          ConstantInt *bitValue = llvm::ConstantInt::get(LargestType, 1 << target_id_orig);
          value = IRB.CreateOr(MapCnt, bitValue);

          IRB.CreateStore(value, MapTargetPtr)
              ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          target_id_orig++;
          if(target_id_orig >= TARGETS_NUM_ORIG - 1 ){
            errs() << "target_id_orig>TARGETS_NUM_ORIG\n";
            target_id_orig_toomany = 1;
          }
          outfile7 << bb_id << std::endl;
        }

      uint32_t distance = -1;
      std::map<NodeID, uint32_t> distance_targets;

      if(HMpreNodeMapBB.count(bb)){
        distance = (uint32_t)(100 * HMpreNodeMapBB[bb]);

        int i = -1;
        for (auto target_bb: targets_DT_bb)
        {
          i++;
          if(i>=TARGETS_NUM){
            exit(1);
          }
          NodeID target_bb_id = BB_IDs[target_bb];
          if(!targetID2preNodeMapBB[target_bb_id].count(bb)){
            continue;
          }
          distance_targets[target_bb_id] = (uint32_t)(100 * targetID2preNodeMapBB[target_bb_id][bb]);

          ConstantInt *Distance = ConstantInt::get(LargestType, (unsigned) distance_targets[target_bb_id]);

          /* Add distance to shm[MAPSIZE] */

          ConstantInt *MapDistLoc_index = ConstantInt::get(LargestType, MAP_SIZE + 64 + 16 * i);
          ConstantInt *MapCntLoc_index = ConstantInt::get(LargestType, MAP_SIZE + 64 + 8 + 16 * i);

          Value *MapDistPtr = IRB.CreateBitCast(
            IRB.CreateGEP(MapPtr, MapDistLoc_index), LargestType->getPointerTo());
          LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
          IRB.CreateStore(IncrDist, MapDistPtr)
            ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          /* Increase count at shm[MAPSIZE + (4 or 8)] */

          Value *MapCntPtr = IRB.CreateBitCast(
            IRB.CreateGEP(MapPtr, MapCntLoc_index), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
          MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

          Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
          IRB.CreateStore(IncrCnt, MapCntPtr)
            ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        }

				ConstantInt *Distance = ConstantInt::get(LargestType, (unsigned) distance);

				/* Add distance to shm[MAPSIZE] */

				Value *MapDistPtr = IRB.CreateBitCast(
					IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
				LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
				MapDist->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
				IRB.CreateStore(IncrDist, MapDistPtr)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				/* Increase count at shm[MAPSIZE + (4 or 8)] */

				Value *MapCntPtr = IRB.CreateBitCast(
					IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
				LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
				MapCnt->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
				IRB.CreateStore(IncrCnt, MapCntPtr)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				if (distance == 0 && target_id < TARGETS_NUM) {
					ConstantInt *TFlagLoc = ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + target_id);
					Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
					ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
					IRB.CreateStore(FlagOne, TFlagPtr)
						->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

					outfile3 << target_id << " " << getDebugInfo(bb) << std::endl;
          outfile5 << bb_id << std::endl;
					target_id++;
				}

				outfile << bb_id << " " << distance << " ";
				outfile << 0 << " "; 
				outfile << getDebugInfo(bb) << std::endl;
			}
      if(getDebugInfo(bb).find("/usr/") == string::npos ){
        BBID2dis[bb_id] = distance;
      }
    }
	}

	outfile.close();
	outfile2.close();
	outfile3.close();
	outfile5.close();
	outfile7.close();
}


void instrumentSuffix() {
  ofstream outfile("suffix.txt", std::ios::out | std::ios::app);
	ofstream outfile2("prefix.txt", std::ios::out | std::ios::app);
	ofstream outfile3("suffix_data.txt", std::ios::out | std::ios::app);

  IntegerType *Int64Ty = IntegerType::getInt64Ty(*C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(*C);
  GlobalVariable *AFLMapPtrSufBB = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr_suf_bb",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr_suf_bb");
    });
  
  GlobalVariable *AFLMapPtr = (GlobalVariable*)M->getOrInsertGlobal("__afl_area_ptr",PointerType::get(IntegerType::getInt8Ty(*C), 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M, PointerType::get(IntegerType::getInt8Ty(M->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
    });
  IntegerType *LargestType = Int64Ty;  
  ConstantInt *MapCntLocSuf = ConstantInt::get(LargestType, MAP_SIZE + 32);
  ConstantInt *One = ConstantInt::get(LargestType, 1);
  
  uint32_t bb_id = 0;
  uint32_t suf_bb_id = 0;
  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
      
        BasicBlock *bb = &*(bit);
        if(!BB_IDs.count(bb))
          continue;
        if(test.find(BB_IDs[bb])!=test.end()){
          ;
        }
        test.insert(BB_IDs[bb]);

        
        if (all_suf_cfg_bb.find(bb) != all_suf_cfg_bb.end()){
          BasicBlock::iterator IP3 = bb->getFirstInsertionPt();
          llvm::IRBuilder<> IRB3(&(*IP3));
          llvm::LoadInst *MapPtrSufBB = IRB3.CreateLoad(AFLMapPtrSufBB);
          ConstantInt *cur_id = llvm::ConstantInt::get(IntegerType::getInt32Ty(*C), suf_bb_id);

          llvm::Value *MapPtrIdxSufBB = IRB3.CreateGEP(MapPtrSufBB, cur_id);
          llvm::LoadInst *CounterBB = IRB3.CreateLoad(MapPtrIdxSufBB);
          llvm::Value *IncrBB = IRB3.CreateAdd(CounterBB, ConstantInt::get(Int8Ty, 1));
          IRB3.CreateStore(IncrBB, MapPtrIdxSufBB)
              ->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));
          suf_bb_id++;
          if(suf_bb_id >= MAP_SIZE){
            suf_bb_id = 0;
            errs() << "suf_bb_id reset\n";
            exit(1);
          }

        /* Load SHM pointer */

				LoadInst *MapPtr = IRB3.CreateLoad(AFLMapPtr);
				MapPtr->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

        
				/* Increase count at shm[MAPSIZE + (4 or 8)] */

				Value *MapCntPtrSuf = IRB3.CreateBitCast(
					IRB3.CreateGEP(MapPtr, MapCntLocSuf), LargestType->getPointerTo());
				LoadInst *MapCntSuf = IRB3.CreateLoad(MapCntPtrSuf);
				MapCntSuf->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));

				Value *IncrCntSuf = IRB3.CreateAdd(MapCntSuf, One);
				IRB3.CreateStore(IncrCntSuf, MapCntPtrSuf)
					->setMetadata(M->getMDKindID("nosanitize"), MDNode::get(*C, None));


        }
    }
  }
  outfile << suf_bb_id<< " hello" << std::endl;
  outfile2 << " hello" << std::endl;
  outfile3 << " hello" << std::endl;

  for(auto tbb:targets_llvm_bb){
    uint32_t target_bb_id = BB_IDs[tbb];
    // errs() << target_bb_id << "\n";
    for (auto sufbb : targets_suf_cfg_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile << target_bb_id << " " << suffix_bb_id << " " << std::endl;
    }
  }
  for(auto tbb:targets_llvm_bb){
    uint32_t target_bb_id = BB_IDs[tbb];
    for (auto sufbb : targets_pre_cfg_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile2 << target_bb_id << " " << suffix_bb_id << " " << std::endl;
    }
  }
  for(auto tbb:targets_llvm_bb){
    const BasicBlock *dtbb = origBB2DTBB[tbb];
    uint32_t target_bb_id_dt = BB_IDs[dtbb];
    uint32_t target_bb_id = BB_IDs[tbb];
    string filename = to_string(target_bb_id_dt) + "_suffix_data.txt";
    ofstream outfile5(filename.c_str(), std::ios::out | std::ios::app);

    for (auto sufbb : targets_suf_data_bb[target_bb_id])
    {
      uint32_t suffix_bb_id = BB_IDs[sufbb];
      outfile3 << target_bb_id << " " << suffix_bb_id << " " << std::endl;
      targets_suf_data_bb_target[target_bb_id_dt].insert(sufbb);
      outfile5 << target_bb_id_dt << " " << suffix_bb_id << " " << std::endl;

    }

    outfile5.close();
  }

  outfile.close();
  outfile2.close();
  outfile3.close();

}

void findTargetControl(std::vector<NodeID> x){

    set<const ICFGNode *> isvisited_pre;
    set<const ICFGNode *> isvisited_suf;

  for(const BasicBlock* BB:targets_DT_bb){
    const Instruction *lastInstr = BB->getTerminator();
    
    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(lastInstr))->getId();
    ICFGNode *iNode = icfg->getICFGNode(id);
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
    uint32_t taget_bb_id = BB_IDs[BB_target];

    bool sufFlag = 1;   
    bool preFlag = 1;
    if(isvisited_suf.find(iNode)!=isvisited_suf.end()){
      sufFlag = 0;
    }else{
      isvisited_suf.clear();
    }

    if(isvisited_pre.find(iNode)!=isvisited_pre.end()){
      isvisited_pre.clear();
    }else{
      isvisited_pre.clear();
    }

    std::set<const BasicBlock*> tmp_pre_bbs;
    std::set<const BasicBlock*> tmp_suf_bbs;

    FIFOWorkList<const ICFGNode *> worklist;
    FIFOWorkList<const SVF::ICFGNode *> worklist_suf;
    worklist.push(iNode);
    targetID2preNodeMap[taget_bb_id][iNode] = 0;
    targetID2preNodeMapBB[taget_bb_id][BB] = 0;
    tmp_pre_bbs.insert(BB);
    worklist_suf.push(iNode);

    set<const ICFGNode *> caller;
    set<const SVFFunction *> caller_func;

    int pre_num_cfg = 0;

    while(!worklist.empty() && preFlag && (pre_num_cfg<PRE_NUM_CFG)){
      pre_num_cfg++;
      const ICFGNode *iNode = worklist.pop();
      isvisited_pre.insert(iNode);

      const BasicBlock *nowBB = NULL;
      if(iNode->getBB()){
        nowBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(iNode->getBB()));
      }

      for(ICFGNode::const_iterator it = iNode->InEdgeBegin(), eit =
                                                                        iNode->InEdgeEnd();
           it != eit; ++it)
      {
        ICFGEdge *edge = *it;
        ICFGNode *preNode = edge->getSrcNode();

        if(isvisited_pre.find(preNode) != isvisited_pre.end()){
          continue;
        }

        const IntraICFGNode *intraNode = NULL;
        const BasicBlock *callBB = NULL;
        const BasicBlock *preBB = NULL;

        if(preNode->getBB()){
          preBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(preNode->getBB()));
        }

        if(RetICFGNode * retNode = dyn_cast<RetICFGNode>(preNode)){
          const ICFGNode *callICFGNode = retNode->getCallICFGNode();
          worklist.push(callICFGNode);
          if(callICFGNode->getBB()){
            callBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(callICFGNode->getBB()));
          }

          if(callBB == nowBB){
            ;
          }else if(targetID2preNodeMapBB[taget_bb_id].count(callBB)){
            targetID2preNodeMapBB[taget_bb_id][callBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 < targetID2preNodeMapBB[taget_bb_id][callBB] ? targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 : targetID2preNodeMapBB[taget_bb_id][callBB];

          }else{
            targetID2preNodeMapBB[taget_bb_id][callBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1;
          }
          for(ICFGNode::const_iterator it = retNode->InEdgeBegin(), eit =
                                                                          retNode->InEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunExitICFGNode *FunExitNode = NULL;
            if(FunExitNode = dyn_cast<FunExitICFGNode>(edge->getSrcNode())) {
              caller.insert(callICFGNode);
              caller_func.insert(FunExitNode->getFun());
            }
          }
        }
        else if(CallICFGNode* callICFGNode= dyn_cast<CallICFGNode>(preNode)){
          if(caller_func.count(iNode->getFun())){
            if(caller.find(callICFGNode) == caller.end()){
              continue;
            }
          }
        }
        worklist.push(preNode);
        
        if(preBB == nowBB){
          ;
        }else if(targetID2preNodeMapBB[taget_bb_id].count(preBB)){
          targetID2preNodeMapBB[taget_bb_id][preBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 < targetID2preNodeMapBB[taget_bb_id][preBB] ? targetID2preNodeMapBB[taget_bb_id][nowBB] + 1 : targetID2preNodeMapBB[taget_bb_id][preBB];
        }else{
          targetID2preNodeMapBB[taget_bb_id][preBB] = targetID2preNodeMapBB[taget_bb_id][nowBB] + 1;
        }
        
      }
    }

    if(preFlag){
      /// Collect all LLVM Values
      for(auto it = isvisited_pre.begin(), eit = isvisited_pre.end(); it!=eit; ++it)
      {
        const ICFGNode *node = *it;
        const IntraICFGNode *intraNode = NULL;
        if (intraNode= dyn_cast<IntraICFGNode>(node)){

          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getInst()));
          if (inst)
          {
            const BasicBlock *BB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getBB()));

            tmp_pre_bbs.insert(BB);
          }
        }
      }

      targets_pre_cfg_bb[taget_bb_id].insert(tmp_pre_bbs.begin(), tmp_pre_bbs.end());
      all_pre_cfg_bb.insert(tmp_pre_bbs.begin(), tmp_pre_bbs.end());
    }


    set<FunEntryICFGNode *> callee;

    int suf_num_cfg = 0;

    while(!worklist_suf.empty() && sufFlag &&(suf_num_cfg<SUF_NUM_CFG)){
      suf_num_cfg++;
      const ICFGNode *iNode = worklist_suf.pop();
      isvisited_suf.insert(iNode);
      if(const CallICFGNode * callNode = dyn_cast<const CallICFGNode>(iNode)){
        worklist_suf.push(callNode->getRetICFGNode());
        for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
        {
          ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = NULL;
            if(FunEntryNode = dyn_cast<FunEntryICFGNode>(edge->getDstNode())) {
              callee.insert(FunEntryNode);
            }
        }

      }
      for(ICFGNode::const_iterator it = iNode->OutEdgeBegin(), eit =
                                                                        iNode->OutEdgeEnd();
           it != eit; ++it)
      {
        ICFGEdge *edge = *it;
        ICFGNode *sufNode = edge->getDstNode();

        if(isvisited_suf.find(sufNode) != isvisited_suf.end()){
          continue;
        }
        if(CallICFGNode * callNode = dyn_cast<CallICFGNode>(sufNode)){
          worklist_suf.push(callNode->getRetICFGNode());
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                            callNode->OutEdgeEnd();
              it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = NULL;
            if(FunEntryNode = dyn_cast<FunEntryICFGNode>(edge->getDstNode())) {
              callee.insert(FunEntryNode);
            }
          }

        }else if(FunExitICFGNode* funExitNode = dyn_cast<FunExitICFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(funExitNode->getFun());
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        }
        worklist_suf.push(sufNode);

      }
    }

    if(sufFlag){
      /// Collect all LLVM Values
      for(auto it = isvisited_suf.begin(), eit = isvisited_suf.end(); it!=eit; ++it)
      {
        const SVF::ICFGNode *node = *it;
        const SVF::IntraICFGNode *intraNode = NULL;
        if (intraNode= dyn_cast<SVF::IntraICFGNode>(node)){

          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(intraNode->getInst()));
          if (inst)
          {
            const BasicBlock *BB = (BasicBlock*)inst->getParent();
            tmp_suf_bbs.insert(BB);
          }
        }

      }

      targets_suf_cfg_bb[taget_bb_id].insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
      all_suf_cfg_bb.insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
    }
   
	}


  ofstream outfile("targetBB_dis_sep.txt", std::ios::out | std::ios::app);
  ofstream outfile1("BBtargetBB_dis_sep.txt", std::ios::out | std::ios::app);
  std::set<uint32_t> targetBBIDs;
  std::set<const BasicBlock *> targetBBs;

  for(const BasicBlock* BB:targets_DT_bb){
    const Instruction *firstInstr = &*(BB->begin());
    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(firstInstr))->getId();
    
      ICFGNode* iNode = icfg->getICFGNode(id);
    
      const SVFBasicBlock *svfbb = iNode->getBB();
      const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
      uint32_t taget_bb_id = BB_IDs[BB_target];
      targetBBIDs.insert(taget_bb_id);
      targetBBs.insert(BB_target);
  }

  
  for(auto BB : all_pre_cfg_bb){
    uint32_t BBID = BB_IDs[BB];
    outfile1 << BBID <<" : ";
    for(auto BB_target : targetBBs ){
      uint32_t taget_bb_id = BB_IDs[BB_target];
      if(targetID2preNodeMapBB[taget_bb_id].count(BB)){
        if(HMpreNodeMapBB.count(BB)){
          if(HMpreNodeMapBB[BB]==0 || targetID2preNodeMapBB[taget_bb_id][BB]==0){
            HMpreNodeMapBB[BB]=0;
          }else{
            HMpreNodeMapBB[BB] = (double)2 / (((double)1 / targetID2preNodeMapBB[taget_bb_id][BB]) + ((double)1 / (HMpreNodeMapBB[BB])));
          }
        }else{
          HMpreNodeMapBB[BB] = targetID2preNodeMapBB[taget_bb_id][BB];
        }

        outfile1 << " " << targetID2preNodeMapBB[taget_bb_id][BB];
      }else{
        outfile1 << " None";
      }
    }
    outfile1 <<" "<< HMpreNodeMapBB[BB] << std::endl;
  }

  for(auto BB_target : targetBBs ){
    uint32_t taget_bb_id = BB_IDs[BB_target];
    for(auto BB : all_pre_cfg_bb){
      uint32_t BBID = BB_IDs[BB];
      if(targetID2preNodeMapBB[taget_bb_id].count(BB)){
        outfile<<taget_bb_id<<" "<<BBID<<" "<<targetID2preNodeMapBB[taget_bb_id][BB]<<std::endl;
      }
    }
  }

  outfile.close();
  outfile1.close();
}

SVFGNode * SVFVar2SVFNode(const SVFVar *Var){
  const SVFValue *val = Var->getValue();
  uint32_t totalNodeNum = svfg->getTotalNodeNum();
  SVF::SVFGNode *vNode;
  for (uint32_t i = 0; i < totalNodeNum; i++)
  {
    if (!svfg->hasSVFGNode(i))
    {
      errs() << "i num: " << i << "\n";
      break;
    }
    vNode = svfg->getSVFGNode(i);
    if (vNode->getValue() == val)
    {
      break;
    }
  }

  return vNode;
}

bool isBlacklisted(const SVFVar * Var ) {
  static const SmallVector<std::string, 50> Blacklist = {
    "alloc",
    "strcpy",
    "strncpy",
    "bsearch",
    "_Znwm",
    "_Znam",
    "strcat",
    "memchr",
    "mmap",
    "strchr",
    "fopen",
    "strdup",
    "pthread_getspecific",
    "fgets",
    "realpath",
    "__dynamic_cast",
    "getenv",
    "strstr",
    "fdopen",
    "popen",
    "strrchr",
    "str",
    "gmtime",
    "time",
    "open",
    "isdigit",
    "inet_ntop"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (Var->toString().find(BlacklistFunc)!=string::npos) {
      return true;
    }
  }

  return false;
}

void findTargetUse(SVFG *svfg, int num){
    FIFOWorkList<const VFGNode *> worklist;
    set<const VFGNode*> visited;

  for(auto val : VFGNodes){
    SVFGNode *vNode = (SVFGNode *)val;
    bool sufFlag = 1;   
    if(visited.find(vNode)!=visited.end()){
      ;
    }else{
      visited.clear();
    }

    worklist.push(vNode);

    const ICFGNode* iNode = val->getICFGNode();
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *BB_target = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
    uint32_t taget_bb_id = BB_IDs[BB_target];

    std::set<const BasicBlock*> tmp_suf_bbs;
    set<FunEntryICFGNode *> callee;

    int suf_num = 0;

    while(!worklist.empty() && sufFlag && (suf_num<SUF_NUM)){
      suf_num++;
      const VFGNode *treeNode = worklist.pop();
      
      visited.insert(treeNode);
      if(const ActualParmVFGNode* AParmNode=dyn_cast<ActualParmVFGNode>(treeNode)){
          const CallICFGNode *callNode = AParmNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
          }
          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          for (auto nodeid : AOUTNodeSet)
          {
            worklist.push(svfg->getSVFGNode(nodeid));
          }

          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          
          const SVFValue *val = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
          
      }else if(const ActualINSVFGNode * AINNode = dyn_cast<ActualINSVFGNode>(treeNode)){
          const CallICFGNode *callNode = AINNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
            // break;
          }

          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          for(auto nodeid : AOUTNodeSet){
            worklist.push(svfg->getSVFGNode(nodeid));
          }
          
          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          const SVFValue *val = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
      }
      for (VFGNode::const_iterator it = treeNode->OutEdgeBegin(), eit = treeNode->OutEdgeEnd();
           it != eit; ++it)
      {
        VFGEdge *edge = *it;
        VFGNode *sufNode = edge->getDstNode();
        if(visited.find(sufNode) != visited.end()){
          continue;
        }
        if(ActualParmVFGNode* AParmNode=dyn_cast<ActualParmVFGNode>(sufNode)){
          const CallICFGNode *callNode = AParmNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
          }
               
            NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
            for(auto nodeid : AOUTNodeSet){
              worklist.push(svfg->getSVFGNode(nodeid));
            }

          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          const SVFValue *SVFval = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }
        }else if(FormalRetVFGNode * FRetNode = dyn_cast<FormalRetVFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(FRetNode->getFun());
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        }else if(ActualINSVFGNode * AINNode = dyn_cast<ActualINSVFGNode>(sufNode)){
          const CallICFGNode *callNode = AINNode->getCallSite();
          for(ICFGNode::const_iterator it = callNode->OutEdgeBegin(), eit =
                                                                          callNode->OutEdgeEnd();
            it != eit; ++it)
          {
            ICFGEdge *edge = *it;
            FunEntryICFGNode *FunEntryNode = (FunEntryICFGNode *) edge->getDstNode();
            callee.insert(FunEntryNode);
          }
          NodeBS &AOUTNodeSet = svfg->getActualOUTSVFGNodes(callNode);
          for(auto nodeid : AOUTNodeSet){
            worklist.push(svfg->getSVFGNode(nodeid));
          }
          
          const RetICFGNode *RetNode = callNode->getRetICFGNode();
          const SVFVar *Var = RetNode->getActualRet();
          if(Var ==NULL){
            continue;
          }
          const SVFValue *val = Var->getValue();
          if(isBlacklisted(Var)){
            SVFGNode *svfgNode = SVFVar2SVFNode(Var);
            worklist.push(svfgNode);
          }else{
            const ActualRetVFGNode *ARetNode = svfg->getActualRetVFGNode(Var);
            worklist.push(ARetNode);
          }

        }else if(FormalOUTSVFGNode * FOUTNode=dyn_cast<FormalOUTSVFGNode>(sufNode)){
          FunEntryICFGNode *funEntryNode = icfg->getFunEntryICFGNode(FOUTNode->getFunExitNode()->getFun());
          if(callee.find(funEntryNode)!=callee.end()){
            continue;
          }
        }
        worklist.push(sufNode);
      }
    }

    if(sufFlag){
      for(auto it = visited.begin(), eit = visited.end(); it!=eit; ++it)
      {
        const VFGNode *node = *it;
        const StmtVFGNode *stmtNode = NULL;
        if (stmtNode= dyn_cast<StmtVFGNode>(node)){
          if(stmtNode->getInst() == nullptr){
            continue;
          }
          const Instruction *inst = cast<const Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(stmtNode->getInst()));
          
          if (inst)
          {
            const BasicBlock *BB = (BasicBlock*)inst->getParent();
            tmp_suf_bbs.insert(BB);
          }
        }
      }
      targets_suf_data_bb[taget_bb_id].insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
      all_suf_data_bb.insert(tmp_suf_bbs.begin(), tmp_suf_bbs.end());
    }

  }

}

const BasicBlock *getDominatorBB(const Function* fun, std::set<const BasicBlock *> BBs)
{
  // Build the dominator tree for this function
  const DominatorTree DT(const_cast<Function&>(*fun));

  // Find the common dominator of the given basic blocks
  const BasicBlock *DominatorBB = nullptr;
  
  for (auto it = BBs.begin(); it != BBs.end(); it++) {
    const BasicBlock *BB = *it;

    if (!DT.isReachableFromEntry(BB))
    {
      ;
    }else{
      if (!DominatorBB) {
        DominatorBB = BB;
      } else {
        DominatorBB = DT.findNearestCommonDominator(DominatorBB, BB);
      }
    }
  }
  
  if(!DominatorBB){
    exit(1);
  }
  return DominatorBB;
}


void filter_target(){
  errs() << "filter targets...\n";
  for (auto func: targets_llvm_func){
    const BasicBlock *dominatorBB = getDominatorBB(func, targets_llvm_func_bbs[func]);
    targets_DT_bb.insert(dominatorBB);

    for(auto origBB: targets_llvm_func_bbs[func]){
      origBB2DTBB[origBB] = dominatorBB;
    }
  }

  int i = 0;
  for (auto it = targets_DT_bb.begin(); it != targets_DT_bb.end(); ) {
      i++;
      if (i >= TARGETS_NUM) {
          errs() << "target too many!, delete over target\n";
          it = targets_DT_bb.erase(it); 
      } else {
          ++it; 
      }
  }

  targets_DT_bb_num = i;
  targets_DT_bb_num_orig = targets_DT_bb_orig.size();
}



std::vector<NodeID> loadTargets(std::string filename) {
  ifstream inFile(filename);
	if (!inFile) {
		std::cerr << "can't open target file!" << std::endl;
		exit(1);
	}
	std::vector<NodeID> result;
	std::vector<std::pair<std::string,u32_t>> targets;
	std::string line;
	while(getline(inFile, line)) {
		std::string func;
		uint32_t num;
		std::istringstream text_stream(line);
		getline(text_stream, func, ':');
    if(func.empty()){
      errs() << "empty\n";
      continue;
    }
		text_stream >> num;
    targets.push_back(make_pair(func, num));
	}

  for (Module::const_iterator F = M->begin(), E = M->end(); F != E; ++F){
    const Function *fun = &*(F);
		std::string file_name = "";
		std::string Filename = "";

		if (llvm::DISubprogram *SP = fun->getSubprogram()){
			if (SP->describes(fun))
				file_name = (SP->getFilename()).str();
		}
		bool flag = false;
		for (auto target : targets) {
      auto idx = file_name.find(target.first);
      if (idx != string::npos) {
				flag = true;
				break;
			}
		}
		if (!flag)
			continue;
    
    for (Function::const_iterator bit = fun->begin(), ebit = fun->end(); bit != ebit; ++bit) {

			const BasicBlock* bb = &(*bit);
			for (BasicBlock::const_iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
				uint32_t line_num = 0;
				const Instruction* inst = &(*it);
				std::string str=LLVMUtil::getSourceLoc(inst);

					if (SVFUtil::isa<AllocaInst>(inst)) {
            continue;
					}
					else if (MDNode *N = inst->getMetadata("dbg")) {
						llvm::DILocation* Loc = SVFUtil::cast<llvm::DILocation>(N);
						line_num = Loc->getLine();
            Filename = Loc->getFilename().str();
					}
					
					// if the line number match the one in targets
					for (auto target : targets) {
						auto idx = Filename.find(target.first);
						if (idx != string::npos && (idx == 0 || Filename[idx-1]=='/')) {
							if ((target.second == line_num) ) {
                std::list<const VFGNode *> TempVFGNodes = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst))->getVFGNodes();

                // only search for StoreVFGNode
                std::list<const VFGNode *>::iterator it = TempVFGNodes.begin();
                while (it != TempVFGNodes.end()) {
                  if (!dyn_cast<const StoreVFGNode>(*it) && !dyn_cast<const CopyVFGNode>(*it) && !dyn_cast<const CmpVFGNode>(*it) && !dyn_cast<const BinaryOPVFGNode>(*it) && !dyn_cast<const UnaryOPVFGNode>(*it)) {
                    it = TempVFGNodes.erase(it); 
                  }else{
                    ++it;
                    targets_DT_bb_orig.insert(bb);
                    NodeID id = icfg->getICFGNode(LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst))->getId();
                    result.push_back(id);
                  }
                }
                VFGNodes.splice(VFGNodes.end(), TempVFGNodes);
              }
						}
					}
        }
      }
    }
  inFile.close();

  for (NodeID id : result) {
		ICFGNode* iNode = icfg->getICFGNode(id);
    const SVFBasicBlock *svfbb = iNode->getBB();
    const BasicBlock *bb = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
    const Function *func = bb->getParent();

    targets_llvm_bb.insert(bb);
    targets_llvm_func.insert(func);
    targets_llvm_func_bbs[func].insert(bb);
  }

  filter_target();

	return result;
}

static void buildBranchInfo(std::vector<NodeID> target_ids){
  std::map<const BasicBlock *,uint32_t> BB2Loc;
	ofstream outfile("icfg-edge.txt", std::ios::out | std::ios::app);
	ofstream outfile2("edge-test.txt", std::ios::out | std::ios::app);
	ofstream outfile3("branch-distance.txt", std::ios::out | std::ios::app);
	ofstream outfile4("branch-distance-min.txt", std::ios::out | std::ios::app);
	ofstream outfile5("branch-curloc.txt", std::ios::out | std::ios::app);
  ofstream outfile6("branch-data.txt", std::ios::out | std::ios::app);
  ofstream outfile7("branch-distance-min-data.txt", std::ios::out | std::ios::app);

  vector<ofstream> files;
  for(auto target_bb:targets_DT_bb){
    NodeID target_bb_id = BB_IDs[target_bb];

    string filename = to_string(target_bb_id) + "_distance.txt";
    files.emplace_back(filename);
  }

  vector<ofstream> files_data;
  for(auto target_bb:targets_DT_bb){
    NodeID target_bb_id = BB_IDs[target_bb];

    string filename = to_string(target_bb_id) + "_edge_suffix_data.txt";
    files_data.emplace_back(filename);
  }

  srandom(994);
  int num = 0;
  for (auto iter = M->begin(), eiter = M->end(); iter != eiter;++iter){
    llvm::Function *fun = &*(iter);
    for (auto bit = fun->begin(), ebit = fun->end(); bit != ebit;++bit){
      
        BasicBlock *bb = &*(bit);
      unsigned int cur_loc = AFL_R(MAP_SIZE);
      BB2Loc[bb] = cur_loc;
      num++;
      outfile2 <<"bbid: "<<BB_IDs[bb]<<" cur_loc: " << cur_loc << " bbinfo: "<< getDebugInfo(bb)<<" \n";     
    }
  }

  std::set<const BasicBlock *> visited_bb;
  Set<const ICFGNode *> visited;
  NodeID id = 0;
  ICFGNode* iNode = icfg->getICFGNode(id);
  FIFOWorkList<const ICFGNode*> worklist;
  worklist.push(iNode);
  for(auto nodeid:target_ids){
    worklist.push(icfg->getICFGNode(nodeid));
  }

  while (!worklist.empty())
    {
        const ICFGNode* iNode = worklist.pop();
        const SVFBasicBlock *svfbb = iNode->getBB();
        const BasicBlock *SrcBB = nullptr;
        if(!svfbb) {
          ;
        }else{
          SrcBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(svfbb));
        }
        
        visited_bb.insert(SrcBB);
        for (ICFGNode::const_iterator it = iNode->OutEdgeBegin(), eit =
                    iNode->OutEdgeEnd(); it != eit; ++it)
        {
            ICFGEdge* edge = *it;
            ICFGNode* succNode = edge->getDstNode();
            const BasicBlock *DstBB = nullptr;
            if(!(succNode->getBB())) {
              ;
            }
            else{
              DstBB = cast<const BasicBlock>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(succNode->getBB()));
            }
            if(SrcBB != DstBB){
              uint32_t cur_loc = BB2Loc[DstBB];
              uint32_t pre_loc = BB2Loc[SrcBB];
              uint32_t temp_pre_loc = pre_loc;
              pre_loc = pre_loc >> 1;
              uint32_t edge_index = cur_loc ^ pre_loc;
              uint32_t distance = (uint32_t)BBID2dis[BB_IDs[DstBB]];

              std::map<NodeID, double> distance_target;
              for (auto target_bb:targets_DT_bb){
                NodeID target_bb_id = BB_IDs[target_bb];
                if(targetID2preNodeMapBB[target_bb_id].count(DstBB)){
                  distance_target[target_bb_id] = targetID2preNodeMapBB[target_bb_id][DstBB];

                }else{
                  distance_target[target_bb_id] = -1;
                }
              }

              outfile << "bbid: " << BB_IDs[DstBB] << " pre_loc: " << temp_pre_loc << " cur_loc: " << cur_loc << " branch_index: " << edge_index << " distance: " << distance << "\n";
              outfile5 << edge_index << " " << cur_loc << " "<< distance<< "\n";
              outfile3 << "branch_index: " << edge_index << " distance: " << distance << "\n";
              if(distance<(uint32_t)(-1)){
                outfile4 << edge_index << " " << distance << "\n";
              }
              int i = 0;
              for(auto target_bb:targets_DT_bb){
                NodeID target_bb_id = BB_IDs[target_bb];
                if(targetID2preNodeMapBB[target_bb_id].count(DstBB)){
                  uint32_t distance_target_temp = targetID2preNodeMapBB[target_bb_id][DstBB];
                  if(distance_target_temp<(uint32_t)(-1)){
                    files[i] << edge_index << " " << distance_target_temp << "\n";
                  }
                }
                if(targets_suf_data_bb_target[target_bb_id].count(DstBB)){
                  files_data[i] << edge_index << " \n";
                  outfile7 << edge_index << " \n";
                }
                i++;
              }
            }

            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }
    outfile <<"BBnum: "<<num<< " total: " << visited_bb.size() << "\n";

    outfile.close();
    outfile2.close();
    outfile3.close();
    outfile4.close();
    outfile5.close();    
    outfile6.close();
    outfile7.close();
    for (int i = 0; i < files.size(); i++) {
      files[i].close();
      files_data[i].close();
    }
}

int main(int argc, char ** argv) {
    int arg_num = 0;
    char **arg_value = new char*[argc];
    std::vector<std::string> moduleNameVec;
    LLVMUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    std::string firstElement = moduleNameVec.front();
    std::cout << firstElement << std::endl; 
    for (const std::string& str : moduleNameVec) {
      
        std::cout << str << std::endl;
    }

    cl::ParseCommandLineOptions(arg_num, arg_value,
                                "analyze the vinilla distance of bb\n");

    svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
    SVFIRBuilder builder(svfModule);
    SVFIR *svfir = builder.build();
    AndersenWaveDiff *ander = AndersenWaveDiff::createAndersenWaveDiff(svfir);
    
    SVFGBuilder svfBuilder(true);
    svfg = svfBuilder.buildFullSVFG(ander);

    icfg = svfir->getICFG();

    PTACallGraph* callgraph = ander->getPTACallGraph();
    icfg->updateCallGraph(callgraph);
    
    svfg->updateCallGraph(ander);

    for (Module& Mi : LLVMModuleSet::getLLVMModuleSet()->getLLVMModules()){
          errs() << "ModuleName: " << Mi.getName().str() << "\n";
          if (Mi.getName().str() == firstElement) {
              M = &Mi;
          }
    }
    C = &(LLVMModuleSet::getLLVMModuleSet()->getContext());

    std::cout << "loadTargets..." << std::endl;
    std::vector<NodeID> target_ids = loadTargets(TargetsFile);
    std::cout << "caculate vanilla distance..." << std::endl;
    instrument_orig();

    std::cout << "findTargetControl..." << std::endl;
    findTargetControl(target_ids);
    std::cout << "findTargetUse..." << std::endl;
    findTargetUse(svfg,0);
    std::cout << "instrument distance..." << std::endl;
    instrument();
    std::cout << "instrument suffix..." << std::endl;
    instrumentSuffix();
    std::cout << "ci.bc..." << std::endl;
    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".ci.bc");

    std::cout << "buildBranchInfo..." << std::endl;
    buildBranchInfo(target_ids);

    return 0;
}