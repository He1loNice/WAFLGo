/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <map>
#include <set>
#include <random>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
using namespace llvm;
using namespace std;

static llvm::cl::opt<bool> Instrument("notI",cl::desc("Instrument prev_loc?"),cl::init(false));

std::set<BasicBlock*> all_suffix;
std::map<uint32_t, BasicBlock *> ID2BB;
std::map< BasicBlock *,uint32_t> BB2ID;
std::map<uint32_t, uint32_t> edge_dis;
std::map<uint32_t,std::map<uint32_t, uint32_t>> edge_dis_target;
std::map<uint32_t,std::set<uint32_t>> bb_suffix_data_target;
std::set<uint32_t> bb_suffix_data;
std::map<uint32_t,std::map<uint32_t,uint32_t>> bb_suffix_data_target_map;
std::map<uint32_t,uint32_t> bb_suffix_data_target_num;
std::map<uint32_t,uint32_t> bb_suffix_data_map;
uint32_t bb_suffix_data_num;
vector<uint32_t> target_ids;
std::map<uint32_t, uint32_t> curloc_edge;
std::map<uint32_t, int> edge_order;
std::map<uint32_t,std::map<uint32_t, int>> edge_order_target;
u32 targets_num = 0;
u32 total_suffix_num;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

  };

}

Module* M2;
char AFLCoverage::ID = 0;

void readSuffix() {
  FILE* suffix_file = fopen("suffix.txt","r");
  char buf[1024];
  if (suffix_file==NULL){
    errs() << "suffix.txt not exist\n";
    return;
  }

	errs() << "loading suffix...\n" ;
  
  
  if(fgets(buf,sizeof(buf),suffix_file)!=NULL){
    char *token;
    token = strtok(buf," ");    
    total_suffix_num = atoi(token);
  }

  int target_id=0;
  while(fgets(buf, sizeof(buf), suffix_file) != NULL) {
    char* token;
    token = strtok(buf, " ");
    int temp_target_id = atoi(token);
    token = strtok(NULL, " ");
    int suffix_id = atoi(token);
    if (temp_target_id != target_id)
    {
      target_id = temp_target_id;
    }

    all_suffix.insert(ID2BB[suffix_id]);
	}
  fclose(suffix_file);

}

void readreadTargetBranches_data(){
  FILE* targetbranch_file = fopen("branch-distance-min-data.txt","r");

  char buf[1024];
  if (targetbranch_file==NULL){
    errs() << "branch-distance-min-data.txt not exist\n";
    return;
  }

  while(fgets(buf, sizeof(buf), targetbranch_file) != NULL) {
    char* token;
    token = strtok(buf, " ");
    uint32_t edge_index = atoi(token);
    auto result = bb_suffix_data.insert(edge_index);
      if(result.second){
        bb_suffix_data_num++;
      }
  }

  fclose(targetbranch_file);
  ofstream outfile_out1("branch-distance-min-data-order.txt", std::ios::out);

    std::vector<uint32_t> elements(bb_suffix_data.begin(), bb_suffix_data.end());
    std::mt19937 g(994); 
    std::shuffle(elements.begin(), elements.end(), g);
    for (int j = 0; j < std::min(static_cast<int>(elements.size()), MAX_DATA_SUFFIX); j++) {
        bb_suffix_data_map.insert({elements[j], j});
        outfile_out1 << elements[j] << " " << j << "\n";
    }

    outfile_out1.close();

  errs() << "\n\ntarget_ids size: " << target_ids.size() << "\n\n";

  for (int i = 0; i < target_ids.size();i++){
    bb_suffix_data_target_num[target_ids[i]] = 0;
    string filename = to_string(target_ids[i]) + "_edge_suffix_data.txt";
    string filename_out = to_string(target_ids[i]) + "_edge_suffix_data-order.txt";
    ofstream outfile_out(filename_out.c_str(), std::ios::out);
    FILE* targetbranch_file_target = fopen(filename.c_str(),"r");
    if (targetbranch_file_target==NULL){
      errs() << filename<< " not exist\n";
      return;
    }    
    errs() << "read from " << filename << " \n";
    while(fgets(buf, sizeof(buf), targetbranch_file_target) != NULL) {
      char* token;
      token = strtok(buf, " ");
      uint32_t edge_index = atoi(token);
      auto result = bb_suffix_data_target[target_ids[i]].insert(edge_index);
      if(result.second){
        bb_suffix_data_target_num[target_ids[i]]++;
      }

    }
    fclose(targetbranch_file_target);

    std::vector<uint32_t> elements(bb_suffix_data_target[target_ids[i]].begin(), bb_suffix_data_target[target_ids[i]].end());
    std::mt19937 g(994); 
    std::shuffle(elements.begin(), elements.end(), g);
    for (int j = 0; j < std::min(static_cast<int>(elements.size()), MAX_DATA_SUFFIX); j++) {
        bb_suffix_data_target_map[target_ids[i]].insert({elements[j], j});
        outfile_out << elements[j] << " " << j << "\n";
    }

    outfile_out.close();
  }

}

void readTargetBranches(){
  FILE* targetbranch_file = fopen("branch-distance-min.txt","r");
  FILE *targetid_file = fopen("targets_id.txt", "r");

  char buf[1024];
  if (targetbranch_file==NULL){
    errs() << "branch-distance-min.txt not exist\n";
    return;
  }
  if (targetid_file==NULL){
    errs() << "targets_id.txt not exist\n";
    return;
  }
	errs() << "loading targets_id.txt...\n";
  while(fgets(buf,sizeof(buf),targetid_file)!=NULL){
    target_ids.emplace_back(atoi(buf));
  }

  for (int i = 0; i < target_ids.size();i++){
    string filename = to_string(target_ids[i]) + "_distance.txt";
    FILE* targetbranch_file_target = fopen(filename.c_str(),"r");
    if (targetbranch_file_target==NULL){
      errs() << filename<< " not exist\n";
      return;
    }    
    errs() << "read from " << filename << " \n";
    while(fgets(buf, sizeof(buf), targetbranch_file_target) != NULL) {
      char* token;
      token = strtok(buf, " ");
      uint32_t edge_index = atoi(token);
      token = strtok(NULL, " ");
      uint32_t distance = atoi(token);
      edge_dis_target[target_ids[i]][edge_index] = distance;
    }
    fclose(targetbranch_file_target);
  }

  errs() << "loading branch-distance-min...\n";
  int num = 0;

  while(fgets(buf, sizeof(buf), targetbranch_file) != NULL) {
    char* token;
    token = strtok(buf, " ");
    uint32_t edge_index = atoi(token);
    token = strtok(NULL, " ");
    uint32_t distance = atoi(token);
    edge_dis[edge_index] = distance;
    num++;

  }

  fclose(targetbranch_file);
  fclose(targetid_file);

  ofstream outfile4("branch-distance-order.txt", std::ios::out);
  ofstream outfile5("branch-distance-order-total.txt", std::ios::out);

  vector<ofstream> files_out;
  vector<ofstream> files_out_dis;
  for (int i = 0; i < target_ids.size();i++){
    string filename = to_string(target_ids[i]) + "-distance-order.txt";
    string filename_dis= to_string(target_ids[i]) + "-distance-order-total.txt";
    files_out.emplace_back(filename);
    files_out_dis.emplace_back(filename_dis);

      
    std::vector<pair<uint32_t, uint32_t>> arr;
    for (auto it = edge_dis_target[target_ids[i]].begin(); it != edge_dis_target[target_ids[i]].end();++it){
      arr.push_back(make_pair(it->first, it->second));
    }
    std::sort(arr.begin(), arr.end(), [](const pair<int, int> &x, const pair<int, int> &y) -> int
        { return x.second < y.second; });

    int order = 0;
    for (auto it = arr.begin(); it != arr.end();it++){
      edge_order_target[target_ids[i]][it->first] = order;
      files_out[i]<<it->first << " " << order << "\n";
      files_out_dis[i]<<it->first << " "<< it->second<<" " << order  <<"\n";
      order++;
    }

    files_out[i].close();
    files_out_dis[i].close();
  }

  std::vector<pair<uint32_t, uint32_t>> arr;
  for (auto it = edge_dis.begin(); it != edge_dis.end();++it){
    arr.push_back(make_pair(it->first, it->second));
  }
  std::sort(arr.begin(), arr.end(), [](const pair<int, int> &x, const pair<int, int> &y) -> int
       { return x.second < y.second; });

  int order = 0;
  for (auto it = arr.begin(); it != arr.end();it++){
    edge_order[it->first] = order;
    outfile4 << it->first << " " << order << "\n";
    outfile5 << it->first << " "<< it->second<<" " << order  <<"\n";
    order++;
  }

  outfile4.close();
  outfile5.close();
}

void readTargetsNum(){
  FILE* targets_file = fopen("/home/targets.txt","r");
  FILE* curloc_file = fopen("/home/branch-curloc.txt","r");
  
  char buf[1024];
  
  if (targets_file==NULL)
    FATAL("targets.txt not exist");

  while(fgets(buf, sizeof(buf), targets_file) != NULL) {
    targets_num++;
  }
  errs() << "targets_num: " << targets_num << "\n";

  if (curloc_file==NULL)
    FATAL("branch-curloc.txt not exist");

  while(fgets(buf, sizeof(buf), curloc_file) != NULL) {
    char* token;
    token = strtok(buf, " ");
    uint32_t edge_index = atoi(token);
    token = strtok(NULL, " ");
    uint32_t cur_loc = atoi(token);

    // edge_curloc[edge_index] = cur_loc;
    curloc_edge[cur_loc] = edge_index;
  }
  fclose(targets_file);
  fclose(curloc_file);
}



static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}


std::string getDebugInfo(BasicBlock* bb) {
	for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it) {
		Instruction* inst = &(*it);

    std::string filename;
    unsigned line;
		getDebugLoc(inst, filename, line);

    if (filename.empty() || line == 0 )
      continue;

    filename +=  to_string(line);
    return filename;
    // if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos)
    //   return str;
  }
	return "{ }";
}

void setBBID(Module &M){
	ofstream outfile("bbinfo-fast.txt", std::ios::out);

  uint32_t bb_id = 0;
  for (auto &F : M)
  {
    for(auto &BB:F){
      if(getDebugInfo(&BB).find("/usr/") == string::npos ){

        ID2BB[bb_id] = &BB;
        BB2ID[&BB] = bb_id;
        bb_id++;
				outfile << getDebugInfo(&BB) << std::endl;
      }
    }
  }
  errs() << "total bb_id: " << bb_id << "\n";

  readSuffix();
  readTargetBranches();
  readreadTargetBranches_data();
  readTargetsNum();
}

bool AFLCoverage::runOnModule(Module &M) {
  ofstream outfile("edges.txt", std::ios::out);
  srandom(994);

  LLVMContext &C = M.getContext();

  M2 = &M;

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  IntegerType *LargestType = Int64Ty;


  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */
  
	GlobalVariable *AFLMapPtr = (GlobalVariable*)M.getOrInsertGlobal("__afl_area_ptr",PointerType::get(Int8Ty, 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M2, PointerType::get(IntegerType::getInt8Ty(M2->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
  });
  GlobalVariable *AFLMapPtrSuf = (GlobalVariable*)M.getOrInsertGlobal("__afl_area_ptr_suf",PointerType::get(Int8Ty, 0),[]() -> GlobalVariable* {
      return new GlobalVariable(*M2, PointerType::get(IntegerType::getInt8Ty(M2->getContext()), 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr_suf");
  });

  if(Instrument){
    errs() << "Not Instrument __afl_prev_loc\n";
    return true;
  }

  errs() << "Yes Instrument __afl_prev_loc\n";

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  ConstantInt *One = ConstantInt::get(LargestType, 1);
  ConstantInt *zero = ConstantInt::get(Int32Ty, 0);

  ConstantInt *MapNotPreLoc = ConstantInt::get(LargestType, MAP_SIZE + 48);

  /* Instrument all the things! */

  int inst_blocks = 0;

  setBBID(M);

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      outfile <<"bbid: "<<BB2ID[&BB]<<" cur_loc: " << cur_loc << " bbinfo: "<< getDebugInfo(&BB)<<" \n";

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      uint32_t edge_index = curloc_edge[cur_loc];

      if(edge_order.find(edge_index) != edge_order.end()){
        if(edge_order[edge_index] < MAX_RARE_BRANCHES ){
          
          ConstantInt *TFlagLoc =
              ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + targets_num + edge_order[edge_index]);
          Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
          ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
          IRB.CreateStore(FlagOne, TFlagPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        }
      }
      
      for(int i = 0; i < target_ids.size();i++){
        if(edge_order_target[target_ids[i]].find(edge_index) != edge_order_target[target_ids[i]].end()){
          if(edge_order_target[target_ids[i]][edge_index] < MAX_RARE_BRANCHES ){
            ConstantInt *TFlagLoc =
                ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + targets_num + MAX_RARE_BRANCHES * (i+1) + edge_order_target[target_ids[i]][edge_index]);
            Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
            ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
            IRB.CreateStore(FlagOne, TFlagPtr)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          }
        }

      }

      if(bb_suffix_data_map.find(edge_index) != bb_suffix_data_map.end()){
          if(bb_suffix_data_map[edge_index] < MAX_DATA_SUFFIX){
          ConstantInt *TFlagLoc =
              ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + targets_num + MAX_RARE_BRANCHES * (targets_num+1) + bb_suffix_data_map[edge_index]);
          Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
          ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
          IRB.CreateStore(FlagOne, TFlagPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          }
        
      }

      for(int i = 0; i < target_ids.size();i++){
        if(bb_suffix_data_target_map[target_ids[i]].find(edge_index) != bb_suffix_data_target_map[target_ids[i]].end()){
          if(bb_suffix_data_target_map[target_ids[i]][edge_index] < MAX_DATA_SUFFIX ){
            ConstantInt *TFlagLoc =
                ConstantInt::get(LargestType, MAP_SIZE + 16 + 16 + 16 + 16 + TARGETS_NUM * 16 + targets_num + MAX_RARE_BRANCHES * (targets_num+1) + MAX_DATA_SUFFIX * (i+1) + bb_suffix_data_target_map[target_ids[i]][edge_index]);
            Value* TFlagPtr = IRB.CreateGEP(MapPtr, TFlagLoc);
            ConstantInt *FlagOne = ConstantInt::get(Int8Ty, 1);
            IRB.CreateStore(FlagOne, TFlagPtr)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          }
        }

      }

      if(all_suffix.find(&BB)!=all_suffix.end()){
        /* Load SHM pointer */

        LoadInst *MapPtrSuf = IRB.CreateLoad(AFLMapPtrSuf);
        MapPtrSuf->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MapPtrIdxSuf =
            IRB.CreateGEP(MapPtrSuf, IRB.CreateXor(PrevLocCasted, CurLoc));

        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdxSuf);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdxSuf)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      }

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }
  outfile.close();

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
