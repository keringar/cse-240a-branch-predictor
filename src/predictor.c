//========================================================//
//  predictor.c                                           //
//  Source file for the Branch Predictor                  //
//                                                        //
//  Implement the various branch predictors below as      //
//  described in the README                               //
//========================================================//
#include <stdio.h>
#include <math.h>
#include "predictor.h"

//
// TODO:Student Information
//
const char *studentName = "Warren Hu";
const char *studentID   = "A15154462";
const char *email       = "wsh003@ucsd.edu";

//------------------------------------//
//      Predictor Configuration       //
//------------------------------------//

// Handy Global for use in output routines
const char *bpName[4] = { "Static", "Gshare",
                          "Tournament", "Custom" };

//define number of bits required for indexing the BHT here. 
int ghistoryBits = 14; // Number of bits used for Global History
int bpType;       // Branch Prediction Type
int verbose;

// the alpha-21264 tournament predictor paper uses bottom 10 bits of PC for local history but we can
// bump up the numbers to make it use up to 32 kilobits
const int tLocalPCBits = 12;
const int tGlobalHistoryBits = 12;
const int tChooserHistoryBits = 12;

//------------------------------------//
//      Predictor Data Structures     //
//------------------------------------//

//gshare
uint8_t *bht_gshare;
uint64_t ghistory;

//alpha-21264 tournament predictor
//https://acg.cis.upenn.edu/milom/cis501-Fall09/papers/Alpha21264.pdf
//   32 bits for PC
// + 12 bits for global branch history
unsigned int tHistoryTable; // past 12 branch histories

// 16384 entries * 2 bits each = 32768 bits
unsigned int* tLocalPHT; // 4096 entries (2^12)
unsigned int* tLocalCounters; // 4096 entries (2^12)
unsigned int* tGlobalCounters; // 4096 entries (2^12)
unsigned int* tChooserCounters; // 4096 entries (2^12)

// BATAGE: https://dl.acm.org/doi/fullHtml/10.1145/3226098

//------------------------------------//
//        Predictor Functions         //
//------------------------------------//

// Initialize the predictor
//

//gshare functions
void init_gshare() {
 int bht_entries = 1 << ghistoryBits;
  bht_gshare = (uint8_t*)malloc(bht_entries * sizeof(uint8_t));
  int i = 0;
  for(i = 0; i< bht_entries; i++){
    bht_gshare[i] = WN;
  }
  ghistory = 0;
}



uint8_t 
gshare_predict(uint32_t pc) {
  //get lower ghistoryBits of pc
  uint32_t bht_entries = 1 << ghistoryBits;
  uint32_t pc_lower_bits = pc & (bht_entries-1);
  uint32_t ghistory_lower_bits = ghistory & (bht_entries -1);
  uint32_t index = pc_lower_bits ^ ghistory_lower_bits;
  switch(bht_gshare[index]){
    case WN:
      return NOTTAKEN;
    case SN:
      return NOTTAKEN;
    case WT:
      return TAKEN;
    case ST:
      return TAKEN;
    default:
      printf("Warning: Undefined state of entry in GSHARE BHT!\n");
      return NOTTAKEN;
  }
}

void
train_gshare(uint32_t pc, uint8_t outcome) {
  //get lower ghistoryBits of pc
  uint32_t bht_entries = 1 << ghistoryBits;
  uint32_t pc_lower_bits = pc & (bht_entries-1);
  uint32_t ghistory_lower_bits = ghistory & (bht_entries -1);
  uint32_t index = pc_lower_bits ^ ghistory_lower_bits;

  //Update state of entry in bht based on outcome
  switch(bht_gshare[index]){
    case WN:
      bht_gshare[index] = (outcome==TAKEN)?WT:SN;
      break;
    case SN:
      bht_gshare[index] = (outcome==TAKEN)?WN:SN;
      break;
    case WT:
      bht_gshare[index] = (outcome==TAKEN)?ST:WN;
      break;
    case ST:
      bht_gshare[index] = (outcome==TAKEN)?ST:WT;
      break;
    default:
      printf("Warning: Undefined state of entry in GSHARE BHT!\n");
  }

  //Update history register
  ghistory = ((ghistory << 1) | outcome); 
}

void
cleanup_gshare() {
  free(bht_gshare);
}

// alpha tournament

void init_tournament() {
  int localBits = 1 << tLocalPCBits;

  tLocalPHT = (unsigned int*)malloc(localBits * sizeof(unsigned int));
  tLocalCounters = (unsigned int*)malloc(localBits * sizeof(unsigned int));

  for (int i = 0; i <= localBits; i++) {
    tLocalPHT[i] = 0; // bits 0000000000
    tLocalCounters[i] = WN;
  } 

  int globalBits = 1 << tGlobalHistoryBits;
  int chooserBits = 1 << tChooserHistoryBits;

  tGlobalCounters = (unsigned int*)malloc(globalBits * sizeof(unsigned int));
  tChooserCounters = (unsigned int*)malloc(chooserBits * sizeof(unsigned int));

  for (int i = 0; i <= globalBits; i++) {
    tGlobalCounters[i] = WN;
  } 

  for (int i = 0; i <= chooserBits; i++) {
    tChooserCounters[i] = WN;
  } 

  tHistoryTable = 0;
}

uint8_t tournament_predict(uint32_t pc) {
  unsigned int global_history_bits = 1 << tGlobalHistoryBits;
  unsigned int chooser_history_bits = 1 << tChooserHistoryBits;
  unsigned int global_history_lower = tHistoryTable & (global_history_bits - 1);
  unsigned int chooser_history_lower = tHistoryTable & (chooser_history_bits - 1);

  unsigned int local_pc_bits = 1 << tLocalPCBits;
  unsigned int pc_lower = pc & (local_pc_bits - 1);

  switch (tChooserCounters[chooser_history_lower]) {
    case SN:
    case WN:
      // arbitrarily assign not taken in chooser to local predictor
      switch (tLocalCounters[tLocalPHT[pc_lower]]) {
        case SN:
        case WN:
          return NOTTAKEN;
        case ST:
        case WT:
          return TAKEN;
        default:
          printf("Undefined state in tournament local table");
          return NOTTAKEN;
      }
      break;
    case ST:
    case WT:
      // arbitrarily assign taken in chooser to global predictor
      switch (tGlobalCounters[global_history_lower]) {
        case SN:
        case WN:
          return NOTTAKEN;
        case ST:
        case WT:
          return TAKEN;
        default:
          printf("Undefined state in tournament global table");
          return NOTTAKEN;
      }
      break;
    default:
      printf("Undefined state in chooser table");
      return NOTTAKEN;
  }
}

void train_tournament(uint32_t pc, uint8_t outcome) {
  unsigned int global_history_bits = 1 << tGlobalHistoryBits;
  unsigned int chooser_history_bits = 1 << tChooserHistoryBits;
  unsigned int global_history_lower = tHistoryTable & (global_history_bits - 1);
  unsigned int chooser_history_lower = tHistoryTable & (chooser_history_bits - 1);

  unsigned int local_pc_bits = 1 << tLocalPCBits;
  unsigned int pc_lower = pc & (local_pc_bits - 1);

  // get local predictor choice and update counter
  unsigned int local_predictor_choice;
  switch (tLocalCounters[tLocalPHT[pc_lower]]) {
    case SN:
      local_predictor_choice = NOTTAKEN;    

      if (outcome == TAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]++;
      } 
      break;
    case WN:
      local_predictor_choice = NOTTAKEN;

      if (outcome == TAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]++;
      } else if (outcome == NOTTAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]--;
      }
      break;
    case ST:
      local_predictor_choice = TAKEN;

      if (outcome == NOTTAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]--;
      }
      break;
    case WT:
      local_predictor_choice = TAKEN;

      if (outcome == TAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]++;
      } else if (outcome == NOTTAKEN) {
        tLocalCounters[tLocalPHT[pc_lower]]--;
      }
      break;
    default:
      printf("Undefined state in tournament local table");
      local_predictor_choice = NOTTAKEN;
  }

  // get global predictor choice and update counter
  unsigned int global_predictor_choice;
  switch (tGlobalCounters[global_history_lower]) {
    case SN:
      global_predictor_choice = NOTTAKEN;
      
      if (outcome == TAKEN) {
        tGlobalCounters[global_history_lower]++;
      } 
      break;
    case WN:
      global_predictor_choice = NOTTAKEN;

      if (outcome == TAKEN) {
        tGlobalCounters[global_history_lower]++;
      } else if (outcome == NOTTAKEN) {
        tGlobalCounters[global_history_lower]--;
      }
      break;
    case ST:
      global_predictor_choice = TAKEN;

      if (outcome == NOTTAKEN) {
        tGlobalCounters[global_history_lower]--;
      } 
      break;
    case WT:
      global_predictor_choice = TAKEN;

      if (outcome == TAKEN) {
        tGlobalCounters[global_history_lower]++;
      } else if (outcome == NOTTAKEN) {
        tGlobalCounters[global_history_lower]--;
      }
      break;
    default:
      printf("Undefined state in tournament global table");
      global_predictor_choice = NOTTAKEN;
  }

  // compare actual outcome to both predictor choices and update choooser accordingly
  if (local_predictor_choice == NOTTAKEN && global_predictor_choice == NOTTAKEN && outcome == NOTTAKEN) {
    // both right, dont change anything
  } else if (local_predictor_choice == NOTTAKEN && global_predictor_choice == NOTTAKEN && outcome == TAKEN) {
    // both wrong, dont change anything
  } else if (local_predictor_choice == NOTTAKEN && global_predictor_choice == TAKEN && outcome == NOTTAKEN) {
    // local predictor is correct, bias chooser towards not taken
    if (tChooserCounters[chooser_history_lower] > SN) {
      tChooserCounters[chooser_history_lower]--;
    }
  } else if (local_predictor_choice == NOTTAKEN && global_predictor_choice == TAKEN && outcome == TAKEN) {
    // global predictor is correct, bias chooser towards taken
    if (tChooserCounters[chooser_history_lower] < ST) {
      tChooserCounters[chooser_history_lower]++;
    }
  } else if (local_predictor_choice == TAKEN && global_predictor_choice == NOTTAKEN && outcome == NOTTAKEN) {
    // global predictor is correct, bias chooser towards taken
    if (tChooserCounters[chooser_history_lower] < ST) {
      tChooserCounters[chooser_history_lower]++;
    }
  } else if (local_predictor_choice == TAKEN && global_predictor_choice == NOTTAKEN && outcome == TAKEN) {
    // local predictor is correct, bias chooser towards not taken
    if (tChooserCounters[chooser_history_lower] > SN) {
      tChooserCounters[chooser_history_lower]--;
    }
  } else if (local_predictor_choice == TAKEN && global_predictor_choice == TAKEN && outcome == NOTTAKEN) {
    // both wrong, dont change anything
  } else if (local_predictor_choice == TAKEN && global_predictor_choice == TAKEN && outcome == TAKEN) {
    // both right, dont change anything
  } else {
    printf("Undefined state in tournament predictor choices");
  }

  // update global history
  tHistoryTable = (tHistoryTable << 1) | outcome;

  // update local pattern history table
  tLocalPHT[pc_lower] = ((tLocalPHT[pc_lower] << 1) | outcome) & (local_pc_bits - 1);
}

void
init_predictor()
{
  switch (bpType) {
    case STATIC:
    case GSHARE:
      init_gshare();
      break;
    case TOURNAMENT:
      init_tournament();
      break;
    case CUSTOM:
    default:
      break;
  }
  
}

// Make a prediction for conditional branch instruction at PC 'pc'
// Returning TAKEN indicates a prediction of taken; returning NOTTAKEN
// indicates a prediction of not taken
//
uint8_t
make_prediction(uint32_t pc)
{

  // Make a prediction based on the bpType
  switch (bpType) {
    case STATIC:
      return TAKEN;
    case GSHARE:
      return gshare_predict(pc);
    case TOURNAMENT:
      return tournament_predict(pc);
    case CUSTOM:
    default:
      break;
  }

  // If there is not a compatable bpType then return NOTTAKEN
  return NOTTAKEN;
}

// Train the predictor the last executed branch at PC 'pc' and with
// outcome 'outcome' (true indicates that the branch was taken, false
// indicates that the branch was not taken)
//

void
train_predictor(uint32_t pc, uint8_t outcome)
{

  switch (bpType) {
    case STATIC:
    case GSHARE:
      return train_gshare(pc, outcome);
    case TOURNAMENT:
      return train_tournament(pc, outcome);
    case CUSTOM:
    default:
      break;
  }
  

}
