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

// TAGE: https://www.irisa.fr/caps/people/seznec/JILP-COTTAGE.pdf
// BATAGE: https://dl.acm.org/doi/fullHtml/10.1145/3226098
// From the TAGE paper, pick an 5 component TAGE due to limited space
// Each table contains a 10 bit hash computed from PC and global branch history
//                     a 2 bit saturating taken unsigned counter
//                     a 2 bit saturating not taken unsigned counter
// each table entry needs to be 14 bits long to maximize use of the 32kbits.
// base predictor (table 0) is a simple bimodal predictor. needs 2^(15-4) = 2048 entries
// each of the other 4 tables has2^(15-6) = 512 entries
uint16_t* tage_table[5];

const int tage_ti_tag_bits = 10;
const int tage_ti_counter_size = 2;
const int tage_t0_pc_bits = 11;
const int tage_t1_history_bits = 8;
const int tage_t2_history_bits = 16;
const int tage_t3_history_bits = 32;
const int tage_t4_history_bits = 64;
const int tage_table_size_bits = 9;
const int tage_num_components = 5;

uint64_t tage_global_history; // 64 bits
uint8_t tage_table_used_to_predict; // 3 bits
uint8_t tage_table_hit[5]; // 5 bits
uint8_t tage_hit_confidence[5]; // 10 bits
uint8_t tage_prediction[5]; // 5 bits
uint8_t tage_actual_prediction; // 1 bit
uint16_t tage_calculated_indices[5]; // 11 + 9*4 = 47 bits
uint16_t tage_calculated_tags[5]; // 0 + 4*10 = 40 bits

//------------------------------------//
//        Helper Functions            //
//------------------------------------//

// see section 2.1 of https://jilp.org/vol7/v7paper10.pdf for details on the hashing
void tage_calculate_indices_and_tags(uint32_t pc, uint64_t global_history) {
  tage_calculated_indices[0] = pc & ((1 << tage_t0_pc_bits) - 1);
  tage_calculated_tags[0] = 0; // table 0 is tagless bimodal

  // see section 2.1 of https://jilp.org/vol7/v7paper10.pdf
  unsigned int tage_table_size_mask = (1 << tage_table_size_bits) - 1;
  unsigned int tage_tag_size_mask = (1 << tage_ti_tag_bits) - 1;

  unsigned int tage_t1_history_mask = (1 << tage_t1_history_bits) - 1;
  unsigned int tage_t1_history = global_history & tage_t1_history_mask;
  tage_calculated_indices[1] = (pc ^ tage_t1_history) & tage_table_size_mask;
  tage_calculated_tags[1] = (pc ^ tage_t1_history) & tage_tag_size_mask;

  unsigned int tage_t2_history_mask = (1 << tage_t2_history_bits) - 1;
  unsigned int tage_t2_history = global_history & tage_t2_history_mask; // 16 bits. need to fold down to 9 index bits. 2 folds
  tage_calculated_indices[2] = (pc ^ (tage_t2_history) ^ (tage_t2_history >> tage_table_size_mask)) & tage_table_size_mask;
  tage_calculated_tags[2] = (pc ^ (tage_t2_history) ^ (tage_t2_history >> tage_ti_tag_bits)) & tage_tag_size_mask;

  unsigned int tage_t3_history_mask = (1 << tage_t3_history_bits) - 1;
  unsigned int tage_t3_history = global_history & tage_t3_history_mask; // 32 bits. need to fold down to 9 index bits. 4 folds
  tage_calculated_indices[3] = (pc ^ (tage_t3_history) ^ (tage_t3_history >> tage_table_size_bits) ^ (tage_t3_history >> (2 * tage_table_size_bits)) ^ (tage_t3_history >> (3 * tage_table_size_bits))) & tage_table_size_mask;
  tage_calculated_tags[3] = (pc ^ (tage_t3_history) ^ (tage_t3_history >> tage_ti_tag_bits) ^ (tage_t3_history >> (2 * tage_ti_tag_bits)) ^ (tage_t3_history >> (3 * tage_ti_tag_bits))) & tage_tag_size_mask;

  unsigned int tage_t4_history_mask = (1 << tage_t4_history_bits) - 1;
  unsigned int tage_t4_history = global_history & tage_t4_history_mask; // 64 bits. need to fold down to 9 index bits. 8 folds
  tage_calculated_indices[4] = (pc ^ 
                           (tage_t4_history) ^
                           (tage_t4_history >> tage_table_size_bits) ^
                           (tage_t4_history >> (2 * tage_table_size_bits)) ^
                           (tage_t4_history >> (3 * tage_table_size_bits)) ^
                           (tage_t4_history >> (4 * tage_table_size_bits)) ^
                           (tage_t4_history >> (5 * tage_table_size_bits)) ^
                           (tage_t4_history >> (6 * tage_table_size_bits)) ^
                           (tage_t4_history >> (7 * tage_table_size_bits))
                          ) & tage_table_size_mask;
  tage_calculated_tags[4] = (pc ^
                           (tage_t4_history) ^
                           (tage_t4_history >> tage_ti_tag_bits) ^
                           (tage_t4_history >> (2 * tage_ti_tag_bits)) ^
                           (tage_t4_history >> (3 * tage_ti_tag_bits)) ^
                           (tage_t4_history >> (4 * tage_ti_tag_bits)) ^
                           (tage_t4_history >> (5 * tage_ti_tag_bits)) ^
                           (tage_t4_history >> (6 * tage_ti_tag_bits)) ^
                           (tage_t4_history >> (7 * tage_ti_tag_bits))
                          ) & tage_tag_size_mask;
}

// see section 4.2 of https://dl.acm.org/doi/fullHtml/10.1145/3226098
uint8_t tage_calculate_confidence(unsigned int taken_counter, unsigned int not_taken_counter) {
  uint8_t med = (taken_counter == (2 * not_taken_counter + 1)) || (not_taken_counter == (2 * taken_counter + 1)) ? 1 : 0;
  uint8_t low = (taken_counter <  (2 * not_taken_counter + 1)) && (not_taken_counter <  (2 * taken_counter + 1)) ? 1 : 0;
  
  return med | (low << 1);
}

void tage_update_counters(uint8_t outcome, uint16_t* taken, uint16_t* not_taken) {
  if (outcome == TAKEN) {
    // taken and not_taken are 2 bit unsigned saturating counters
    if ((*taken) < 3) {
      (*taken)++;
    } else if ((*not_taken) > 0) {
      (*not_taken)--;
    }
  } else {
    if ((*not_taken) < 3) {
      (*not_taken)++;
    } else if (taken > 0) {
      (*taken)--;
    }
  }
}

// bit packing helper macros
#define GET_T(tage_entry) (tage_entry & ((1 << tage_ti_counter_size) - 1))
#define GET_NT(tage_entry) ((tage_entry >> tage_ti_counter_size) & ((1 << tage_ti_counter_size) - 1))
#define GET_TAG(tage_entry) ((tage_entry >> (tage_ti_counter_size * 2)) & ((1 << tage_ti_tag_bits) - 1))
#define MAKE_ENTRY(tage_tag, tage_t_counter, tage_nt_counter) (((tage_tag & ((1 << tage_ti_tag_bits) - 1)) << (tage_ti_counter_size * 2)) | ((tage_nt_counter & ((1 << tage_ti_counter_size) - 1)) << tage_ti_counter_size) | (tage_t_counter & ((1 << tage_ti_counter_size) - 1)))

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

// custom (BATAGE)

void init_custom() {
  unsigned int t0_entries = 1 << tage_t0_pc_bits;
  tage_table[0] = malloc(sizeof(uint16_t) * t0_entries);
  for (int i = 0; i < t0_entries; i++) {
    tage_table[0][i] = WN;
  }

  unsigned int tage_table_size = 1 << tage_table_size_bits;

  tage_table[1] = malloc(sizeof(uint16_t) * tage_table_size);
  tage_table[2] = malloc(sizeof(uint16_t) * tage_table_size);
  tage_table[3] = malloc(sizeof(uint16_t) * tage_table_size);
  tage_table[4] = malloc(sizeof(uint16_t) * tage_table_size);
  
  for (int i = 0; i < tage_table_size; i++) {
    // set up and down counters to weakly not taken and leave tag equal to 0
    tage_table[1][i] = MAKE_ENTRY(0xFE, 0, 1); 
    tage_table[2][i] = MAKE_ENTRY(0xFE, 0, 1); 
    tage_table[3][i] = MAKE_ENTRY(0xFE, 0, 1); 
    tage_table[4][i] = MAKE_ENTRY(0xFE, 0, 1); 
  }

  tage_global_history = 0;
}

// see PPM paper for how the indices and hashing work 
// https://jilp.org/vol7/v7paper10.pdf
uint8_t custom_predict(uint32_t pc) {
  tage_calculate_indices_and_tags(pc, tage_global_history);
  
  // reset tage table hit tracker
  tage_table_hit[0] = 1;
  tage_table_hit[1] = 0;
  tage_table_hit[2] = 0;
  tage_table_hit[3] = 0;
  tage_table_hit[4] = 0;

  // track current best prediction and current best confidence level
  unsigned int prediction = NOTTAKEN;
  unsigned int confidence_level = LOW_CONF;

  // loop through all the tables and find the prediction with the longest history
  for (int i = 0; i < tage_num_components; i++) {
    if (i == 0) {
      // table 0 is a simple bimodal predictor
      // see table 1 of https://dl.acm.org/doi/fullHtml/10.1145/3226098 for details of confidence levels
      switch(tage_table[0][tage_calculated_indices[0]]) {
        case WN:
          prediction = NOTTAKEN;
          confidence_level = LOW_CONF;
          break;
        case SN:
          prediction = NOTTAKEN;
          confidence_level = MED_CONF;
          break;
        case WT:
          prediction = TAKEN;
          confidence_level = LOW_CONF;
          break;
        case ST:
          prediction = TAKEN;
          confidence_level = MED_CONF;
          break;
        default:
          printf("Warning: Undefined state of entry in TAGE t0!\n");
          prediction = NOTTAKEN;
          confidence_level = LOW_CONF;
      }

      tage_hit_confidence[i] = confidence_level;
      tage_prediction[i] = prediction;
      tage_table_used_to_predict = 0;
    } else {
      // tage tables
      uint16_t tage_entry = tage_table[i][tage_calculated_indices[i]];
      
      tage_hit_confidence[i] = tage_calculate_confidence(GET_T(tage_entry), GET_NT(tage_entry));
      tage_prediction[i] = GET_T(tage_entry) > GET_NT(tage_entry);

      // if tag in entry matches the calculated tag, then we have a hit
      if (GET_TAG(tage_entry) == tage_calculated_tags[i]) {
        tage_table_hit[i] = 1;

        // if the hit confidence is at least as good as the current best confidence level, then
        // overwrite current prediction as the current hit matches a longer history table
        if (tage_hit_confidence[i] <= confidence_level) {
          tage_table_used_to_predict = i;
          confidence_level = tage_hit_confidence[i];
          prediction = tage_prediction[i];
        }
      }
    }
  }

  // store the final prediction result in order to detect mispredicts
  tage_actual_prediction = prediction;
  return prediction;
}

void train_custom(uint32_t pc, uint8_t outcome) {
  tage_calculate_indices_and_tags(pc, tage_global_history);

  // see table 3 of https://dl.acm.org/doi/fullHtml/10.1145/3226098
  // update all matching tables that came after the table used to predict
  // the later entries were probably skipped because they were cold so update with
  // the branch direction to try and increase confidence
  for (int table_idx = tage_table_used_to_predict + 1; table_idx < tage_num_components; table_idx++) {
    if (tage_table_hit[table_idx]) {
      uint16_t tage_entry = tage_table[table_idx][tage_calculated_indices[table_idx]];

      uint16_t taken = GET_T(tage_entry);
      uint16_t not_taken = GET_NT(tage_entry);
      tage_update_counters(outcome, &taken, &not_taken);

      tage_table[table_idx][tage_calculated_indices[table_idx]] = MAKE_ENTRY(GET_TAG(tage_entry), taken, not_taken);
    }
  }

  // find the last hitting entry before the choosen table
  uint8_t penultimate_table = -1;
  for (int i = 0; i < tage_table_used_to_predict; i++) {
    if (tage_table_hit[i]) {
      penultimate_table = i;
    }
  }

  // If the previous entry was also a good result (high confidence and correct), then
  // we probably don't need the later entry taking up space, so decay the entry
  // we used to predict since it probably isn't useful. Decrementing the counters will
  // decrease the confidence level
  if (tage_table_used_to_predict > 0 &&
      tage_hit_confidence[tage_table_used_to_predict] == HIGH_CONF &&
      tage_hit_confidence[penultimate_table] == HIGH_CONF &&
      tage_prediction[penultimate_table] == outcome) {
    
    uint16_t tage_entry = tage_table[tage_table_used_to_predict][tage_calculated_indices[tage_table_used_to_predict]];

    uint16_t taken = GET_T(tage_entry);
    uint16_t not_taken = GET_NT(tage_entry);

    // if both are equal, then confidence is already LOW so no need to decay further
    if (taken > not_taken) {
      taken--;
    } else if (not_taken > taken) {
      not_taken--;
    }

    tage_table[tage_table_used_to_predict][tage_calculated_indices[tage_table_used_to_predict]] = MAKE_ENTRY(GET_TAG(tage_entry), taken, not_taken);
  } else {
    // Otherwise, just update the choosen entry with the branch direction

    if (tage_table_used_to_predict > 0) {
      // update the hitting entry
      uint16_t tage_entry = tage_table[tage_table_used_to_predict][tage_calculated_indices[tage_table_used_to_predict]];

      uint16_t taken = GET_T(tage_entry);
      uint16_t not_taken = GET_NT(tage_entry);
      tage_update_counters(outcome, &taken, &not_taken);

      tage_table[tage_table_used_to_predict][tage_calculated_indices[tage_table_used_to_predict]] = MAKE_ENTRY(GET_TAG(tage_entry), taken, not_taken);
    } else {
      // update the bimodal
      switch(tage_table[0][tage_calculated_indices[0]]) {
        case WN:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?WT:SN;
          break;
        case SN:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?WN:SN;
          break;
        case WT:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?ST:WN;
          break;
        case ST:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?ST:WT;
          break;
        default:
          printf("Warning: Undefined state of entry in TAGE table 0 BHT!\n");
      }
    }
  }

  // If the previous entry is not high confidence, might as well try updating it as well to
  // to potentially save some space
  if (tage_table_used_to_predict > 0 && tage_hit_confidence[tage_table_used_to_predict] != HIGH_CONF) {
    if (penultimate_table == 0) {
      // update the bimodal
      switch(tage_table[0][tage_calculated_indices[0]]) {
        case WN:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?WT:SN;
          break;
        case SN:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?WN:SN;
          break;
        case WT:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?ST:WN;
          break;
        case ST:
          tage_table[0][tage_calculated_indices[0]] = (outcome==TAKEN)?ST:WT;
          break;
        default:
          printf("Warning: Undefined state of entry in TAGE table 0 BHT!\n");
      }
    } else {
      // update the tage entry
      uint16_t tage_entry = tage_table[penultimate_table][tage_calculated_indices[penultimate_table]];

      uint16_t taken = GET_T(tage_entry);
      uint16_t not_taken = GET_NT(tage_entry);
      tage_update_counters(outcome, &taken, &not_taken);
      
      tage_table[penultimate_table][tage_calculated_indices[penultimate_table]] = MAKE_ENTRY(GET_TAG(tage_entry), taken, not_taken);
    }
  }

  // attempt to allocate new entry on mispredict
  if (tage_actual_prediction != outcome) {
    // find the next table after the hitting table with a low or medium confidence slot
    for (int table_idx = tage_table_used_to_predict + 1; table_idx < tage_num_components; table_idx++) {
      uint16_t table_entry = tage_table[table_idx][tage_calculated_indices[table_idx]];
      
      if (tage_calculate_confidence(GET_T(table_entry), GET_NT(table_entry)) != HIGH_CONF) {
        // overwrite this low/med confidence entry
        tage_table[table_idx][tage_calculated_indices[table_idx]] = MAKE_ENTRY(tage_calculated_tags[table_idx], outcome, 1 - outcome);

        break;
      }
    }
  }

  // append to global history
  tage_global_history = (tage_global_history << 1) | outcome;
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
      init_custom();
      break;
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
      return custom_predict(pc);
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
      return train_custom(pc, outcome);
    default:
      break;
  }
  

}
