// Copyright (C) 2021, Gururaj Saileshwar, Moinuddin Qureshi: Georgia Institute of Technology.

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <queue> //used for max heap
#include <tuple>
#include "mtrand.h"
#include <any>
#include <algorithm>

using namespace std;
/////////////////////////////////////////////////////
// COMMAND-LINE ARGUMENTS
/////////////////////////////////////////////////////
//argv[1] : EXTRA TAGS PER SET (PER SKEW)
int EXTRA_BUCKET_CAPACITY = 3;  //set extra tags to 1 for now!

//argv[2] : NUMBER OF BALLS THROWN
int NUM_BILLION_TRIES = 1;

//argv[3] : SEED
unsigned int myseed = 1;

/////////////////////////////////////////////////////
// DEFINES
/////////////////////////////////////////////////////
//Cache Configuration
//Default: 16 Way LLC
#ifndef CUSTOM_BASE_WAYS_PER_SKEW
#define BASE_WAYS_PER_SKEW        (8)
#else
#define BASE_WAYS_PER_SKEW        (CUSTOM_BASE_WAYS_PER_SKEW)
#endif
#define NUM_SKEWS                 (2)

//16MB LLC
#define CACHE_SZ_BYTES            (16*1024*1024) 
#define LINE_SZ_BYTES             (64)
#define NUM_BUCKETS               ((CACHE_SZ_BYTES/LINE_SZ_BYTES)/(BASE_WAYS_PER_SKEW))
#define NUM_BUCKETS_PER_SKEW      (NUM_BUCKETS/NUM_SKEWS)

//Bucket Capacities
#define BALLS_PER_BUCKET      (BASE_WAYS_PER_SKEW)
#ifndef CUSTOM_MAX_FILL
#define MAX_FILL              (16)
#else
#define MAX_FILL              (CUSTOM_MAX_FILL)
#endif
int SPILL_THRESHOLD = BALLS_PER_BUCKET + EXTRA_BUCKET_CAPACITY;

// Tie-Breaking Policy between Skews on Ball-Throws
//0 - Randomly picks either skew on Ties. 
//1 - Always picks Skew-0 on Ties.
#define BREAK_TIES_PREFERENTIALLY      (0)

//Experiment Size
//#define BILLION_TRIES             (1000*1000*1000)
#define BILLION_TRIES (1000*1000*10)
#define HUNDRED_MILLION_TRIES     (1000*1000*1)


/////////////////////////////////////////////////////

//Types
typedef unsigned int uns;
typedef unsigned long long uns64;
typedef double dbl;

/////////////////////////////////////////////////////
// EXPERIMENT VARIABLES
/////////////////////////////////////////////////////

//For each Bucket (Set), number of Balls in Bucket
//(Data-Structure Similar to Tag-Store
//)

struct bucket_tuple {
  uns count; //amount of balls in bucket
  vector<uns64> ball_list;
  uns64 bucket; //bucket id
  uns64 access_count; //number of times bucket has been accessed, used for LRU
  uns64 frequency; //number of times bucket has been accessed, used for LFU
  uns64 index_min; //current location in the min heap 
  uns64 index_lfu; //current location in the lfu heap
  uns64 index_lru; //current location in the lru heap
  uns64 skew_index; //skew index
  uns64 index_max; //max heap index
};

union bucket_value {
  uns count;
  bucket_tuple* tuple_ptr; //index, cnt not sure about this?
};

//having count twice is not needed so use tuple pointer for count 
vector<bucket_value> bucket[NUM_BUCKETS];

//function declarations
void relocate_LRU(bucket_tuple* tuple_ptr);

void relocate_LFU(bucket_tuple* tuple_ptr);

void relocate_smart(bucket_tuple* tuple_ptr);

void relocate_max_heap(void);

void relocate_mfu(void); 

void relocate_mru(void);


//For each Ball (Cache-Line), which Bucket (Set) it is in
//(Data-Structure Similar to Data-Store RPTR)
uns64 balls[NUM_BUCKETS*BALLS_PER_BUCKET];

//Number of Times Each Bucket Indexed 
uns64 bucket_fill_observed[MAX_FILL+1];
//Number of Times Bucket Containing N Balls has a Ball-Insertion
uns64 stat_counts[MAX_FILL+1];

//Number of Spills from Buckets
uns64 spill_count = 0;
//Number of Spills despite relocation attempts.
uns64 cuckoo_spill_count = 0;

//Tracks if Initialization of Buckets Done
bool init_buckets_done = false;

//track if heap is created
bool init_heap_done = false;

//Mersenne Twister Rand Generator
MTRand *mtrand=new MTRand();

//count of balls in each bucket used to determine orderingx
uns64 number_relocations = 0; 

uns64 number_empty_buckets = 0;

//this is used for LRU heuristic
uns64 current_timestamp = 0;


//this is used to determine how many balls to relocate
uns64 CURR_NUM_WAYS = 0;

uns64 NUM_TO_RELOC = 0;


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
//priority queue that is used to determine which 
//bucket to insert into based on LFU heuristic
/////////////////////////////////////////////////////
/////////////////////////////////////////////////////


class GriffinsAwesomeLFUQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_lfu_[index]->frequency < storage_lfu_[parent_index]->frequency) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_lfu_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_lfu_[left_index]->frequency < storage_lfu_[max]->frequency) {
      max = left_index;
    }

    if (right_index < size && storage_lfu_[right_index]->frequency < storage_lfu_[max]->frequency) {
      max = right_index;
    }
    
    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_lfu_.size() == 0){
      return nullptr;
    }
    return storage_lfu_[0];
  }

  void pop() {
    uns64 size = storage_lfu_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_lfu_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_lfu_.push_back(element);
    element->index_lfu = storage_lfu_.size() - 1;
    heapify_upwards(element->index_lfu);
  }

  uns64 size(void) {
    uns64 size = storage_lfu_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_lfu_[index];
    return val;
  }


private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_lfu_.size() && b < storage_lfu_.size()) {
    std::swap(storage_lfu_[a], storage_lfu_[b]);
    std::swap(storage_lfu_[a]->index_lfu, storage_lfu_[b]->index_lfu);
    }
  }

private:
  vector<bucket_tuple*> storage_lfu_;
};

GriffinsAwesomeLFUQueue pq_lfu;
GriffinsAwesomeLFUQueue pq_lfu_skew1;
GriffinsAwesomeLFUQueue pq_lfu_skew2;



/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////


class GriffinsAwesomeMFUQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_mfu_[index]->frequency > storage_mfu_[parent_index]->frequency) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_mfu_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_mfu_[left_index]->frequency > storage_mfu_[max]->frequency) {
      max = left_index;
    }

    if (right_index < size && storage_mfu_[right_index]->frequency > storage_mfu_[max]->frequency) {
      max = right_index;
    }
    
    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_mfu_.size() == 0){
      return nullptr;
    }
    return storage_mfu_[0];
  }

  void pop() {
    uns64 size = storage_mfu_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_mfu_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_mfu_.push_back(element);
    //just use the lfu index for now
    element->index_lfu = storage_mfu_.size() - 1;
    heapify_upwards(element->index_lfu);
  }

  uns64 size(void) {
    uns64 size = storage_mfu_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_mfu_[index];
    return val;
  }


private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_mfu_.size() && b < storage_mfu_.size()) {
    std::swap(storage_mfu_[a], storage_mfu_[b]);
    std::swap(storage_mfu_[a]->index_lfu, storage_mfu_[b]->index_lfu);
    }
  }

private:
  vector<bucket_tuple*> storage_mfu_;
};

GriffinsAwesomeMFUQueue pq_mfu;

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
//priority queue that is used to determine which 
//bucket to insert into based on LRU heuristic
/////////////////////////////////////////////////////
/////////////////////////////////////////////////////


class GriffinsAwesomeLRUQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_lru_[index]->access_count < storage_lru_[parent_index]->access_count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_lru_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_lru_[left_index]->access_count< storage_lru_[max]->access_count) {
      max = left_index;
    }

    if (right_index < size && storage_lru_[right_index]->access_count < storage_lru_[max]->access_count) {
      max = right_index;
    }
    
    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_lru_.size() == 0){
      return nullptr;
    }
    return storage_lru_[0];
  }

  void pop() {
    uns64 size = storage_lru_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_lru_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_lru_.push_back(element);
    element->index_lru = storage_lru_.size() - 1;
    heapify_upwards(element->index_lru);
  }

  uns64 size(void) {
    uns64 size = storage_lru_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_lru_[index];
    return val;
  }


private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_lru_.size() && b < storage_lru_.size()) {
    std::swap(storage_lru_[a], storage_lru_[b]);
    std::swap(storage_lru_[a]->index_lru, storage_lru_[b]->index_lru);
    }
  }

private:
  vector<bucket_tuple*> storage_lru_;
};

GriffinsAwesomeLRUQueue pq_lru;
GriffinsAwesomeLRUQueue pq_lru_skew1;
GriffinsAwesomeLRUQueue pq_lru_skew2;

///////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////


class GriffinsAwesomeMRUQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_mru_[index]->access_count > storage_mru_[parent_index]->access_count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_mru_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_mru_[left_index]->access_count > storage_mru_[max]->access_count) {
      max = left_index;
    }

    if (right_index < size && storage_mru_[right_index]->access_count > storage_mru_[max]->access_count) {
      max = right_index;
    }
    
    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_mru_.size() == 0){
      return nullptr;
    }
    return storage_mru_[0];
  }

  void pop() {
    uns64 size = storage_mru_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_mru_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_mru_.push_back(element);
    element->index_lru = storage_mru_.size() - 1;
    heapify_upwards(element->index_lru);
  }

  uns64 size(void) {
    uns64 size = storage_mru_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_mru_[index];
    return val;
  }


private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_mru_.size() && b < storage_mru_.size()) {
    std::swap(storage_mru_[a], storage_mru_[b]);
    std::swap(storage_mru_[a]->index_lru, storage_mru_[b]->index_lru);
    }
  }

private:
  vector<bucket_tuple*> storage_mru_;
};

GriffinsAwesomeMRUQueue pq_mru;

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
//priority queue that is used to determine which 
//bucket to insert into for min element bases relocation
/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

class GriffinsAwesomeMinQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_min_[index]->count < storage_min_[parent_index]->count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_min_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_min_[left_index]->count < storage_min_[max]->count) {
      max = left_index;
    }

    if (right_index < size && storage_min_[right_index]->count < storage_min_[max]->count) {
      max = right_index;
    }
    

    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_min_.size() == 0){
      return nullptr;
    }
    return storage_min_[0];
  }

  void pop() {
    uns64 size = storage_min_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_min_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_min_.push_back(element);
    element->index_min = storage_min_.size() - 1;
    heapify_upwards(element->index_min);
  }

  uns64 size(void) {
    uns64 size = storage_min_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_min_[index];
    return val;
  }

private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_min_.size() && b < storage_min_.size()) {
    std::swap(storage_min_[a], storage_min_[b]); 
    std::swap(storage_min_[a]->index_min, storage_min_[b]->index_min); 
    }
  }

private:
  vector<bucket_tuple*> storage_min_;
};

GriffinsAwesomeMinQueue pq_min;
GriffinsAwesomeMinQueue pq_min_skew1;
GriffinsAwesomeMinQueue pq_min_skew2;


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

class GriffinsAwesomeMaxQueue {
public:
  // Called when count is decremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_max_[index]->count > storage_max_[parent_index]->count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is incremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_max_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_max_[left_index]->count > storage_max_[max]->count) {
      max = left_index;
    }

    if (right_index < size && storage_max_[right_index]->count > storage_max_[max]->count) {
      max = right_index;
    }
    
    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    if(storage_max_.size() == 0){
      return nullptr;
    }
    return storage_max_[0];
  }

  void pop() {
    uns64 size = storage_max_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_max_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_max_.push_back(element);
    element->index_max = storage_max_.size() - 1;
    heapify_upwards(element->index_max);
  }

  uns64 size(void) {
    uns64 size = storage_max_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_max_[index];
    return val;
  }


private:
  void swap_elements(uns64 a, uns64 b) {
    if (a < storage_max_.size() && b < storage_max_.size()) {
    std::swap(storage_max_[a], storage_max_[b]);
    std::swap(storage_max_[a]->index_max, storage_max_[b]->index_max);
    }
  }

private:
  vector<bucket_tuple*> storage_max_;
};

GriffinsAwesomeMaxQueue pq_max;

GriffinsAwesomeMaxQueue pq_max_skew1;
GriffinsAwesomeMaxQueue pq_max_skew2;


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////


/////////////////////////////////////////////////////
// FUNCTIONS - Ball Insertion, Removal, Spill, etc.
/////////////////////////////////////////////////////


/////////////////////////////////////////////////////
// Spill Ball: relocating filled bucket
// -- Based on which skew spill happened;
// -- cuckoo into other recursively.
/////////////////////////////////////////////////////


void spill_ball(uns64 index, uns64 ballID){
  uns done=0;

  ////////////////////////////////////////////////////////
  //below are changes

  bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
  //cout << "tuple got" << endl;
  //decrement count of bucket that is full
  bucket[index].at(0).count--;
  //reflect the pointer count to match the new count, this can just be a decremet, would probs be faster
  tuple_ptr->count--;
  //heapify up to correct ordering as count is decreased
  
  //cout << "here" << endl;

  /*

  if (tuple_ptr->skew_index == 0) {
    pq_min_skew1.heapify_upwards(tuple_ptr->index_min);
    pq_lfu_skew1.heapify_upwards(tuple_ptr->index_lfu);
    pq_lru_skew1.heapify_upwards(tuple_ptr->index_lru);
  }
  else {
    pq_min_skew2.heapify_upwards(tuple_ptr->index_min);
    pq_lfu_skew2.heapify_upwards(tuple_ptr->index_lfu);
    pq_lru_skew2.heapify_upwards(tuple_ptr->index_lru);
  }
  */

  //cout << "here 1" << endl;

  pq_max.heapify_downwards(tuple_ptr->index_max);
  //pq_mfu.heapify_downwards(tuple_ptr->index_lfu);
  //pq_mru.heapify_downwards(tuple_ptr->index_lru);
  //pq_min.heapify_upwards(tuple_ptr->index_min);
  //pq_lfu.heapify_upwards(tuple_ptr->index_lfu);
  //pq_lru.heapify_upwards(tuple_ptr->index_lru);

  
  //remove inserted ball from bucket balls vector
  for (uns64 k =0; k < tuple_ptr->ball_list.size(); ++k){
    if (tuple_ptr->ball_list[k] == ballID) //search thru vector to erase ballid from ball list so wont be relocated by accidnet
    {
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin() + k);
      break;
    }
  }

  //above are changes
  //////////////////////////////////////////////////////


  while(done!=1){
    //Pick skew & bucket-index where spilled ball should be placed.
    uns64 spill_index ;
    //If current index is in Skew0, then pick Skew1. Else vice-versa.
    if(index < NUM_BUCKETS_PER_SKEW)
      spill_index = NUM_BUCKETS_PER_SKEW + mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);
    else
      spill_index = mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);

    //If new spill_index bucket where spilled-ball is to be installed has space, then done.
    if(bucket[spill_index].at(0).count < SPILL_THRESHOLD){
      done=1;

      ////////////////////////////////////////////////////////////////
      //below are changes
     
      //set the ball to the new bucket
      balls[ballID] = spill_index;
      //get pointer to update needed values 
      bucket_tuple* tuple_spill = bucket[spill_index].at(1).tuple_ptr;
      //increment count of bucket that ball is inserted into
      bucket[spill_index].at(0).count++;
      //set the count of the tuple to the new count
      tuple_spill->count++;
      //update access count of bucket
      tuple_spill->access_count = current_timestamp++;
      //uodate frequency count of bucket
      tuple_spill->frequency++;
      //add ball to bucket balls vector
      tuple_spill->ball_list.push_back(ballID);
      //heapify down to correct ordering as count is increased


      /*
      if (tuple_spill->skew_index == 0) {
        pq_min_skew1.heapify_downwards(tuple_spill->index_min);
        pq_lfu_skew1.heapify_downwards(tuple_spill->index_lfu);
        pq_lru_skew1.heapify_downwards(tuple_spill->index_lru);
      }
      else {
        pq_min_skew2.heapify_downwards(tuple_spill->index_min);
        pq_lfu_skew2.heapify_downwards(tuple_spill->index_lfu);
        pq_lru_skew2.heapify_downwards(tuple_spill->index_lru);
      }
      */


      pq_max.heapify_upwards(tuple_spill->index_max);
      //pq_mfu.heapify_upwards(tuple_spill->index_lfu);
      //pq_mru.heapify_upwards(tuple_spill->index_lru);
     //pq_min.heapify_downwards(tuple_spill->index_min);
      //pq_lfu.heapify_downwards(tuple_spill->index_lfu);
      //pq_lru.heapify_downwards(tuple_spill->index_lru);
      
      //above are changes
      ////////////////////////////////////////////////////////////////
     
    } else {
      bucket_tuple* spill = bucket[spill_index].at(1).tuple_ptr;
      assert(bucket[spill_index].at(0).count == SPILL_THRESHOLD);
      //if bucket of spill_index is also full, then recursive-spill, we call this a cuckoo-spill
      index = spill_index;
      cuckoo_spill_count++;
    }
  }

  spill_count++;
}

/////////////////////////////////////////////////////
// Insert Ball in Bucket
// -- ballID => ID of Data-Store Entry (ball) which got evicted via global eviction
/////////////////////////////////////////////////////

uns insert_ball(uns64 ballID){

  //Index for Rand Bucket in Skew-0
  uns64 index1 = mtrand->randInt(NUM_BUCKETS_PER_SKEW - 1);
  //Index for Rand Bucket in Skew-1
  uns64 index2 = NUM_BUCKETS_PER_SKEW + mtrand->randInt(NUM_BUCKETS_PER_SKEW - 1);

  bucket_tuple* tuple_idx1 = bucket[index1].at(1).tuple_ptr;  
  bucket_tuple* tuple_idx2 = bucket[index2].at(1).tuple_ptr;

  //Increments Tracking of Indexed Buckets
  if(init_buckets_done){
    bucket_fill_observed[bucket[index1].at(0).count]++;
    bucket_fill_observed[bucket[index2].at(0).count]++;
  }

  relocate_max_heap();
  //relocate_mfu();
  //relocate_mru();

  uns64 index;
  uns retval;

  //------ LOAD AWARE SKEW SELECTION -----
  //Identify which Bucket (index) has Less Load
  if(bucket[index2].at(0).count < bucket[index1].at(0).count){
    index = index2;
  } else if (bucket[index1].at(0).count < bucket[index2].at(0).count){
    index = index1;    
  } else if (bucket[index2].at(0).count == bucket[index1].at(0).count) {

#if BREAK_TIES_PREFERENTIALLY == 0
    //Break ties randomly
    if(mtrand->randInt(1) == 0)
      index = index1;
    else
      index = index2;

#elif BREAK_TIES_PREFERENTIALLY == 1
    //Break ties favoring Skew-0.
    index = index1;
#endif
     
  } else {
    assert(0);
  }

  retval = bucket[index].at(0).count;

  ////////////////////////////////////////////////////////////////
  //below are changes 


  //cout << "index " <<index << endl;
  //get pointer to update needed values
  bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
  assert(tuple_ptr != nullptr);

  //update count of bucket that ball is inserted into 
  bucket[index].at(0).count++;
  //set the count of the tuple to the new count
  tuple_ptr->count++;
  //update access count of bucket
  tuple_ptr->access_count = current_timestamp++;
  //uodate frequency count of bucket
  tuple_ptr->frequency++;
  //add ball id to current bucket
  tuple_ptr->ball_list.push_back(ballID); //ball should be added to the bucket balls vector 
  //heapify down to correct ordering as count is increased 


  /*
  if (tuple_ptr->skew_index == 0) {
    pq_min_skew1.heapify_downwards(tuple_ptr->index_min);
    pq_lfu_skew1.heapify_downwards(tuple_ptr->index_lfu);
    pq_lru_skew1.heapify_downwards(tuple_ptr->index_lru);
  }
  else {
    pq_min_skew2.heapify_downwards(tuple_ptr->index_min);
    pq_lfu_skew2.heapify_downwards(tuple_ptr->index_lfu);
    pq_lru_skew2.heapify_downwards(tuple_ptr->index_lru);
  }
  */

  pq_max.heapify_upwards(tuple_ptr->index_max);
  //pq_mfu.heapify_upwards(tuple_ptr->index_lfu);
  //pq_mru.heapify_upwards(tuple_ptr->index_lru);
  //pq_min.heapify_downwards(tuple_ptr->index_min);
  //pq_lfu.heapify_downwards(tuple_ptr->index_lfu);
  //pq_lru.heapify_downwards(tuple_ptr->index_lru);

  uns64 bucket_id = tuple_ptr->bucket;

  //above are changes
  ////////////////////////////////////////////////////////////////

  //Track which bucket the new Ball was inserted in
  assert(balls[ballID] == (uns64)-1);
  balls[ballID] = index;

  ////////////////////////////////////////////////////////////////
  //below are changes

  assert(index == bucket_id);

  assert(bucket[index].at(0).count == tuple_ptr->count);

  //if(bucket[index].at(0).count > BALLS_PER_BUCKET){
    //relocate_LRU(tuple_ptr);
    //relocate_LFU(tuple_ptr);
    //relocate_smart(tuple_ptr);
  //}

  //above are changes
  ////////////////////////////////////////////////////////////////

  //----------- SPILL --------
  if(SPILL_THRESHOLD && (retval >= SPILL_THRESHOLD)){
    //Overwrite balls[ballID] with spill_index.
    spill_ball(index,ballID); 
  }

  return retval; 
}

/////////////////////////////////////////////////////
// Remove Random Ball (Global Eviction)
/////////////////////////////////////////////////////

uns64 remove_ball(void){
  // Select Random BallID from all Balls
  uns64 ballID = mtrand->randInt(NUM_BUCKETS*BALLS_PER_BUCKET -1);

  // Identify which bucket this ball is in 
  assert(balls[ballID] != (uns64)-1);
  uns64 bucket_index = balls[ballID]; //bucket index is just the bucket id

  assert(bucket[bucket_index].at(0).count != 0);

  ////////////////////////////////////////////////////////////////
  //below are changes

  // modify count of bucket
  bucket[bucket_index].at(0).count--;
 
  // get bucket tuple
  bucket_tuple* tuple_ptr = bucket[bucket_index].at(1).tuple_ptr;

  //set the count of the tuple to the new count
  tuple_ptr->count--;

  //search thru vector to erase ballid from ball list so wont be relocated by accidnet
  tuple_ptr->ball_list.erase(
  std::remove(tuple_ptr->ball_list.begin(), tuple_ptr->ball_list.end(), ballID),
  tuple_ptr->ball_list.end());

  /*
  if (tuple_ptr->skew_index == 0) {
    pq_min_skew1.heapify_upwards(tuple_ptr->index_min);
    pq_lfu_skew1.heapify_upwards(tuple_ptr->index_lfu);
    pq_lru_skew1.heapify_upwards(tuple_ptr->index_lru);

  }
  else {
    pq_min_skew2.heapify_upwards(tuple_ptr->index_min);
    pq_lfu_skew2.heapify_upwards(tuple_ptr->index_lfu);
    pq_lru_skew2.heapify_upwards(tuple_ptr->index_lru);
  }
  */

  pq_max.heapify_downwards(tuple_ptr->index_max);
  //pq_mfu.heapify_downwards(tuple_ptr->index_lfu);
  //pq_mru.heapify_downwards(tuple_ptr->index_lru);
  //pq_min.heapify_upwards(tuple_ptr->index_min);
  //pq_lfu.heapify_upwards(tuple_ptr->index_lfu);
  //pq_lru.heapify_upwards(tuple_ptr->index_lru);
  
  //above are changes
  ////////////////////////////////////////////////////////////////

  // -1 signals that ball is not assigned
  balls[ballID] = -1;

  // Return BallID removed (ID will be reused for new ball to be inserted)  
  return ballID;
}

////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////

void display_histogram(void){
  uns ii;
  uns s_count[MAX_FILL+1];

  for(ii=0; ii<= MAX_FILL; ii++){
    s_count[ii]=0;
  }

  for(ii=0; ii< NUM_BUCKETS; ii++){
    s_count[bucket[ii].at(0).count]++;
  }

  printf("\nOccupancy: \t\t Count");
  for(ii=0; ii<= MAX_FILL; ii++){
    double perc = 100.0 * (double)s_count[ii]/(double)(NUM_BUCKETS);
    printf("\nBucket[%2u Fill]: \t %u \t (%4.2f)", ii, s_count[ii], perc);
  }

  printf("\n");
}

////////////////////////////////////////////////////////////////
//sanity check to insure no corruption
////////////////////////////////////////////////////////////////

void sanity_check(void){
  uns ii, count=0;
  uns s_count[MAX_FILL+1];

  for(ii=0; ii<= MAX_FILL; ii++){
    s_count[ii]=0;
  }
  
  for(ii=0; ii< NUM_BUCKETS; ii++){
    count += bucket[ii].at(0).count;
    s_count[bucket[ii].at(0).count]++;
  }

  if(count != (NUM_BUCKETS*BALLS_PER_BUCKET)){
    printf("\n*** Sanity Check Failed, TotalCount: %u*****\n", count);
  }
}


/////////////////////////////////////////////////////
// Randomly Initialize all the Buckets with Balls (NumBuckets * BallsPerBucket) 
/////////////////////////////////////////////////////

void init_buckets(void){
  uns64 ii;
  assert(NUM_SKEWS * NUM_BUCKETS_PER_SKEW == NUM_BUCKETS);
  
  //Initialize Buckets with correct data structures


  for(ii=0; ii<NUM_BUCKETS; ii++){
    bucket_value count_value = {0};
    bucket[ii].push_back(count_value);
    bucket_value null_value = {0};
    bucket[ii].push_back(null_value);

    //now assign tuple
    bucket_tuple* mytuple = new bucket_tuple();
    mytuple->count = 0;
    //bucket is unqiue id for each bucket
    mytuple->bucket = ii;
    //add access counters
    mytuple->access_count = 0;
    //add frequency counters
    mytuple->frequency = 0;
    //add index for min
    mytuple->index_min = 0;
    //add index for lfu
    mytuple->index_lfu = 0;
    //add index for lru
    mytuple->index_lru = 0;
    //add index for max
    mytuple->index_max = 0;
    //add skew index
    //mytuple->skew_index = 0;
    //add to max heap
    pq_max.push(mytuple);
    //pq_mfu.push(mytuple);
    //pq_mru.push(mytuple);
    //assign pointer 
    bucket[ii].at(1).tuple_ptr = mytuple;
  }
  
  cout << "init " << endl;
  
  
  /*
  //skew 1
  uns64 last = 0;
  for(ii=0; ii<NUM_BUCKETS_PER_SKEW; ii++){

    /////////////////////////////////////////////////
    //below are changes

    //add 0 to first entry in all vectors as place holder for count
    bucket_value count_value = {0};
    bucket[ii].push_back(count_value);
    //add empty entry in all buckets to place pointer to heap tuple
    bucket_value null_value = {0};
    bucket[ii].push_back(null_value);
    //now assign tuple
    bucket_tuple* mytuple = new bucket_tuple();
    mytuple->count = 0;
    //bucket is unqiue id for each bucket
    mytuple->bucket = ii; 
    //add access counters
    mytuple->access_count = 0;
    //add frequency counters
    mytuple->frequency = 0;
    //add index for min
    mytuple->index_min = 0;
    //add index for lfu  
    mytuple->index_lfu = 0;
    //add index for lru
    mytuple->index_lru = 0;
    mytuple->skew_index = 0;
    //add to min heap
    pq_min_skew1.push(mytuple);

    pq_lfu_skew1.push(mytuple);
    pq_lru_skew1.push(mytuple);
    //pq_min.push(mytuple);
    //add to lfu heap
    //pq_lfu.push(mytuple);
    //add to lru heap
    //pq_lru.push(mytuple);
    //set the pointer to the tuple in the bucket
    bucket[ii].at(1).tuple_ptr = mytuple;
    last= ii;

    //above are changes
    /////////////////////////////////////////////////
  }
  //cout << "skew 1 done" << endl;
  //cout << last << endl;

  //skew 2 
  uns64 last_2 =0;
  for(ii=0; ii<NUM_BUCKETS_PER_SKEW; ii++){

    /////////////////////////////////////////////////
    //below are changes

    //add 0 to first entry in all vectors as place holder for count
    bucket_value count_value = {0};
    bucket[ii+NUM_BUCKETS_PER_SKEW].push_back(count_value);
    //add empty entry in all buckets to place pointer to heap tuple
    bucket_value null_value = {0};
    bucket[ii+NUM_BUCKETS_PER_SKEW].push_back(null_value);
    //now assign tuple
    bucket_tuple* mytuple = new bucket_tuple();
    mytuple->count = 0;
    //bucket is unqiue id for each bucket
    mytuple->bucket = ii + NUM_BUCKETS_PER_SKEW; 
    //add access counters
    mytuple->access_count = 0;
    //add frequency counters
    mytuple->frequency = 0;
    //add index for min
    mytuple->index_min = 0;
    //add index for lfu  
    mytuple->index_lfu = 0;
    //add index for lru
    mytuple->index_lru = 0;
    //add to min heap
    mytuple->skew_index = 1;
    pq_min_skew2.push(mytuple);
    pq_lfu_skew2.push(mytuple);
    pq_lru_skew2.push(mytuple);
    //pq_min.push(mytuple);
    //add to lfu heap
    //pq_lfu.push(mytuple);
    //add to lru heap
    //pq_lru.push(mytuple);
    //set the pointer to the tuple in the bucket
    bucket[ii+NUM_BUCKETS_PER_SKEW].at(1).tuple_ptr = mytuple;
    last_2 = ii+NUM_BUCKETS_PER_SKEW;

    //above are changes
    /////////////////////////////////////////////////
  }

  */

  //assert(last_2 == NUM_BUCKETS);

  //cout << "skew 2 done" << endl;
  //cout << last_2 << endl;
  //cout << NUM_BUCKETS_PER_SKEW << endl;
  //cout << NUM_BUCKETS << endl;
   
  for(ii=0; ii<(NUM_BUCKETS*BALLS_PER_BUCKET); ii++){
    balls[ii] = -1;
    insert_ball(ii);
  }
  cout << "insert balls done" << endl;

  for(ii=0; ii<=MAX_FILL; ii++){
    stat_counts[ii]=0;
  }

  sanity_check();
  cout << "sanity check done" << endl;
  init_buckets_done = true;
}



/////////////////////////////////////////////////////
// Randomly remove a ball and
// then insert a new ball with Power-of-Choices Install
/////////////////////////////////////////////////////

uns  remove_and_insert(void){
  
  uns res = 0;

  uns64 ballID = remove_ball();
  res = insert_ball(ballID);

  if(res <= MAX_FILL){
    stat_counts[res]++;
  }else{
    printf("Overflow\n");
    exit(-1);
  }
  return res;
}

////////////////////////////////////////////////////////////
//ideal relocate function, that creates 
//even distribution with min heap
////////////////////////////////////////////////////////////

void relocate_smart(bucket_tuple* tuple_ptr) {
    uns64 buck_to_move = tuple_ptr->bucket;
    bucket_tuple* tuple_last = nullptr;


    //var to keep track of how many balls to relocate
    uns64 amount_to_relcoate = 1; 

    if (tuple_ptr->count == BALLS_PER_BUCKET || tuple_ptr->count == SPILL_THRESHOLD) {
      return;
    }

    if (tuple_ptr->skew_index == 0) {
      tuple_last = pq_min_skew1.top();
    }
    else {
      tuple_last = pq_min_skew2.top();
    }

    //tuple_last = pq_min.top();
        
    if(tuple_last == nullptr) {
      return;
    }

    if(tuple_last->count >= SPILL_THRESHOLD-1) {

      return;
    }

    assert(tuple_last->count != SPILL_THRESHOLD);
    //cout << "tuple last count " << tuple_last->count << endl;

    
    //get the first ball in the bucket to remove
    uns64 firstBall = tuple_ptr->ball_list.front();
    //erase bucket at the front of the list 
    tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

    //decrement the count of the bucket that is being relocated from
    tuple_ptr->count--;
    bucket[tuple_ptr->bucket].at(0).count--;


    if (tuple_ptr->skew_index == 0) {
      pq_min_skew1.heapify_upwards(tuple_ptr->index_min);
    }
    else {
      pq_min_skew2.heapify_upwards(tuple_ptr->index_min);
    }

    //heapify up to correct ordering as count is decreased
    //pq_min.heapify_upwards(tuple_ptr->index_min);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;
    assert(tuple_last->count != SPILL_THRESHOLD);


   ///////////////////////////////////////
    //check this could be source of error? it was needed to be inverted
    if(tuple_last->skew_index == 0) {
      pq_min_skew1.heapify_downwards(tuple_last->index_min);
    }
    else {
      pq_min_skew2.heapify_downwards(tuple_last->index_min);
    }


    //pq_min.heapify_downwards(tuple_last->index_min);

    number_relocations++;
  
}

/////////////////////////////////////////////////////
//relocate function, that mimics LFU
/////////////////////////////////////////////////////


void relocate_LFU(bucket_tuple* tuple_ptr) {
    uns64 buck_to_move = tuple_ptr->bucket;

    bucket_tuple* tuple_last = nullptr;
    //= pq_lfu.top();
    if(tuple_ptr->skew_index == 0) {
      tuple_last = pq_lfu_skew1.top();
    }
    else {
      tuple_last = pq_lfu_skew2.top();
    }

    
    if (tuple_last == nullptr) {
      return;
    }

    if (tuple_last->count >= BALLS_PER_BUCKET || tuple_last->count == SPILL_THRESHOLD) {
      return;
    }

    //get the first ball in the bucket to remove
    uns64 firstBall = tuple_ptr->ball_list.front();
    //erase bucket at the front of the list 
    tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

    //decrement the count of the bucket that is being relocated from
    tuple_ptr->count--;
    bucket[buck_to_move].at(0).count--;

    if(tuple_ptr->skew_index == 0) {
      pq_lfu_skew1.heapify_upwards(tuple_ptr->index_lfu);
    }
    else {
      pq_lfu_skew2.heapify_upwards(tuple_ptr->index_lfu);
    }
    //pq_lfu.heapify_upwards(tuple_ptr->index_lfu);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    tuple_last->frequency++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;

    // Fix the heap ordering
    if (tuple_last->skew_index == 0) {
      pq_lfu_skew1.heapify_upwards(tuple_last->index_lfu);
    }
    else {
      pq_lfu_skew2.heapify_downwards(tuple_last->index_lfu);
    }
    //pq_lfu.heapify_downwards(tuple_last->index_lfu);

    number_relocations++;
}



/////////////////////////////////////////////////////
//relocate function, that mimics LRU
/////////////////////////////////////////////////////



void relocate_LRU(bucket_tuple* tuple_ptr) {
    uns64 buck_to_move = tuple_ptr->bucket;

    //bucket_tuple* tuple_last = pq_lru.top();

    bucket_tuple* tuple_last = nullptr;

    if(tuple_ptr->skew_index == 0) {
      tuple_last = pq_lru_skew1.top();
    }
    else {
      tuple_last = pq_lru_skew2.top();
    }
    
    if (tuple_last == nullptr) {
      return;
    }

    if (tuple_last->count == SPILL_THRESHOLD || tuple_last->count >= BALLS_PER_BUCKET) {
      return;
    }

    //get the first ball in the bucket to remove
    uns64 firstBall = tuple_ptr->ball_list.front();
    //erase bucket at the front of the list 
    tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

    //decrement the count of the bucket that is being relocated from
    tuple_ptr->count--;
    bucket[buck_to_move].at(0).count--;
    //heapify up to correct ordering as count is decreased
    if(tuple_ptr->skew_index == 0) {
      pq_lru_skew1.heapify_upwards(tuple_ptr->index_lru);
    }
    else {
      pq_lru_skew2.heapify_upwards(tuple_ptr->index_lru);
    }

    //pq_lru.heapify_upwards(tuple_ptr->index_lru);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    tuple_last->frequency++;
    tuple_last->access_count = current_timestamp++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;

    // Fix the heap ordering
    //pq_lru.heapify_upwards(tuple_last->index_lru);
    if(tuple_last->skew_index == 0) {
      pq_lru_skew1.heapify_upwards(tuple_last->index_lru);
    }
    else {
      pq_lru_skew2.heapify_upwards(tuple_last->index_lru);
    }

    number_relocations++;
  
}

/////////////////////////////////////////////////////
uns64 get_number_to_relocate_8(bucket_tuple* tuple_ptr) 
{
  uns64 amount_to_relcoate; 
  switch(tuple_ptr->count) {
    case 0:
    case 1:
    case 2:
      amount_to_relcoate = 0;
      break;
    case 3:
    case 4:
    case 5:
    case 6:
    case 7:
    case 8:
      amount_to_relcoate = 2;
      break;
    case 9:
      amount_to_relcoate = 3;
      break;
    default:
      amount_to_relcoate = 0;
      break;
  }
  return amount_to_relcoate;
}



/////////////////////////////////////////////////////

void relocate_max_heap (void) {
  
  for (uns ii=0; ii<NUM_TO_RELOC; ii++) {
    
    bucket_tuple* tuple_top = pq_max.top();

    if (tuple_top == nullptr || tuple_top->count == 0 || tuple_top->count ==1) {
      return;
    }

    uns64 index = tuple_top->bucket;
    uns64 spill_index; 
    
    uns done = 0;

    while(done != 1) {

      if(index < NUM_BUCKETS_PER_SKEW)
        spill_index = NUM_BUCKETS_PER_SKEW + mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);
      else
        spill_index = mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);

      if(bucket[spill_index].at(0).count < SPILL_THRESHOLD){
        done = 1; 
        //remove ball and to spill index

        uns64 ballID = tuple_top->ball_list.front();

        tuple_top->ball_list.erase(tuple_top->ball_list.begin());

        tuple_top->count--;
        bucket[index].at(0).count--;
        pq_max.heapify_downwards(tuple_top->index_max); 


        //now mv ball to spill index aka new bucket

        bucket_tuple* insert_buck = bucket[spill_index].at(1).tuple_ptr;
        
        insert_buck->ball_list.push_back(ballID);
        insert_buck->count++;
        bucket[spill_index].at(0).count++;
        insert_buck->access_count = current_timestamp++;
        insert_buck->frequency++;
        balls[ballID] = spill_index;
        pq_max.heapify_upwards(insert_buck->index_max);

      }
    }
    number_relocations++;
  }
}


/////////////////////////////////////////////////////
////////////////////////////////////////////////////

void relocate_mfu (void) {
  
  bucket_tuple* tuple_top = pq_mfu.top();

  //cout << "top got" << endl;
  //cout << tuple_top->count << endl;

  //if (tuple_top->count <= BALLS_PER_BUCKET) {
  //  return;
  //}//

  /*
  if (pq_max.size() <= 2){
    return;
  }
  */

  /*
  bucket_tuple* tuple_last = pq_mfu.top();
  
  for(uns ii=0; ii<NUM_BUCKETS; ii++) {
    if (tuple_last->frequency < bucket[ii].at(1).tuple_ptr->frequency) {
      tuple_last = bucket[ii].at(1).tuple_ptr;
    }
  }
  assert(tuple_last->frequency == pq_mfu.top()->frequency);
  */


  if (tuple_top == nullptr || tuple_top->count == 0 || tuple_top->count ==1) {
    return;
  }

  //uns amount_to_relocate = get_number_to_relocate_8(tuple_top);
  //uns amount_to_relocate = 1;
  //cout << "amount to relocate " << amount_to_relocate << endl;
  //cout << "tuple top count " << tuple_top->count << endl;
  //cout << "tuple top bucket " << tuple_top->bucket << endl;
  //cout << "frequency " << tuple_top->frequency << endl;
  //cout << "access count " << tuple_top->access_count << endl;
  //if(amount_to_relocate == 0) {
  //  return;
  //}
  

  uns64 index = tuple_top->bucket;
  uns64 spill_index; 
  
  //for(int ii=0; ii<amount_to_relocate; ii++) {
    uns done = 0;

    while(done != 1) {

      if(index < NUM_BUCKETS_PER_SKEW)
        spill_index = NUM_BUCKETS_PER_SKEW + mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);
      else
        spill_index = mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);

      if(bucket[spill_index].at(0).count < SPILL_THRESHOLD){
        done = 1; 
        //remove ball and to spill index

        uns64 ballID = tuple_top->ball_list.front();

        tuple_top->ball_list.erase(tuple_top->ball_list.begin());

        tuple_top->count--;
        bucket[index].at(0).count--;
        pq_mfu.heapify_downwards(tuple_top->index_max); 

        //now mv ball to spill index aka new bucket

        bucket_tuple* insert_buck = bucket[spill_index].at(1).tuple_ptr;
        
        insert_buck->ball_list.push_back(ballID);
        insert_buck->count++;
        bucket[spill_index].at(0).count++;
        insert_buck->access_count = current_timestamp++;
        insert_buck->frequency++;
        balls[ballID] = spill_index;
        pq_mfu.heapify_upwards(insert_buck->index_max);

      }
    }
    number_relocations++;
  //}
}



/////////////////////////////////////////////////////
////////////////////////////////////////////////////


void relocate_mru(void) {
  
  bucket_tuple* tuple_top = pq_mru.top();

  //cout << "top got" << endl;
  //cout << tuple_top->count << endl;

  //if (tuple_top->count <= BALLS_PER_BUCKET) {
  //  return;
  //}//

  /*
  if (pq_max.size() <= 2){
    return;
  }
  */

  /*
  bucket_tuple* tuple_last = pq_mfu.top();
  
  for(uns ii=0; ii<NUM_BUCKETS; ii++) {
    if (tuple_last->frequency < bucket[ii].at(1).tuple_ptr->frequency) {
      tuple_last = bucket[ii].at(1).tuple_ptr;
    }
  }
  assert(tuple_last->frequency == pq_mfu.top()->frequency);
  */


  if (tuple_top == nullptr || tuple_top->count == 0 || tuple_top->count ==1) {
    return;
  }

  uns amount_to_relocate = get_number_to_relocate_8(tuple_top);
  //cout << "amount to relocate " << amount_to_relocate << endl;
  //cout << "tuple top count " << tuple_top->count << endl;
  //cout << "tuple top bucket " << tuple_top->bucket << endl;
  //cout << "frequency " << tuple_top->frequency << endl;
  //cout << "access count " << tuple_top->access_count << endl;
  if(amount_to_relocate == 0) {
    return;
  }
  

  uns64 index = tuple_top->bucket;
  uns64 spill_index; 
  
  for(int ii=0; ii<amount_to_relocate; ii++) {
    uns done = 0;

    while(done != 1) {

      if(index < NUM_BUCKETS_PER_SKEW)
        spill_index = NUM_BUCKETS_PER_SKEW + mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);
      else
        spill_index = mtrand->randInt(NUM_BUCKETS_PER_SKEW-1);

      if(bucket[spill_index].at(0).count < SPILL_THRESHOLD){
        done = 1; 
        //remove ball and to spill index

        uns64 ballID = tuple_top->ball_list.front();

        tuple_top->ball_list.erase(tuple_top->ball_list.begin());

        tuple_top->count--;
        bucket[index].at(0).count--;
        pq_mru.heapify_downwards(tuple_top->index_max); 

        //now mv ball to spill index aka new bucket

        bucket_tuple* insert_buck = bucket[spill_index].at(1).tuple_ptr;
        
        insert_buck->ball_list.push_back(ballID);
        insert_buck->count++;
        bucket[spill_index].at(0).count++;
        insert_buck->access_count = current_timestamp++;
        insert_buck->frequency++;
        balls[ballID] = spill_index;
        pq_mru.heapify_upwards(insert_buck->index_max);

      }
    }
    number_relocations++;
  }
}



/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
int main(int argc, char* argv[]){

  //Get arguments:
  assert((argc == 6) && "Need 5 arguments: (EXTRA_BUCKET_CAPACITY:[0-8] BN_BALL_THROWS:[1-10^5] SEED:[1-400] NUM_WAYS:[4,8,16] NUM_TO_RELOC:[1-8])");
  EXTRA_BUCKET_CAPACITY = atoi(argv[1]);
  SPILL_THRESHOLD = BASE_WAYS_PER_SKEW + EXTRA_BUCKET_CAPACITY;
  NUM_BILLION_TRIES  = atoi(argv[2]);
  myseed = atoi(argv[3]);

  CURR_NUM_WAYS = atoi(argv[4]);
  assert((CURR_NUM_WAYS == 4) || (CURR_NUM_WAYS == 8) || (CURR_NUM_WAYS == 16));
  NUM_TO_RELOC = atoi(argv[5]);
  printf("Cache Configuration: %d MB, %d skews, %d ways (%d ways/skew)\n",CACHE_SZ_BYTES/1024/1024,NUM_SKEWS,NUM_SKEWS*BASE_WAYS_PER_SKEW,BASE_WAYS_PER_SKEW);
  printf("AVG-BALLS-PER-BUCKET:%d, BUCKET-SPILL-THRESHOLD:%d \n",BASE_WAYS_PER_SKEW,SPILL_THRESHOLD);
  printf("Simulation Parameters - BALL_THROWS:%llu, SEED:%d\n\n",(unsigned long long)NUM_BILLION_TRIES*(unsigned long long)BILLION_TRIES,myseed);
  uns64 ii;
  mtrand->seed(myseed);

  //Initialize Buckets
  init_buckets();
  sanity_check();

  printf("Starting --  (Dot printed every 100M Ball throws) \n");
  std::cout << "Extra Tags Provisioned: " << EXTRA_BUCKET_CAPACITY << endl;

  //N Billion Ball Throws
  for (uns64 bn_i=0 ; bn_i < NUM_BILLION_TRIES; bn_i++) {    
    //1 Billion Ball Throws
    for(uns64 hundred_mn_count=0; hundred_mn_count<10; hundred_mn_count++){
      //In multiples of 100 Million Ball Throws.
      for(ii=0; ii<HUNDRED_MILLION_TRIES; ii++){
        //Insert and Remove Ball
        remove_and_insert();      
      }
      printf(".");fflush(stdout);
    }    
    //Ensure Total Balls in Buckets is Conserved.
    sanity_check();
    //Print count of Balls Thrown.
    printf(" %llu\n",bn_i+1);fflush(stdout);    
  }
  std::cout << "Number of Relocations: "<< number_relocations << endl;
  

  printf("\n\nBucket-Occupancy Snapshot at End of Experiment\n");
  display_histogram();
  printf("\n\n");

  printf("Distribution of Bucket-Occupancy (Averaged across Ball Throws) => Used for P(Bucket = k balls) calculation \n");
  printf("\nOccupancy: \t\t %16s \t P(Bucket=k balls)","Count");
  for(ii=0; ii<= MAX_FILL; ii++){
    double perc = 100.0 * (double)bucket_fill_observed[ii]/(NUM_SKEWS*(double)NUM_BILLION_TRIES*(double)BILLION_TRIES);
    printf("\nBucket[%llu Fill]: \t %16llu \t (%5.3f)", ii, bucket_fill_observed[ii], perc);
  }

  printf("\n\n\n");

  printf("Distribution of Balls-in-Dest-Bucket on Ball-Insertion (Best-Of-2 Indexed-Buckets) => Spill-Count = Spills from Bucket-With-%d-Balls\n",SPILL_THRESHOLD);
  //  printf("\n");
  printf("\nBalls-in-Dest-Bucket (k) \t\t Spills from Bucket-With-k-Balls)\n");
  for(ii=0; ii<MAX_FILL; ii++){
    double perc = 100.0*(double)(stat_counts[ii])/(double)((double)NUM_BILLION_TRIES*(double)BILLION_TRIES);
    printf("%2llu:\t\t\t\t %16llu\t (%5.3f)\n", ii, stat_counts[ii], perc);
  }

  printf("\nSpill Count: %llu (%5.3f)\n", spill_count,
         100.0* (double)spill_count/(double)((double)NUM_BILLION_TRIES*(double)BILLION_TRIES));
  printf("\nCuckoo Spill Count: %llu (%5.3f)\n", cuckoo_spill_count,
         100.0* (double)cuckoo_spill_count/(double)((double)NUM_BILLION_TRIES*(double)BILLION_TRIES));

  return 0;
}
