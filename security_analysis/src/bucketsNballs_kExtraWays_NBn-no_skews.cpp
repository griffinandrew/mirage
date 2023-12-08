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
#define BILLION_TRIES (1000*1000*1000)
#define HUNDRED_MILLION_TRIES     (1000*1000*100)


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

uns64 last_row_count_found = 0;



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



/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
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
  //decrement count of bucket that is full
  bucket[index].at(0).count--;
  //reflect the pointer count to match the new count, this can just be a decremet, would probs be faster
  tuple_ptr->count--;
  //heapify up to correct ordering as count is decreased
  pq_min.heapify_upwards(tuple_ptr->index_min);
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
      pq_min.heapify_downwards(tuple_spill->index_min);
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

  //get pointer to update needed values
  bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
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
  pq_min.heapify_downwards(tuple_ptr->index_min);
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

  if(bucket[bucket_id].at(0).count > BALLS_PER_BUCKET){
    //relocate_LRU(tuple_ptr);
    //relocate_LFU(tuple_ptr);
    relocate_smart(tuple_ptr);
  }

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
  
  pq_min.heapify_upwards(tuple_ptr->index_min);
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
    //add to min heap
    pq_min.push(mytuple);
    //add to lfu heap
    //pq_lfu.push(mytuple);
    //add to lru heap
    //pq_lru.push(mytuple);
    //set the pointer to the tuple in the bucket
    bucket[ii].at(1).tuple_ptr = mytuple;

    //above are changes
    /////////////////////////////////////////////////
  }
   
  for(ii=0; ii<(NUM_BUCKETS*BALLS_PER_BUCKET); ii++){
    balls[ii] = -1;
    insert_ball(ii);
  }

  for(ii=0; ii<=MAX_FILL; ii++){
    stat_counts[ii]=0;
  }

  sanity_check();
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

    //cout << "tuple count" << tuple_ptr->count << endl;

    //var to keep track of how many balls to relocate
    uns64 amount_to_relcoate = 1; 

    if (tuple_ptr->count == BALLS_PER_BUCKET) {
      return;
    }

    tuple_last = pq_min.top();
        
    if(tuple_last == nullptr) {
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
    pq_min.heapify_upwards(tuple_ptr->index_min);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;


   ///////////////////////////////////////
    //check this could be source of error? it was needed to be inverted
    pq_min.heapify_downwards(tuple_last->index_min);

    number_relocations++;
  
}

/////////////////////////////////////////////////////
//relocate function, that mimics LFU
/////////////////////////////////////////////////////


void relocate_LFU(bucket_tuple* tuple_ptr) {
    uns64 buck_to_move = tuple_ptr->bucket;

    bucket_tuple* tuple_last = pq_lfu.top();

    
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

    pq_lfu.heapify_upwards(tuple_ptr->index_lfu);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    tuple_last->frequency++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;

    // Fix the heap ordering
    pq_lfu.heapify_downwards(tuple_last->index_lfu);

    number_relocations++;
}



/////////////////////////////////////////////////////
//relocate function, that mimics LRU
/////////////////////////////////////////////////////



void relocate_LRU(bucket_tuple* tuple_ptr) {
    uns64 buck_to_move = tuple_ptr->bucket;

    bucket_tuple* tuple_last = pq_lru.top();
    
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
    pq_lru.heapify_upwards(tuple_ptr->index_lru);

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
    tuple_last->count++;
    bucket[tuple_last->bucket].at(0).count++;
    tuple_last->frequency++;
    tuple_last->access_count = current_timestamp++;
    //this is the reason why I must keep track of the balls 
    balls[firstBall] = tuple_last->bucket;

    // Fix the heap ordering
    pq_lru.heapify_upwards(tuple_last->index_lru);

    number_relocations++;
  
}


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

int main(int argc, char* argv[]){

  //Get arguments:
  assert((argc == 5) && "Need 4 arguments: (EXTRA_BUCKET_CAPACITY:[0-8] BN_BALL_THROWS:[1-10^5] SEED:[1-400] NUM_WAYS:[4,8,16])");
  EXTRA_BUCKET_CAPACITY = atoi(argv[1]);
  SPILL_THRESHOLD = BASE_WAYS_PER_SKEW + EXTRA_BUCKET_CAPACITY;
  NUM_BILLION_TRIES  = atoi(argv[2]);
  myseed = atoi(argv[3]);

  CURR_NUM_WAYS = atoi(argv[4]);
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