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
#define BILLION_TRIES (1000*1000) //thus is 1 1 i tihnk 
#define HUNDRED_MILLION_TRIES     (100*1000) //for 4 ways use size 10*1000


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
  uns64 index; //current location in the heap
  uns64 access_count; //number of times bucket has been accessed, used for LRU
  uns64 frequency; //number of times bucket has been accessed, used for LFU
};

union bucket_value {
  uns count;
  bucket_tuple* tuple_ptr; //index, cnt not sure about this?
};

//having count twice is not needed so use tuple pointer for count 
vector<bucket_value> bucket[NUM_BUCKETS];

//just fucntion declarations
void relocate(bucket_tuple* tuple_ptr);

void relocate_LRU(bucket_tuple* tuple_ptr);

void relocate_LFU(bucket_tuple* tuple_ptr);

void relocate_low_overhead(bucket_tuple* tuple_ptr);


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


//can prob delete now
uns64 number_no_1 = 0;
uns64 number_no_2 = 0;
uns64 number_no_3 = 0;
uns64 number_no_4 = 0;
uns64 number_no_5 = 0;
uns64 number_no_6 = 0;
uns64 number_no_7 = 0;
uns64 number_no_8 = 0;
uns64 number_no_9 = 0;
uns64 number_no_10 = 0;
uns64 number_no_11 = 0;
uns64 number_no_12 = 0;
uns64 number_no_13 = 0;
uns64 number_no_14 = 0;
uns64 number_no_15 = 0;

//this is used to determine how many balls to relocate
uns64 CURR_NUM_WAYS = 0;


uns64 last_row_count_found = 0;


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
//priority queue that is used to determine which 
//bucket to relocate and which bucket to insert into
/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

class GriffinsAwesomePriorityQueue {
public:
  // Called when count is incremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (storage_[index]->count > storage_[parent_index]->count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is decremented.
  void heapify_downwards(uns64 index) {
    uns64 size = storage_.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && storage_[left_index]->count > storage_[max]->count) {
      max = left_index;
    }

    if (right_index < size && storage_[right_index]->count > storage_[max]->count) {
      max = right_index;
    }

    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    return storage_[0];
  }

  void pop() {
    uns64 size = storage_.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    storage_.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    storage_.push_back(element);
    element->index = storage_.size() - 1;
    heapify_upwards(element->index);
  }

  uns64 size(void){
    uns64 size = storage_.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = storage_[index];
    return val;
  }

    bucket_tuple* get_least_filled_4ways(){
    //this linearly searches for the first element with count 0 
    bool zero_found = false;
    bool one_found = false;
    bool two_found = false;
    bool three_found = false;

    for (const auto& element : storage_) {
      if (element->count == 0) {
        number_empty_buckets++;
        bool zero_found = true;
        return element;
      }
    }
    if (zero_found == false) {
      for (const auto& element : storage_) {
        if (element->count == 1) {
          number_no_1++;
          bool one_found = true;
          return element;
        }
      }
    }
    if(one_found == false) {
      for (const auto& element : storage_) {
        if (element->count == 2) {
          number_no_2++;  
          bool two_found = true;
          return element;
        }
      }
    }
    if(two_found == false) {
      for (const auto& element : storage_) {
        if (element->count == 3) {
          bool three_found = true;
          return element;
        }
      }
    }
    return nullptr;
  }

  bucket_tuple* get_least_filled_8ways(){
      bool zero_found = false;
      bool one_found = false;
      bool two_found = false;
      bool three_found = false;
      bool four_found = false;
      bool five_found = false;
      bool six_found = false;
      bool seven_found = false;

      for (const auto& element : storage_) {
        if (element->count == 0) {
          number_empty_buckets++;
          bool zero_found = true;
          return element;
        }
      }
      if (zero_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 1) {
            number_no_1++;
            bool one_found = true;
            return element;
          }
        }
      }
      if(one_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 2) {
            number_no_2++;  
            bool two_found = true;
            return element;
          }
        }
      }
      if(two_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 3) {
            number_no_3++;
            bool three_found = true;
            return element;
          }
        }
      }
      if(three_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 4) {
            number_no_4++;
            bool four_found = true;
            return element;
          }
        }
      }
      if(four_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 5) {
            number_no_5++;
            bool five_found = true;
            return element;
          }
        }
      }
      if(five_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 6) {
            number_no_6++;
            bool six_found = true;
            return element;
          }
        }
      }
      if(six_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 7) {
            number_no_7++;
            bool seven_found = true;
            return element;
          }
        }
      }
      return nullptr;
  }

  bucket_tuple* get_least_filled_16ways(){
      bool zero_found = false;
      bool one_found = false;
      bool two_found = false;
      bool three_found = false;
      bool four_found = false;
      bool five_found = false;
      bool six_found = false;
      bool seven_found = false;
      bool eight_found = false;
      bool nine_found = false;
      bool ten_found = false;
      bool eleven_found = false;
      bool twelve_found = false;
      bool thirteen_found = false;
      bool fourteen_found = false;
      bool fifteen_found = false;

      for (const auto& element : storage_) {
        if (element->count == 0) {
          number_empty_buckets++;
          bool zero_found = true;
          return element;
        }
      }
      if (zero_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 1) {
            number_no_1++;
            bool one_found = true;
            return element;
          }
        }
      }
      if(one_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 2) {
            number_no_2++;  
            bool two_found = true;
            return element;
          }
        }
      }
      if(two_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 3) {
            number_no_3++;
            bool three_found = true;
            return element;
          }
        }
      }
      if(three_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 4) {
            number_no_4++;
            bool four_found = true;
            return element;
          }
        }
      }
      if(four_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 5) {
            number_no_5++;
            bool five_found = true;
            return element;
          }
        }
      }
      if(five_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 6) {
            number_no_6++;
            bool six_found = true;
            return element;
          }
        }
      }
      if(six_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 7) {
            number_no_7++;
            bool seven_found = true;
            return element;
          }
        }
      }
      if(seven_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 8) {
            number_no_8++;
            bool eight_found = true;
            return element;
          }
        }
      }
      if(eight_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 9) {
            number_no_9++;
            bool nine_found = true;
            return element;
          }
        }
      }
      if(nine_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 10) {
            number_no_10++;
            bool ten_found = true;
            return element;
          }
        }
      }
      if(ten_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 11) {
            number_no_11++;
            bool eleven_found = true;
            return element;
          }
        }
      }
      if(eleven_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 12) {
            number_no_12++;
            bool twelve_found = true;
            return element;
          }
        }
      }
      if(twelve_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 13) {
            number_no_13++;
            bool thirteen_found = true;
            return element;
          }
        }
      }
      if(thirteen_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 14) {
            number_no_14++;
            bool fourteen_found = true;
            return element;
          }
        }
      }
      if(fourteen_found == false) {
        for (const auto& element : storage_) {
          if (element->count == 15) {
            number_no_15++;
            bool fifteen_found = true;
            return element;
          }
        }
      }
      return nullptr;
  }



private:
  void swap_elements(uns64 a, uns64 b) {
    std::swap(storage_[a], storage_[b]); //does this counts? no counts are the same
    std::swap(storage_[a]->index, storage_[b]->index); //do i also need to swap counts? or no i dont think
  }

private:
  vector<bucket_tuple*> storage_;
};

GriffinsAwesomePriorityQueue pq;

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
  //heapify down to correct ordering as count is decreased
  pq.heapify_downwards(index);
  
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
      //heapify up to correct ordering as count is increased
      pq.heapify_upwards(tuple_spill->index);
      
      
      //above are changes
      ////////////////////////////////////////////////////////////////
     
    } else {
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
  //heapify up to correct ordering as count is increased 
  pq.heapify_upwards(tuple_ptr->index);
  
  //get bucket id to send to relocate if needed
  //on second thought is this not just index??
  uns64 bucket_id = tuple_ptr->bucket;

  //above are changes
  ////////////////////////////////////////////////////////////////

  //Track which bucket the new Ball was inserted in
  assert(balls[ballID] == (uns64)-1);
  balls[ballID] = index;

  ////////////////////////////////////////////////////////////////
  //below are changes

  //why am i relocating if at average tho?? this is not needed!!!
  //if(bucket[bucket_id].at(0).count >= SPILL_THRESHOLD) {
  if(bucket[bucket_id].at(0).count  >= BALLS_PER_BUCKET){ //but now night shouldnt this not be the case?? because it already spilled?? MFs
  //if(bucket[bucket_id].at(0).count  >= 3){
    //relocate(tuple_ptr); //now just every time a ball is inserted it is relocated
    relocate_low_overhead(tuple_ptr);
    //relocate_LRU(tuple_ptr);
    //relocate_LFU(tuple_ptr);
  }
  //relocate_LFU(tuple_ptr);

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
  
  pq.heapify_downwards(tuple_ptr->index);
  
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
    bucket_tuple* mytuple = new bucket_tuple(); //j, count);
    mytuple->count = 0;
    //set the index in the push operation in the heap
    mytuple->index = 0;
    //bucket is unqiue id for each bucket
    mytuple->bucket = ii; 
    //add access counters
    mytuple->access_count = 0;
    //add frequency counters
    mytuple->frequency = 0;
    //this heapfies and adds to heap
    pq.push(mytuple);
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
  printf("done init buckets\n");
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


/////////////////////////////////////////////////////
//get number of balls to relocate based on how many balls are in the bucket
/////////////////////////////////////////////////////

//detect how many balls to relocate based on how many balls are in the bucket, guesses for now, but work well
uns64 get_number_to_relocate_16(bucket_tuple* tuple_ptr) 
{
  uns64 amount_to_relcoate = 0;
  switch(tuple_ptr->count) {
      case 0:
      case 1:
      case 2:
      case 3:
      case 4:
      case 5:
      case 6:
      case 7:
      case 8:
        amount_to_relcoate = 3;
        break;
      case 9:
      case 10:
      case 11:
        amount_to_relcoate = 2;
        break;
      case 12:  
      case 13:
      case 14:
      case 15:
        amount_to_relcoate = 1;
        break;
      default:
        break;
    }
    return amount_to_relcoate;
}



uns64 get_number_to_relocate_8(bucket_tuple* tuple_ptr) 
{
  uns64 amount_to_relcoate; 
  switch(tuple_ptr->count) {
    case 0:
    case 1:
    case 2:
    case 3:
    case 4:
    case 5:
      amount_to_relcoate = 2;
      break;
    case 6:
    case 7:
      amount_to_relcoate = 1;
      break;
    default:
      amount_to_relcoate = 0;
      break;
  }
  return amount_to_relcoate;
}


///////////////////////////////////////////////////////////////
//get number of balls to relocate based on how many balls are in the bucket
///////////////////////////////////////////////////////////////

//detect how many balls to relocate based on how many balls are in the bucket, guesses for now, but work well
uns64 get_number_to_relocate_4(bucket_tuple* tuple_ptr) 
{
  uns64 amount_to_relcoate = 0; 
  switch(tuple_ptr->count) {
      case 0:
      case 1:
        amount_to_relcoate = 2;
        break;
      case 2:
      case 3:
       amount_to_relcoate = 1;
        break;
      default:
        break;
    }
  return amount_to_relcoate;
}

///////////////////////////////////////////////////////////////
//get number of less filled bucket, for 4 ways
///////////////////////////////////////////////////////////////

bucket_tuple* get_min_bucket_4ways() {
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 0) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 1) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 2) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 3) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  return nullptr; // Return nullptr if no empty bucket is foun
}


///////////////////////////////////////////////////////////////
//get number of less filled bucket, for 8 ways
///////////////////////////////////////////////////////////////

bucket_tuple* get_min_bucket_8ways() {
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 0) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 1) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 2) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 3) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
    for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 4) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 5) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 6) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 7) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  return nullptr; // Return nullptr if no empty bucket is foun
}




///////////////////////////////////////////////////////////////
//get number of less filled bucket, for 16 ways
///////////////////////////////////////////////////////////////

bucket_tuple* get_min_bucket_16ways() {
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 0) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 1) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 2) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 3) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
    for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 4) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 5) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 6) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 7) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 8) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 9) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 10) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 11) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
    for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 12) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 13) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 14) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  for (int i = 0; i < NUM_BUCKETS; ++i) {
    if (bucket[i].at(0).count == 15) {
      number_empty_buckets++;
      return bucket[i].at(1).tuple_ptr; // Return a pointer to the element
    }
  }
  return nullptr; // Return nullptr if no empty bucket is foun
}


////////////////////////////////////////////////////////////
//ideal relocate function, that creates even distribution
////////////////////////////////////////////////////////////

void relocate(bucket_tuple* tuple_ptr) {
    uns64 index_in_heap = tuple_ptr->index;
    uns64 buck_to_move = tuple_ptr->bucket;
    bucket_tuple* tuple_last = nullptr;

    //var to keep track of how many balls to relocate
    uns64 amount_to_relcoate; 

    //determine which bucket to relocate to based on the number of ways
    switch(CURR_NUM_WAYS) {
      case 4:
        tuple_last = pq.get_least_filled_4ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_4(tuple_last); 
        break;
      case 8:
        tuple_last = pq.get_least_filled_8ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_8(tuple_last);
        break;
      case 16:
        tuple_last = pq.get_least_filled_16ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_16(tuple_last);
        break;
      default:
        break;
    }
    //cout << "amount to relocate: " << amount_to_relcoate << endl;
    //cout << "number of balls in bucket: " << tuple_ptr->count << endl;



    for (uns64 i = 0; i < amount_to_relcoate; ++i) {
      //get the first ball in the bucket to remove
      uns64 firstBall = tuple_ptr->ball_list.front();
      //erase bucket at the front of the list 
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

      //decrement the count of the bucket that is being relocated from
      tuple_ptr->count--;
      bucket[buck_to_move].at(0).count--;
      //heapify down to correct ordering as count is decreased
      pq.heapify_downwards(index_in_heap);

      // Move the ball to the new bucket
      tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
      tuple_last->count++;
      bucket[tuple_last->bucket].at(0).count++;
      //this is the reason why I must keep track of the balls 
      balls[firstBall] = tuple_last->bucket;

      // Fix the heap ordering
      pq.heapify_downwards(tuple_last->index);

      number_relocations++;
  }
  
}


/////////////////////////////////////////////////////
//relocate function, that mimics LRU
/////////////////////////////////////////////////////

void relocate_LRU(bucket_tuple* tuple_ptr) {
    uns64 index_in_heap = tuple_ptr->index;
    uns64 buck_to_move = tuple_ptr->bucket;

    bucket_tuple* tuple_last = pq.get_element(0);
    for (uns64 i = 1; i < pq.size(); ++i) {
      bucket_tuple* current_tuple = pq.get_element(i);
      if (current_tuple->access_count < tuple_last->access_count) {
        tuple_last = current_tuple;
      }
    }
    
    if (tuple_last == nullptr) {
      return;
    }

    if (tuple_last->count == SPILL_THRESHOLD) {
      return;
    }
    
    uns64 amount_to_relcoate = 0;
    switch(CURR_NUM_WAYS) {
      case 4:
        amount_to_relcoate = get_number_to_relocate_4(tuple_last); 
        break;
      case 8:
        amount_to_relcoate = get_number_to_relocate_8(tuple_last);
        break;
      case 16:
        amount_to_relcoate = get_number_to_relocate_16(tuple_last);
        break;
      default:
        break;
    }


    for (uns64 i = 0; i < amount_to_relcoate; ++i) {
      //get the first ball in the bucket to remove
      uns64 firstBall = tuple_ptr->ball_list.front();
      //erase bucket at the front of the list 
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

      //decrement the count of the bucket that is being relocated from
      tuple_ptr->count--;
      bucket[buck_to_move].at(0).count--;
      //heapify down to correct ordering as count is decreased
      pq.heapify_downwards(index_in_heap);

      // Move the ball to the new bucket
      tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
      tuple_last->count++;
      bucket[tuple_last->bucket].at(0).count++;
      //this is the reason why I must keep track of the balls 
      balls[firstBall] = tuple_last->bucket;

      // Fix the heap ordering
      pq.heapify_downwards(tuple_last->index);

      number_relocations++;
  }
}



/////////////////////////////////////////////////////
// low overhead relocate function 
/////////////////////////////////////////////////////


void relocate_low_overhead(bucket_tuple* tuple_ptr) {
    uns64 index_in_heap = tuple_ptr->index;
    uns64 buck_to_move = tuple_ptr->bucket;
    bucket_tuple* tuple_last = nullptr;

    //var to keep track of how many balls to relocate
    uns64 amount_to_relcoate; 

    //determine which bucket to relocate to based on the number of ways
    switch(CURR_NUM_WAYS) {
      case 4:
        tuple_last = get_min_bucket_4ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_4(tuple_last); 
        break;
      case 8:
        tuple_last = get_min_bucket_8ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_8(tuple_last);
        break;
      case 16:
        tuple_last =get_min_bucket_16ways();
        if(tuple_last == nullptr) {
          return;
        }
        amount_to_relcoate = get_number_to_relocate_16(tuple_last);
        break;
      default:
        break;
    }


    for (uns64 i = 0; i < amount_to_relcoate; ++i) {
      //get the first ball in the bucket to remove
      uns64 firstBall = tuple_ptr->ball_list.front();
      //erase bucket at the front of the list 
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

      //decrement the count of the bucket that is being relocated from
      tuple_ptr->count--;
      bucket[buck_to_move].at(0).count--;
      //heapify down to correct ordering as count is decreased
      pq.heapify_downwards(index_in_heap);

      // Move the ball to the new bucket
      tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
      tuple_last->count++;
      bucket[tuple_last->bucket].at(0).count++;
      //this is the reason why I must keep track of the balls 
      balls[firstBall] = tuple_last->bucket;

      // Fix the heap ordering
      pq.heapify_downwards(tuple_last->index);

      number_relocations++;
  }
  
}


/////////////////////////////////////////////////////
//relocate function, that mimics LFU
/////////////////////////////////////////////////////

void relocate_LFU(bucket_tuple* tuple_ptr) {
    uns64 index_in_heap = tuple_ptr->index;
    uns64 buck_to_move = tuple_ptr->bucket;

    bucket_tuple* tuple_last = pq.get_element(0);
    for (uns64 i = 1; i < pq.size(); ++i) {
      bucket_tuple* current_tuple = pq.get_element(i);
      if (current_tuple->frequency < tuple_last->frequency) {
        tuple_last = current_tuple;
      }
    }
    
    if (tuple_last == nullptr) {
      return;
    }

    if (tuple_last->count >= SPILL_THRESHOLD) {
      return;
    }


    uns64 amount_to_relcoate = 0;
    switch(CURR_NUM_WAYS) {
      case 4:
        amount_to_relcoate = get_number_to_relocate_4(tuple_last); 
        break;
      case 8:
        amount_to_relcoate = get_number_to_relocate_8(tuple_last);
        break;
      case 16:
        amount_to_relcoate = get_number_to_relocate_16(tuple_last);
        break;
      default:
        break;
    }
    

    for (uns64 i = 0; i < amount_to_relcoate; ++i) {

      //get the first ball in the bucket to remove
      uns64 firstBall = tuple_ptr->ball_list.front();
      //erase bucket at the front of the list 
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin()); 

      //decrement the count of the bucket that is being relocated from
      tuple_ptr->count--;
      bucket[buck_to_move].at(0).count--;
      //heapify down to correct ordering as count is decreased
      pq.heapify_downwards(index_in_heap);

      // Move the ball to the new bucket
      tuple_last->ball_list.push_back(firstBall); //add ball to less used cache line??
      tuple_last->count++;
      bucket[tuple_last->bucket].at(0).count++;
      tuple_last->frequency++;
      //this is the reason why I must keep track of the balls 
      balls[firstBall] = tuple_last->bucket;

      // Fix the heap ordering
      pq.heapify_downwards(tuple_last->index);

      number_relocations++;
  }
}


/////////////////////////////////////////////////////
/////////////////////////////////////////////////////
void print_heap() {
    cout << "Heap Elements: ";
    for (uns64 i = 0; i < pq.size(); ++i) {
        bucket_tuple* element = pq.get_element(i);
        cout << "(" << element->count << ", " << element->bucket << ") " <<endl;
    }
    cout << endl;
}

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

int main(int argc, char* argv[]){

  //Get arguments:
  //assert((argc == 4) && "Need 3 arguments: (EXTRA_BUCKET_CAPACITY:[0-8] BN_BALL_THROWS:[1-10^5] SEED:[1-400])");
  EXTRA_BUCKET_CAPACITY = atoi(argv[1]);
  SPILL_THRESHOLD = BASE_WAYS_PER_SKEW + EXTRA_BUCKET_CAPACITY;
  NUM_BILLION_TRIES  = atoi(argv[2]);
  myseed = atoi(argv[3]);

  CURR_NUM_WAYS = atoi(argv[4]);
  cout << "CURR_NUM_WAYS " << CURR_NUM_WAYS << endl;


  printf("Cache Configuration: %d MB, %d skews, %d ways (%d ways/skew)\n",CACHE_SZ_BYTES/1024/1024,NUM_SKEWS,NUM_SKEWS*BASE_WAYS_PER_SKEW,BASE_WAYS_PER_SKEW);
  printf("AVG-BALLS-PER-BUCKET:%d, BUCKET-SPILL-THRESHOLD:%d \n",BASE_WAYS_PER_SKEW,SPILL_THRESHOLD);
  printf("Simulation Parameters - BALL_THROWS:%llu, SEED:%d\n\n",(unsigned long long)NUM_BILLION_TRIES*(unsigned long long)BILLION_TRIES,myseed);
  uns64 ii;
  mtrand->seed(myseed);

  //Initialize Buckets
  init_buckets();
  sanity_check();

  printf("Starting --  (Dot printed every 100M Ball throws) \n");
  cout << "extra buck cap " << EXTRA_BUCKET_CAPACITY << endl;

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
      cout << "Number of relocations: " << number_relocations << endl;
    }    
    //Ensure Total Balls in Buckets is Conserved.
    sanity_check();
    //Print count of Balls Thrown.
    printf(" %llu\n",bn_i+1);fflush(stdout);    
  }
  cout << number_relocations << endl;
  

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
