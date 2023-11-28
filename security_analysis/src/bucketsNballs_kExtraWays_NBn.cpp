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
int EXTRA_BUCKET_CAPACITY = 2;  //set extra tags to 2

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
#define BILLION_TRIES (1000*1000) //thus is 1 bill i tihnk 
#define HUNDRED_MILLION_TRIES     (100*1000*1000)

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
};

union bucket_value {
  uns count;
  bucket_tuple* tuple_ptr; //index, cnt not sure about this?
};

//vector<bucket_value> bucket[NUM_BUCKETS];

//having count twice is not needed so use tuple pointer for count 
vector<bucket_value> bucket[NUM_BUCKETS];


//just fucntion declaration
void relocate(bucket_tuple* tuple_ptr, uns64 ballID);

void relocate2(bucket_tuple* tuple_ptr, uns64 ballID);

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


//priority queue that is used to determine which bucket to relocate and which bucket to insert into
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

  bucket_tuple* get_count_zero(){
    //uns64 size = storage_.size();
    //uns64 index = 0;
    //this linearly searches for the first element with count 0 
    for (const auto& element : storage_) {
      if (element->count == 0) {
        return element;
      }
      //index++;
    }
    return nullptr;
  }

private:
  void swap_elements(uns64 a, uns64 b) {
    std::swap(storage_[a], storage_[b]); //does this counts? no counts are the same
    std::swap(storage_[a]->index, storage_[b]->index); //do i also need to swap counts? or no i dont think
  }

private:
  //the issue is that this DS is very being modified when buckets is!!!!
  vector<bucket_tuple*> storage_;
};

GriffinsAwesomePriorityQueue pq;


////////////////////////////////////////////////////// 
//attempt Queue implementation with buckets array directly
//////////////////////////////////////////////////////


/*
class GriffinsAwesomePriorityQueue {
public:
  // Called when count is incremented.
  void heapify_upwards(uns64 index) {
    if (index == 0) {
      return;
    }

    uns64 parent_index = (index - 1) / 2;
    if (bucket[index].at(0).count > bucket[parent_index].at(0).count) {
      swap_elements(index, parent_index);
      heapify_upwards(parent_index);
    }
  }

  // Called when count is decremented.
  void heapify_downwards(uns64 index) {
    uns64 size = bucket.size();
    
    uns64 max = index;
    uns64 left_index = 2 * index + 1;
    uns64 right_index = 2 * index + 2;

    if (left_index < size && bucket[left_index].at(0).count > bucket[max].at(0).count) {
      max = left_index;
    }

    if (right_index < size && bucket[right_index].at(0).count > bucket[max].at(0).count) {
      max = right_index;
    }

    if (max != index) {
      swap_elements(index, max);
      heapify_downwards(max);
    }
  }

  bucket_tuple *top() const {
    return bucket[0];
  }

  void pop() {
    uns64 size = bucket.size();
    if (size == 0) {
      return;
    }
    swap_elements(0, size - 1);
    bucket.pop_back();
    heapify_downwards(0);
  }

  void push(bucket_tuple* element) {
    bucket.push_back(element);
    element->index = bucket.size() - 1;
    heapify_upwards(element->index);
  }

  uns64 size(void){
    uns64 size = bucket.size();
    return size;
  }

  bucket_tuple* get_element(uns64 index) {
    bucket_tuple* val = bucket[index];
    return val;
  }

  bucket_tuple* get_count_zero(){
    uns64 size = bucket.size();
    uns64 index = 0;
    //this linearly searches for the first element with count 0 
    for (const auto& element : bucket) {
      if (element->count == 0) {
        return element;
      }
      index++;
    }
    return nullptr;
  }

private:
  void swap_elements(uns64 a, uns64 b) {
    std::swap(bucket[a], bucket[b]); //does this counts? no counts are the same
    std::swap(bucket[a]->index, bucket[b]->index); //do i also need to swap counts? or no i dont think
  }
};

GriffinsAwesomePriorityQueue pq;

*/



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

  bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;

  cout << "start spill tuple cnt " << tuple_ptr->count << endl;
  cout << "start spill bucket cnt " << bucket[index].at(0).count << endl;
  cout << "start spill size " << tuple_ptr->ball_list.size() << endl;

  //decrement count of bucket that is full
  bucket[index].at(0).count--;
  //bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
  //remove inserted ball from bucket balls vector
  for (uns64 k =0; k < tuple_ptr->ball_list.size(); ++k){
    if (tuple_ptr->ball_list[k] == ballID) //search thru vector to erase ballid from ball list so wont be relocated by accidnet
    {
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin() + k);
      break;
    }
  }
  //reflect the pointer count to match the new count, this can just be a decremet, would probs be faster
  tuple_ptr->count--;

  cout << "spill tuple cnt " << tuple_ptr->count << endl;
  cout << "spill bucket cnt " << bucket[index].at(0).count << endl;
  cout << "spill size " << tuple_ptr->ball_list.size() << endl;
  assert(tuple_ptr->ball_list.size() == bucket[index].at(0).count);
  //heapify down to correct ordering as count is decreased
  pq.heapify_downwards(index);


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
      //increment count of bucket that ball is inserted into
      bucket[spill_index].at(0).count++;
      //set the ball to the new bucket
      balls[ballID] = spill_index;

      //get pointer to update needed values 
      bucket_tuple* tuple_ptr = bucket[spill_index].at(1).tuple_ptr;

      tuple_ptr->count++;
      //add ball to bucket balls vector
      tuple_ptr->ball_list.push_back(ballID);


      uns64 index_local = tuple_ptr->index; //this should be the balls location
      //heapify up to correct ordering as count is increased
      pq.heapify_upwards(index_local);

     
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

  //update count of bucket that ball is inserted into 

  bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
  bucket[index].at(0).count++;
  tuple_ptr->count++;
  tuple_ptr->ball_list.push_back(ballID);

  pq.heapify_upwards(tuple_ptr->index);




  //cout << "Inserting ballID: " << ballID << " into bucket: " << index << " with count: " << bucket[index].at(0).count << endl;

  //Track which bucket the new Ball was inserted in
  assert(balls[ballID] == (uns64)-1);
  balls[ballID] = index;


        //----------- SPILL --------
  if(SPILL_THRESHOLD && (retval >= SPILL_THRESHOLD)){
    //Overwrite balls[ballID] with spill_index.
    
    cout << "IN SPILL\n" <<endl;
    spill_ball(index,ballID);
    //return retval;  
  }

  //get pointer to update needed values
  //bucket_tuple* tuple_ptr = bucket[index].at(1).tuple_ptr;
  //update pointer count to match the new count
  //tuple_ptr->count++;
  //add ball id to current bucket
  //tuple_ptr->ball_list.push_back(ballID);

  //uns64 index_local = tuple_ptr->index; //this should be the balls location
  uns64 bucket_id = tuple_ptr->bucket; //this should be the balls location

  //heapify up to correct ordering as count is increased 
  //pq.heapify_upwards(index_local);

  //check if the ball is at the top of the heap, if so relocate it to a less full bucket
  //unsure if this should be above spill or not
  if(tuple_ptr->index == 0 && init_buckets_done == true && bucket[index].at(0).count != 0) {
    cout << "RELOCATE\n" <<endl;
    //cout << "Before relocation - Bucket count: " << bucket[index_local].at(0).count << endl;

    relocate2(tuple_ptr, ballID);
  }

  cout << "tuple cnt " << tuple_ptr->count << endl;
  cout << "bucket cnt " << bucket[bucket_id].at(0).count << endl;
  cout << "size " << tuple_ptr->ball_list.size() << endl;
  assert(tuple_ptr->ball_list.size() == bucket[bucket_id].at(0).count);

        //----------- SPILL --------
  //if(SPILL_THRESHOLD && (retval >= SPILL_THRESHOLD)){
    //Overwrite balls[ballID] with spill_index.
    
    //cout << "in spill\n" <<endl;
   // spill_ball(index,ballID);
    //return retval;  
  //}

  //cout << "After insertion, count in bucket: " << bucket[index].at(0).count << endl;
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

  // get bucket tuple
  //bucket_tuple* this_tuple = bucket[bucket_index].at(1).tuple_ptr; 
  //cout << bucket[bucket_index].at(0).count << endl;
  // check that bucket is not empty

  if (bucket[bucket_index].at(0).count == 0) {
    cout << "Bucket is empty" << endl;
    bucket_tuple* this_tuple = bucket[bucket_index].at(1).tuple_ptr;
    cout << "Bucket count: " << this_tuple->count << endl;
    cout << "Bucket index: " << this_tuple->index << endl;
    cout << "Bucket id: " << this_tuple->bucket << endl;
    cout << "Balls size" << this_tuple->ball_list.size() << endl;
    //if balls size is not 0 then why is count 0?? mrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr
  }
  

  //WHY IS THIS HAPPENING???
  assert(bucket[bucket_index].at(0).count != 0);  
  //isnt this saying that no bucket can be empty? which is not true........ wtf

  //cout << "Removing ballID: " << ballID << " from bucket: " << bucket_index << " with count: " << bucket[bucket_index].at(0).count << endl;


  // modify count of bucket
  bucket[bucket_index].at(0).count--;
  
  // -1 signals that ball is not assigned
  balls[ballID] = -1;


  //this is not needed as repeating set from above
  bucket_tuple* tuple_ptr = bucket[bucket_index].at(1).tuple_ptr;

  //set the count of the tuple to the new count
  tuple_ptr->count--;
  //get the index for heapify? check this step
  uns64 index_local = tuple_ptr->index;

  //search thru vector to erase ballid from ball list so wont be relocated by accidnet
  tuple_ptr->ball_list.erase(
  std::remove(tuple_ptr->ball_list.begin(), tuple_ptr->ball_list.end(), ballID),
  tuple_ptr->ball_list.end());


  cout << "tuple count " << tuple_ptr->count << endl;
  cout << "bucket count " << bucket[bucket_index].at(0).count << endl;
  cout << "size before" << tuple_ptr->ball_list.size() << endl;
  assert(tuple_ptr->ball_list.size() == bucket[bucket_index].at(0).count);
  
  /*
  for (uns64 k =0; k < tuple_ptr->ball_list.size(); ++k){
    if (tuple_ptr->ball_list[k] == ballID) 
    {
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin() + k);
      break;
    }
  }
  */
  
  pq.heapify_downwards(index_local);

  //cout << "After removal, count in bucket: " << bucket[bucket_index].at(0).count << endl;

  // Return BallID removed (ID will be reused for new ball to be inserted)  
  return ballID;
}

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

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

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

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



bool check_empty_buckets() {
  for (uns64 ii = 0; ii < NUM_BUCKETS; ii++) {
    if (bucket[ii].at(0).count == 0) {
      return true;
    }
  }
  return false;
}

/////////////////////////////////////////////////////
// Randomly Initialize all the Buckets with Balls (NumBuckets * BallsPerBucket) 
/////////////////////////////////////////////////////

void init_buckets(void){
  uns64 ii;
  assert(NUM_SKEWS * NUM_BUCKETS_PER_SKEW == NUM_BUCKETS);
  
  //Initialize Buckets with correct data structures

  //ensure that this is doing what I think it is!!
  
  for(ii=0; ii<NUM_BUCKETS; ii++){
    bucket_value count_value = {0};
    bucket[ii].push_back(count_value); //ad 0 to first entry in all vectors
    bucket_value null_value = {0};
    bucket[ii].push_back(null_value); //add empty entry in all buckets to place pointer to heap tuple
  }
  

  for (ii=0; ii<NUM_BUCKETS; ++ii){

    bucket_tuple* mytuple = new bucket_tuple(); //j, count);
    mytuple->count = 0;
    mytuple->index = 0; // i explicitly set the index in the push operation in the heap
    
    //set index to 0 and have heapfify in push determine the ordering??

    //bucket is unqiue id for each bucket
    mytuple->bucket = ii; 
    pq.push(mytuple); //this heapfies
    bucket[ii].at(1).tuple_ptr = mytuple;
  }

 
  for(ii=0; ii<(NUM_BUCKETS*BALLS_PER_BUCKET); ii++){
    balls[ii] = -1;
    insert_ball(ii);
  }

  for(ii=0; ii<=MAX_FILL; ii++){
    stat_counts[ii]=0;
  }

  bool check = check_empty_buckets();

  if (check == true) {
    cout << "There are empty buckets" << endl;
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
/////////////////////////////////////////////////////

//this just return the max element in the heap
void get_max_element(void){
  bucket_tuple* maxElement = pq.top();
  uns index = maxElement->index;
  uns64 count = maxElement->count;
  cout << "Max Element: Index = " << index << ", Count = " << count << endl;
}

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

//get min element in heap, USELESS
void get_min_element(void) {
  bucket_tuple* minElement = pq.get_count_zero();
  uns index = minElement->index;
  uns64 count = minElement->count;
  cout << "Min Element: Index = " << index << ", Count = " << count << endl;
}

// ////////////////////////////////////////////////
//use a max heap to keep track of element that is most full
//preemptively redistrubute to lessen used bucket
// ////////////////////////////////////////////////


//not sure how this will effect retval in insert 
//func responsible for relocating balls from full buckets to less full buckets
void relocate(bucket_tuple* tuple_ptr, uns64 ballID) {

  uns64 index_in_heap = tuple_ptr->index;
  uns64 buck_to_move = tuple_ptr->bucket;
  //cout<< "in relocate" << endl;

  //now swap out ball that was inserted

  //search for ball to be relocated in bucket balls vector and erase it, then decrease count
  
  tuple_ptr->ball_list.erase(
  std::remove(tuple_ptr->ball_list.begin(), tuple_ptr->ball_list.end(), ballID),
  tuple_ptr->ball_list.end());
  tuple_ptr->count--;
  bucket[buck_to_move].at(0).count--;


  
  /*
  for (uns64 k =0; k < tuple_ptr->ball_list.size(); ++k){
    if (tuple_ptr->ball_list[k] == ballID) //search thru vector to erase ballid from ball list so wont be relocated by accidnet
    {
      tuple_ptr->ball_list.erase(tuple_ptr->ball_list.begin() + k);
      tuple_ptr->count--; //decrease count and erase ball
      bucket[buck_to_move].at(0).count--;  //i think this is correct?? 
      break;
    }
  }
  */

  //correct heap ordering with new deleted ball 

  //pq.heapify_downwards(index_in_heap); 

  //get the bucket with the least amount of balls, or just the first bucket with 0 balls
  //bucket_tuple* tuple_last = pq.get_count_zero();


  uns64 bucket_id_to_reloc = mtrand->randInt(NUM_BUCKETS); //get random bucket to relocate ball to??? 

  //really this is random but whatever
  bucket_tuple* tuple_last  = bucket[bucket_id_to_reloc].at(1).tuple_ptr;

  uns64 index_to_reloc = tuple_last->index; //also in heap
  //get the bucket id of the bucket with the least amount of balls
  uns64 bucket_to_reloc = tuple_last->bucket;
  //get the count of the bucket with the least amount of balls to make sure 0 or maybe near 0? 
  //i guess i am assuming that the bucket with the least amount of balls will be 0 
  uns64 count = tuple_last->count;

  //note count already decremnted here
  cout << "Relocating ballID: " << ballID << " from bucket: " << buck_to_move << " to bucket: " << bucket_to_reloc << "with count " <<bucket[buck_to_move].at(0).count+1 << endl;

  //add ball to less bucket to relocate it to
  tuple_last->ball_list.push_back(ballID); //add ball to less used cache line
  //increase count of bucket that ball was relocated to tuple 
  tuple_last->count++;
  //increase count of bucket that ball was relocated to bucket
  bucket[bucket_to_reloc].at(0).count++;
  uns64 count1 = tuple_last->count;
  //cout << "tuple count1 " << count1 << endl;
  
  //cahnge ball to relfect new location
  balls[ballID] = bucket_to_reloc;
  //correct heap ordering with new inserted ball
  tuple_last->index = index_to_reloc; //not sure about this

  //pq.heapify_upwards(index_to_reloc);
  pq.heapify_downwards(0); // idk heapify the whole thing?
  uns64 idx = tuple_last->index;
  //cout << "new idx " << idx << endl; //index is staying the same?

  cout << "After relocation, count in bucket to move: " << bucket[buck_to_move].at(0).count << endl;
  cout << "After relocation, count in destination bucket: " << bucket[bucket_to_reloc].at(0).count << endl;

  number_relocations++;
}


void relocate2(bucket_tuple* tuple_ptr, uns64 ballID) {
    uns64 index_in_heap = tuple_ptr->index;
    uns64 buck_to_move = tuple_ptr->bucket;

    // Remove the ball from the current bucket
    tuple_ptr->ball_list.erase(
    std::remove(tuple_ptr->ball_list.begin(), tuple_ptr->ball_list.end(), ballID),
    tuple_ptr->ball_list.end());

    tuple_ptr->count--;
    bucket[buck_to_move].at(0).count--;

    pq.heapify_downwards(index_in_heap);

    // Get a random destination bucket
    //uns64 bucket_id_to_reloc = mtrand->randInt(NUM_BUCKETS);
    bucket_tuple* tuple_last =  pq.get_count_zero();
    uns64 index_to_reloc = tuple_last->index;
    uns64 bucket_to_reloc = tuple_last->bucket;

    cout << "tuple count " << tuple_last->count << endl;
    cout << "bucket count " << bucket[bucket_to_reloc].at(0).count << endl;
    cout << "size before" << tuple_last->ball_list.size() << endl;

    // Move the ball to the new bucket
    tuple_last->ball_list.push_back(ballID); //add ball to less used cache line??
    tuple_last->count++;
    bucket[bucket_to_reloc].at(0).count++;
    balls[ballID] = bucket_to_reloc;
    //tuple_last->index = index_to_reloc;

    // Fix the heap ordering
    pq.heapify_downwards(0);

    // Print relocation details
    cout << "Relocating ballID: " << ballID << " from bucket: " << buck_to_move
         << " to bucket: " << bucket_to_reloc << " with count " << bucket[buck_to_move].at(0).count + 1 << endl;

    cout << "After relocation, count in bucket to move: " << bucket[buck_to_move].at(0).count << endl;
    cout << "After relocation, count in destination bucket: " << bucket[bucket_to_reloc].at(0).count << endl;

    number_relocations++;

    //assert(tuple_last->ball_list.size() -1 == bucket[bucket_to_reloc].at(0).count);
    cout << "after tuple count " << tuple_last->count << endl;
    cout << "after bucket count " << bucket[bucket_to_reloc].at(0).count << endl;
    cout << "after size " << tuple_last->ball_list.size() << endl;

    assert(tuple_last->ball_list.size() == bucket[bucket_to_reloc].at(0).count);
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
  assert((argc == 4) && "Need 3 arguments: (EXTRA_BUCKET_CAPACITY:[0-8] BN_BALL_THROWS:[1-10^5] SEED:[1-400])");
  EXTRA_BUCKET_CAPACITY = atoi(argv[1]);
  SPILL_THRESHOLD = BASE_WAYS_PER_SKEW + EXTRA_BUCKET_CAPACITY;
  NUM_BILLION_TRIES  = atoi(argv[2]);
  myseed = atoi(argv[3]);

  printf("Cache Configuration: %d MB, %d skews, %d ways (%d ways/skew)\n",CACHE_SZ_BYTES/1024/1024,NUM_SKEWS,NUM_SKEWS*BASE_WAYS_PER_SKEW,BASE_WAYS_PER_SKEW);
  printf("AVG-BALLS-PER-BUCKET:%d, BUCKET-SPILL-THRESHOLD:%d \n",BASE_WAYS_PER_SKEW,SPILL_THRESHOLD);
  printf("Simulation Parameters - BALL_THROWS:%llu, SEED:%d\n\n",(unsigned long long)NUM_BILLION_TRIES*(unsigned long long)BILLION_TRIES,myseed);
  uns64 ii;
  mtrand->seed(myseed);

  //Initialize Buckets
  init_buckets();
  sanity_check();
  //print_heap();

  printf("Starting --  (Dot printed every 100M Ball throws) \n");

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
      get_max_element();
      get_min_element();
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
