// Copyright (C) 2021, Gururaj Saileshwar, Moinuddin Qureshi: Georgia Institute of Technology.

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <queue> //used for max heap
#include <tuple>
#include "mtrand.h"
#include <any>

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
//modify the array to be an array of vecotrs s.t. can contain pointer to max heap entry, as well as pointers to all balls in that bucket
//using bucket_element = std::variant<uns64, tuple<uns, uns64>*>;

using bucket_tuple = tuple<uns, uns64>;

union bucket_value {
    uns count;
    bucket_tuple* tuple_ptr; //index, cnt not sure about this?
};

vector<bucket_value> bucket[NUM_BUCKETS];

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

//max heap to track most used bucket first elemenet is the bucket entry, second is the count
//std::priority_queue<tuple<uns, uns64>, vector<tuple<uns, uns64>>, tuple_comparator> maxHeap; //define a max heap that stores buckets



//count of balls in each bucket used to determine orderingx
struct tuple_comparator {
    bool operator()(const tuple<uns, uns64> t1, const tuple<uns, uns64>t2) const {
        // Compare based on the (count) of the tuple second item
        return get<1>(t1) < get<1>(t2);
    }
};

//max heap to track most used bucket first elemenet is the bucket entry, second is the count
std::priority_queue<tuple<uns, uns64>, vector<tuple<uns, uns64>>, tuple_comparator> maxHeap; //define a max heap that stores buckets


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

  bucket[index].at(0).count--; //assuming 0 is the count, dec count
  
  //uns64 count = bucket[index].at(0).count;
  //get<1>(*bucket[index].at(1).tuple_ptr) = count;

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
      bucket[spill_index].at(0).count++;
      balls[ballID] = spill_index;
      //uns64 count = bucket[spill_index].at(0).count;
      //get<1>(*bucket[spill_index].at(1).tuple_ptr) = count;
     
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

  //Increments count for Bucket where Ball Inserted 
  retval = bucket[index].at(0).count;
  bucket[index].at(0).count++;

  //Track which bucket the new Ball was inserted in
  assert(balls[ballID] == (uns64)-1);
  balls[ballID] = index;
  
  //----------- SPILL --------
  if(SPILL_THRESHOLD && (retval >= SPILL_THRESHOLD)){
    //Overwrite balls[ballID] with spill_index.
    spill_ball(index,ballID);   
  }

  //add to max queue now to track distribution
  //maxHeap.push(index);
  //bucket_tuple* tuple_ptr= bucket[index].at(1).tuple_ptr;
  //printf("here\n");
  //bucket_tuple& original_tuple = *tuple_ptr;
  //printf("here\n");
  if(init_heap_done == true) {
     //printf("Before: %p\n", (void*)bucket[index].at(1).tuple_ptr);
     get<1>(*bucket[index].at(1).tuple_ptr) = retval;
     //std::cout << "Value: " << get<1>(*(bucket[index].at(1).tuple_ptr)) << std::endl;
     //std::cout << "index: " << get<0>(*(bucket[index].at(1).tuple_ptr)) << std::endl;
  }
  //printf("Before: %p\n", (void*)bucket[index].at(1).tuple_ptr);
  //get<1>(*bucket[index].at(1).tuple_ptr) = retval; //set the current value of the tuple count equal to the curr count
  //bucket_tuple* tuple_ptr = &buckets[index].at(1).t
  //printf("here\n");


  
  // Return num-balls in bucket where new ball inserted.
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
  uns64 bucket_index = balls[ballID];

  // Update Ball Tracking
  assert(bucket[bucket_index].at(0).count != 0 );  
  bucket[bucket_index].at(0).count--;
  balls[ballID] = -1;

  //update count when removed
  uns64 count = bucket[bucket_index].at(0).count;
  get<1>(*bucket[bucket_index].at(1).tuple_ptr) = count;
  
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

  //  printf("\n");
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

/////////////////////////////////////////////////////
// Randomly Initialize all the Buckets with Balls (NumBuckets * BallsPerBucket) 
/////////////////////////////////////////////////////

void init_buckets(void){
  uns64 ii;
  assert(NUM_SKEWS * NUM_BUCKETS_PER_SKEW == NUM_BUCKETS);
  
  //printf("in pushback\n");
  for(ii=0; ii<NUM_BUCKETS; ii++){
    bucket_value count_value = {0};
    bucket[ii].push_back(count_value); //ad 0 to first entry in all vectors
    bucket_value null_value = {0};
    bucket[ii].push_back(null_value); //add empty entry in all buckets to place pointer to heap tuple
  }
  //printf("done in pushback\n");

  //for(ii=0; ii<NUM_BUCKETS; ii++){
  //  bucket[ii].at(0)=0;
  //}
 
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



void init_heap(void){
  for (uns64 j=0; j<NUM_BUCKETS; ++j){
    //maxHeap.push(make_tuple(j, bucket[j].at(0));
    uns64 count = bucket[j].at(0).count;
    bucket_tuple* mytuple = new bucket_tuple(j, count);
    maxHeap.push(*mytuple);
    bucket[j].at(1).tuple_ptr = mytuple;
    //buckets_tuple* ptr = &
    //bucket[j].at(1).tuple_ptr = mytuple;
  }
  init_heap_done = true;
}



void get_max_element(void){
  tuple<uns, uns64> maxElement = maxHeap.top();
  uns index = get<0>(maxElement);
  uns64 count = get<1>(maxElement);
  cout << "Max Element: Index = " << index << ", Count = " << count << endl;
}


void display_max_heap_elements(void){
  while (!maxHeap.empty()) {
    tuple<uns, uns64> maxElement = maxHeap.top();
    uns index = get<0>(maxElement);
    uns64 count = get<1>(maxElement);
    cout << "Heap Element: Index = " << index << ", Count = " << count << endl;
    maxHeap.pop();
  }
}


/*
void determine_ordering(void) {
  uns s_count[MAX_FILL+1];
  uns ii;
  uns64 max_balls = 0;
  uns64 min_balls_1 = 100000000;
  for(ii=0; ii<= MAX_FILL; ii++){
    s_count[ii]=0;
  }

  for(ii=0; ii< NUM_BUCKETS; ii++){
    s_count[bucket[ii]]++;
  }

  for(ii=0; ii<= MAX_FILL; ii++) {
    if (s_count[ii] == 0) {
	continue;
    }
    else{	
	if(max_balls < s_count[ii]) {
	  max_balls = s_count[ii]; 
	  max_buck = ii;
	}
        if(min_balls_1 > s_count[ii]) {
	  min_balls_1 =  s_count[ii];  
	  min_buck = ii;
	}

    	//printf("max:  %u\n",s_count[ii]);
    }
  }
   printf("max:  %d\n",max_buck);
   printf("min:  %d\n",min_buck);

} 

*/
/*
void determine_ordering(void) {
  //uns64 max_balls = 0;
  uns64 num_balls = 0;
  //uns64 min_balls_1 = 100000000; make these global
  for(int ii=0; ii<NUM_BUCKETS; ii++){
    num_balls = bucket[ii];
    //printf("num_balls:  %llu\n",num_balls);
    if (num_balls > max_balls) {
       max_balls = num_balls;
       max_buck = ii;
    }
    if (num_balls < min_balls_1) { //possibly elif?
       min_balls_1 = num_balls;
       min_buck = ii; 
    }
    //printf("max:  %llu\n",max_balls);
    //printf("min:  %llu\n",min_balls_1);
  }
   printf("max:  %d\n",max_buck);
   printf("min:  %d\n",min_buck);
}


*/

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

 // printf("Res: %u\n", res);
 //determine_ordering();

  return res;
}


///////////////////////////////////////////////////////////
//use a max heap to keep track of element that is most full
//preemptively redistrubute to less used bucket
// possibly use a min heap to do this or incurr the cost of lookup
// ////////////////////////////////////////////////
//
// in second thought: just determine ordering order by search? terrible performance tho :(











/*
void determine_ordering(void) {
  //uns64 max_balls = 0;
  uns64 num_balls = 0;
  //uns64 min_balls_1 = 100000000; make these global
  for(int ii=0; ii<NUM_BUCKETS; ii++){
    num_balls = bucket[ii];
    if (num_balls > max_balls) {
       max_balls = num_balls;
    }
    if (num_balls < min_balls_1) { //possibly elif?
       min_balls_1 = num_balls; 
    }
  }
}
*/


/*
void display_min_max(void){
   printf("max:  %llu\n",max_balls);
   printf("min:  %llu\n",min_balls_1);
}

*/



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
	
  printf("config set\n");  
  uns64 ii;
  mtrand->seed(myseed);

  //Initialize Buckets
  //
  printf("before init\n");
  init_buckets();
  printf("done init\n");
  //Ensure Total Balls in Buckets is Conserved.
  sanity_check();
  printf("init heap\n");
  init_heap();

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
    }    
    //Ensure Total Balls in Buckets is Conserved.
    sanity_check();
    get_max_element();
    //Print count of Balls Thrown.
    printf(" %llu\n",bn_i+1);fflush(stdout);    
  }
  display_max_heap_elements();
  

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
