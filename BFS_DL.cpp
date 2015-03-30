/*
LICENSING: Copyright (c) 2013, Jesmin Jahan Tithi and Dr. Rezaul Chowdhury

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

/*
This is a Breadth First Search (BFS) Program that uses de-centralized queue pools and lock and atomic instruction free mechanism for dynamic load-balancing. It takes a directed graph as input and a number of source vertices, and for each source vertex it executes BFS from that source and produces the distance of each other vertex in the graph reachable from that source vertex. 

*/

/*
It is possible to produce scalability plot from this code if you compile the program with -DCILKVIEWPLOT, Change MAX_P to number of maximum threads you want to run on.
*/
#include<iostream>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<algorithm>
#include<cmath>
#include<cilk/reducer_opadd.h>
#include<cilk/cilk.h>
#include<time.h>
#include <sys/types.h>
#include <sys/timeb.h>


#ifdef CILKVIEWPLOT
  #include<cilkview.h>
#endif

#ifndef MAX_P
  #define MAX_P 12 
#endif

#define SORT_EDGES
using namespace std;


#define QSize 1024

//n = # of vertices, m = # of edges, tsize = total size of the queue
int n, m, r, tsize=0;

int *qsize;
int plogp;
unsigned int *seed;

// queue segment sizes that changes dynamically
int *Qseg;
int minqseg;
int mintsize; 
int minnseg;

//Array that holds the source vertices
int *source;

//diameter of the graph
int diameter = 0;

//p = Number of threads
int p = MAX_P;

//number of centralized queues
int numCQ=1;

//If we want to get the scalability plot, we need to distribute the edges properly among the threads. These two variables maintain that distribution if CILKVIEWPLOT is on
#ifdef CILKVIEWPLOT
   int adjSizePerThread, *nextAdjSize;
#endif

int Qrange;

//utility functions to get the timing
int getMilliCount( )
{
	timeb tb;
	ftime( &tb );
	int nCount = tb.millitm + ( tb.time & 0xfffff ) * 1000;
	return nCount;
}

int getMilliSpan( int nTimeStart )
{
	int nSpan = getMilliCount( ) - nTimeStart;
	if ( nSpan < 0 ) nSpan += 0x100000 * 1000;
	return nSpan;
}
//End utility functions to get the timing

//A graph structure that holds the degree of each vertex, adjacency list and offset of stating point of adjacency list of each vertex
struct Graph
{
public:
	int **offset;
	int *adjMat;
	int *count;
};

// A single graph structure that take cares of all edges and vertices 
Graph G;

// A randomly accessible queue structure 
struct Q
{
	public:
		int front, rear, size, dummy1; // queue front, queue rear, queue capacity, dummy to pad the size
		int *q; // array that holds the queue elements
		int dummy2; // added to make it a multiple of ints
};

/*
Qin = array of queues to hold current level vertices
Qout = array to queues to hold next level vertices

QinT = points to the end of the current level centralized queue pool
QinC = points to the beginning of current non-empty centralized queue pool

*/

Q *Qin, *Qout;

Q **QinT, **QinC;
// function to extend the size of an output queue if the capacity is full. This function doubles the size queue.
inline void extendQueue( Q *Qu )
{
	Qu->size <<= 1;
	Qu->q = ( int * ) realloc( Qu->q, Qu->size * sizeof( int ) );
}
// This function returns the next queue segment from the [Qid] centralized queue pool to explore and updates the queue pointers appropriately.
int *nextSegment( int Qid )
{    
     int *q = NULL;

     Q* qT=( Q * ) ( QinT[Qid]);  //pointer to the last queue of this queue pool
     Q *qin = ( Q * ) ( QinC[Qid] - 1 ); //pointer to the current non-empty queue pool
	 
	 
     //check the first non-empty queue 
     while ( ++qin <qT )
       {
         int f = qin->front;
         int k = qin->rear - f; 

         if ( !k ) continue;

		 //grab next segment of vertices and update the queue pointers accordingly
         QinC[Qid] = qin;

         q = ( int * ) ( qin->q + f );

		 //decide how much you will be able to grab
         k = min( Qseg[Qid], k );
		 
         qin->front = f + k;

		 qsize[Qid]-= k;
		 
		 //fix Qseg
		 if ( qsize[Qid] > mintsize ) Qseg[Qid] = ( qsize[Qid] >> minnseg);

         break;
       }
     
     return q;
}



/*Function that actually executes BFS. Each thread executes this function simultaneously to explore some segment of vertices. A thread goes to the centralized queue and picks the next available segment, changes the global queue variables, and the explores that segment of vertices.
*/
void Parallel_BFS_Thread( int *d, int l, int id )
{
    int u, v;
	
	//keep track of how many vertices you have already visited
	
	#ifdef CILKVIEWPLOT
		int k = 0, knext = 0;
	#endif
	
    int *qi; 
    Q *Qo = ( Q * ) ( Qout + id ); //A pointer to its own output queue
    int *qo = ( Qo->q + Qo->rear ); //Rear pointer to the output queue
    int *qot = ( Qo->q + Qo->size ); // pointer to the maximum capacity location. size must be >= 1, and rear < size    
	int numTrial=0;

	//seed for generating random number to choose random victim
    uint lseed = seed[ id ];
	int myQ ;
	
	//if you have not tried plogp times to get a non-empty centralized queue
	
    while(numTrial++<plogp){
    
		lseed = ( 214013 * lseed + 2531011 );    
		myQ = ( ( lseed >> 16 ) & 0x7FFF ) % numCQ;  
		
		//while there is still some non-empty segment left in the queue
		while ( ( qi = nextSegment( myQ) ) != NULL )
		{ 
			//while there are unexplored vertices in the segment, pick the next vertex from queue
			while ( (u = *qi) )
			{
				*qi++ = 0; //clear the queue location which helps in avoiding 
              
			    //keep track of how many vertices you have already visited
				#ifdef CILKVIEWPLOT
				k += G.count[ u ];
				if ( k >= adjSizePerThread ) break;          
				#endif
				
				
				int *adj = G.offset[ u ];  // pointer to the adjacency list of the vertex
				while ( v = *adj++ ) //While the vertex has any neighbour unexplored 
				{
					if ( d[ v ] < n ) continue;
					d[ v ] = l; //set the distance of the vertex
					*qo++ = v;  //enqueue it in the queue

					
					#ifdef CILKVIEWPLOT
					knext += G.count[ v ];
					#endif
					
					//if you have not exceeded the capacity of the queue, just continue, otherwise, extend the queue size
					if ( qo < qot ) continue;
					int rear = Qo->size;	
					extendQueue( Qo );
					
					//Fix the read pointer of the output queue
					qo = ( Qo->q + rear );
					qot = ( Qo->q + Qo->size );			
				}	   
			}
            
			//if you have not exceeded the capacity of the queue, just continue, otherwise, extend the queue size
			#ifdef CILKVIEWPLOT
			   if ( k >= adjSizePerThread ) break;          
			#endif
		}
    } 
	seed[ id ] = lseed;  //update seed to keep it random
	#ifdef CILKVIEWPLOT
		nextAdjSize[ id ] = knext;          
	#endif
   
    //end the output queue with a zero
    *qo = 0; 
   
    //fix the rear of the queue   
    Qo->rear = ( int ) ( qo - Qo->q );
}

//The main BFS function that initializes the distance array and input output queues and launches all threads to run parallel_BFS_Threads
void parallelBFS( int s, int *d )
{
	diameter = 0;
	//initialize distance array
	cilk_for ( int i = 0; i < n + 1; i++ ) d[ i ] = n;
	
	//initialize front and rear of all queues
	cilk_for ( int i = 0; i < p; i++ )
	{ 
		Qin[ i ].front = Qin[ i ].rear = 0;
		
	}
	
	//insert the source vertex in the first queue and set its distance to 0
	d[ s ] = 0;
    Qin[ 0 ].q[ 0 ] = s;
    Qin[ 0 ].rear = 1;
	Qin[ 0 ].q[ 1 ] = 0;
    
    //total size of the queue is 1 at this point	
	qsize[0]=tsize= 1;
	Q *temp;

	#ifdef CILKVIEWPLOT
	cilk_for ( int i = 0; i < p; i++ ) nextAdjSize[ i ] = 0;
	adjSizePerThread = 1;
	#endif
	
	while ( tsize > 0 )
	{
        diameter++;
		
		
		QinC[0] = (Qin);  //starting point of current centralized queue
		QinT[0] = (QinC[0]+Qrange); //ending point of the current centralized queue
		int v= qsize[0] >> minnseg ;
		Qseg[0] = max( minqseg, (v) );
		
		//initialize all centralized queue pools
		for(int i=1;i<numCQ;i++){
       // cilk_for(int i=0;i<numCQ;i++){	//seems to be slower!!	
			QinC[i] = QinT[i-1]; 
			QinT[i] = (QinC[i]+Qrange);
			v=qsize[i] >> minnseg;
			Qseg[i] = max( minqseg, ( v ) );
		}
        
		//spawn all threads to work to explore the vertices 
		for ( int i = 0; i < p - 1; i++ )
			cilk_spawn Parallel_BFS_Thread( d, diameter, i );  
		
		Parallel_BFS_Thread( d, diameter, p - 1 );
		cilk_sync; //sync all threads after finishing of current BFS level
		
		
		//swap input and output queues (current and next level queues)
		temp = Qin;
		Qin = Qout;
		Qout = temp;
        tsize=0;
		
		//compute the current size of the input queues
		for ( int i = 0; i < p; i++ )
		{   
            Qout[ i ].front = Qout[ i ].rear = 0;
			int x=Qin[ i ].rear - Qin[ i ].front;
		    qsize[i/Qrange]+=x ;
            if(x>0) tsize=1;			
		}				
        //If you want a scalability plot, compute how much each of the thread should explore
		#ifdef CILKVIEWPLOT
        cilk::reducer_opadd< int > adjSize;
        adjSize.set_value( 0 );
		cilk_for ( int i = 0; i < p; i++ )
		{   
		    adjSize += nextAdjSize[ i ];	
            nextAdjSize[ i ] = 0;
		}				

		adjSizePerThread = ( int ) ceil( ( 1.0 * adjSize.get_value( ) ) / p );
		#endif
	}	
}

//function to check the  sanity of the result
unsigned long long computeChecksum( int *d, int flag, int src )
{
    cilk::reducer_opadd< unsigned long long > chksum;
    cilk_for ( int i = 1; i < (n+1); i++ ){
	    if(flag==1) {
		 if(i!=src)
			chksum+=n;		
		}
		else chksum += d[ i ];
	}
	return chksum.get_value();
}


//function to get the parameter value from command prompt
char *getParamVal( int argc, char **argv, char *param )
{
  for ( int i = 1; i < argc - 1; i++ )
    if ( !strcasecmp( argv[ i ], param ) ) return argv[ i + 1 ];

  return NULL;
}



int main( int argc, char **argv ){



        char *pv = getParamVal( argc, argv, ( char * ) "-i" );  //name of the input file
        if ( pv != NULL ) freopen( pv, "r" , stdin );

        pv = getParamVal( argc, argv, ( char * ) "-o" );  //name for the output file
        if ( pv != NULL ) freopen( pv, "w" , stdout );

		#ifdef CILKVIEWPLOT	
        pv = getParamVal( argc, argv, ( char * ) "-p" );  //number of threads
        if ( pv != NULL ) p = atoi( pv );
        else p = MAX_P;
		#else
        p = __cilkrts_get_nworkers(); //number of threads = maximum number threads
		#endif
       
	   
	   
		pv = getParamVal( argc, argv, ( char * ) "-numCQ" );  //number of centralized queues
		if(pv!=NULL) numCQ=atoi(pv);

		//compute the value of numCQ log numCQ in plogp 
		plogp = -1;  
		int t = numCQ;
        while ( t )
        {
            plogp++;
            t >>= 1;
        } 
        
		plogp *= numCQ;  
		
		// I changed plogp value to make it more efficient. It should be changed based on the necessity		
		if (numCQ==1) 
			plogp=1;
		else 
			if(plogp< 24) plogp=24;
		
		//initialize the random number generator
		srand ( time(NULL) );
	   
	   //three integers giving the number of vertices (n), number of edges (m), and the number of source vertices (r), respectively
	   cin>>n; //#vertices
	   cin>>m;  //#edges
	   cin>>r;
    	
	   r=100;
	   
	   //Allocate memory for graph
       G.adjMat = new int[ m + n + 1 ]; //adj list
       G.count  = new int[ n + 1 ];     //Degree
       G.offset = new int*[ n + 1 ];    //starting point of vertex i's adjacency list

       int *ofs = new int[ n + 1 ];
	   int **edgeList = new int*[ 2 ];  //edges
	
	   for ( int i = 0; i < 2; i++ )
			edgeList[ i ] = new int[ m ];
	
	    //initialize the degree of the vertices
	    cilk_for ( int i = 0; i < n + 1; i++ ) 
			G.count[ i ] = 0;
        
		//initialize the graph and construct it
		for ( int i = 0; i < m; i++ )
		{
			cin >> edgeList[ 0 ][ i ];
			G.count[ edgeList[ 0 ][ i ] ]++;
			cin >> edgeList[ 1 ][ i ];
		}
 
        //ofs array works as a prefix sum array and holds the stating of adjacency list for vertex i
        ofs[ 1 ] = 0;
        G.offset[ 1 ] = ( int * ) ( G.adjMat + ofs[ 1 ] );
		for ( int i = 2; i < n + 1; i++ )
		{
            ofs[ i ] = ofs[ i - 1 ] + G.count[ i - 1 ] + 1; 
            G.offset[ i ] = ( int * ) ( G.adjMat + ofs[ i ] ); 
		}  
		
		for ( int i = 0; i < m; i++ )
		{
             int j = edgeList[ 0 ][ i ];
             int k = ofs[ j ];
             G.adjMat[ k ] = edgeList[ 1 ][ i ];
             ofs[ j ] = k + 1;
		}
		//add a 0 at the end of each adjacency list as an end marker
		for ( int i = 1; i < n + 1; i++ )
        {
             int k = ofs[ i ];
             G.adjMat[ k ] = 0;
			 
			 //sort the edges to make the access pattern cache efficient
			 #ifdef SORT_EDGES
             std::sort( G.adjMat + k - G.count[ i ], G.adjMat + k ); // should use a parallel sorting algorithm
             #endif
	    }
    
	    //free memory
		for (int i = 0; i < 2; i++ )
			delete [] edgeList[ i ];
		delete [] edgeList;
	    delete [] ofs;
	    
		//take the source vertices as input
		source=new int [r];
		for (int i=0;i<r;i++){
			cin>>source[i];
		}
	    
		//allocate the distance array
		int *dist=new int [n+1];
		if(dist==NULL) {cout<<"Allocation failed in line 61 for size"<<n<<endl; exit(1);}
	
	    //allocate input and output queues
		Qin=new Q[p];
		Qout=new Q[p];

		//initialize the queue variables
		cilk_for ( int i = 0; i < p; i++ )
		{
			Qin[ i ].size = QSize;
			Qin[ i ].front = Qin[ i ].rear = 0;
			Qin[ i ].q = ( int * ) malloc( Qin[ i ].size * sizeof( int ) );

			Qout[ i ].size = QSize;
			Qout[ i ].front = Qout[ i ].rear = 0;
			Qout[ i ].q = ( int * ) malloc( Qout[ i ].size * sizeof( int ) );
		}
         
		#ifdef CILKVIEWPLOT
		nextAdjSize = new int[ p ];
		#endif

		int zerovtx=0; //number of zero degree vertex
		int flag=0;
		
		//Initialize the random seeds for each thread  
		seed = new unsigned int[p];
		for ( int i = 0; i < p; i++ ) seed[ i ] = rand( );
	 
	 
		double start=0, end=0;
		int minQseg = 64; //minimum queue segment
		int minNseg = -1;
		t = p * p;
		while ( t )
		{
			minNseg++;
			t >>= 1;
		} 
     
		int minTsize = minQseg * ( 1L << minNseg );
	 
	 
		qsize=new int[numCQ];
		memset(qsize, 0, sizeof(int)*numCQ);
	
		Qseg=new int[numCQ];
		minqseg=minQseg;
		minnseg=minNseg;
		mintsize=minTsize;
	 
		
     
		QinT=new Q*[numCQ];
		QinC=new Q*[numCQ];
		Qrange=p/numCQ; //each centralize queue pool contains p/numCQ queues

		#ifdef CILKVIEWPLOT
		cilk::cilkview cv;     
		cv.start( );
		#endif
   	 
	    //run BFS for all source vertex one by one
		for(int i=0;i<r;i++){
			flag=0;
			cilk_for(int j = 0; j < numCQ; j++ ) qsize[j]=0;		 
			if(G.count[source[i]]>0){
			#ifndef CILKVIEWPLOT
			start = getMilliCount();
			#endif
			parallelBFS(source[i],dist);
			#ifndef CILKVIEWPLOT
			end=end+getMilliSpan(start);
			#endif
		}
		else 
		{
			zerovtx++; 
			flag=1;
			diameter=1;
		}
		#ifdef DEBUG
		 cout<<diameter-1<<" "; 
		 cout<<computeChecksum(dist, flag, source[i] )<<endl;
		#endif
	}

	#ifdef CILKVIEWPLOT
    cv.stop( );
	cv.dump( argv[ 0 ] );
	#endif

	
	cout<<"Threads "<<p;
	printf(" Run time: %f seconds\n", (float)end/1000);
	cout<<"Num of disconnected sources: "<<zerovtx<<endl;
	delete []dist;
	#ifdef CILKVIEWPLOT
	delete []nextAdjSize;	 
	#endif
    delete []source;
	delete[]G.count;
	delete[]G.adjMat;
 	delete[]G.offset;
	for (int i=0;i<p;i++){
		free(Qin[i].q);
		free(Qout[i].q);
	}
	delete []Qin;
	delete []Qout;
	 
	delete [] qsize;
	delete [] seed;
	return 0;
}
