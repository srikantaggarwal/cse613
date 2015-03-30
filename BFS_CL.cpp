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
This is a Breadth First Search (BFS) Program that uses centralized queues and lock and atomic instruction free mechanism for dynamic load-balancing. It takes a directed graph as input and a number of source vertices, and for each source vertex it executes BFS from that source and produces the distance of each other vertex in the graph reachable from that source vertex. 

*/

/*
It is possible to produce scalability plot from this code if you compile the program with -DCILKVIEWPLOT, Change MAX_P to number of maximum threads you want to run on.
*/
#include<stdio.h>
#include<string.h>
#include<iostream>
#include<algorithm>
#include<cmath>
#include<cilk/cilk.h>
#include<cilk/reducer_opadd.h>
#include<time.h>
#include <sys/types.h>
#include <sys/timeb.h>



//define CILKVIEWPLOT if you want to get a CILKVIEW scalability plot
#ifdef CILKVIEWPLOT
	#include<cilkview.h>
#endif

//Maximum number of cores you have in your machine
#ifndef MAX_P
	#define MAX_P 16 
#endif

//by default we will sort the edges
#define SORT_EDGES


using namespace std;

//initial Queue size
#define QSize 256

//n = # of vertices, m = # of edges, tsize = total size of the queue
int n, m, r, tsize = 0;
/*
//If we want to get the scalability plot, we need to distribute the edges properly among the threads. These two variables maintain that distribution if CILKVIEWPLOT is on
#ifdef CILKVIEWPLOT
	int adjSizePerThread, *nextAdjSize;
#endif
*/
// queue segment size that changes dynamically
int Qseg;


int minqseg, mintsize, minnseg;

//Array that holds the source vertices
int *source;

//diameter of the graph
int diameter = 0;

//p = Number of threads
int p = MAX_P;


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

QinT = points to the end of the current level queue
QinC = points to the beginning of current non-empty queue

*/
Q *Qin, *Qout, *QinT, *QinC;

// function to extend the size of an output queue if the capacity is full. This function doubles the size queue.
inline void extendQueue( Q *Qu )
{
	Qu->size <<= 1;
	Qu->q = ( int * ) realloc( Qu->q, Qu->size * sizeof( int ) );
}

// This function returns the next queue segment to explore and updates the queue pointers appropriately.
int *nextSegment( void )
{    
	int *q = NULL;

	Q *qin = ( Q * ) ( QinC - 1 );
    
	//check the first non-empty queue 
	while ( ++qin < QinT )
	{
		int f = qin->front;
		int k = qin->rear - f; 

		if ( !k ) continue;

		QinC = qin;

		q = ( int * ) ( qin->q + f );
		//grab next segment of vertices and update the queue pointers accordingly
		
        //decide how much you will be able to grab
		k = min( Qseg, k );

		qin->front = f + k;

		//update total queue size
		tsize -= k;
		
		//Dynamically change queue segment size based on the current queue size
		if ( tsize > mintsize ) Qseg = ( tsize >> minnseg );

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

	        //While you can get a next segment
			while ( ( qi = nextSegment( ) ) != NULL )
			{ 
			    //while there are unexplored vertices in the segment, pick the next vertex from queue
				while ( (u = *qi) )
				{
					*qi++ = 0;  //clear the queue location which helps in avoiding 

					//keep track of how many vertices you have already visited
					#ifdef CILKVIEWPLOT
					k += G.count[ u ];
					if ( k >= adjSizePerThread ) break;          
					#endif

					
					int *adj = G.offset[ u ]; // pointer to the adjacency list of the vertex

					//While the vertex has any neighbour unexplored 
					while ( v = *adj++ ) 
					{
						if ( d[ v ] < n ) continue;

						d[ v ] = l; //set the distance of the vertex
						*qo++ = v;  //enqueue it in the queue

						#ifdef CILKVIEWPLOT
						knext += G.count[ v ];
						#endif

						if ( qo < qot ) continue; //if you have not exceeded the capacity of the queue, just continue, otherwise, extend the queue size

						int rear = Qo->size;	
						extendQueue( Qo );
						qo = ( Qo->q + rear );
						qot = ( Qo->q + Qo->size );			
					}	   
				}
                //If you want a scalability plot and a thread has already explored so many edges, stop the thread now
				#ifdef CILKVIEWPLOT
				if ( k >= adjSizePerThread ) break;          
				#endif
			}

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
    
	//initialize front and read of all queues
	cilk_for ( int i = 0; i < p; i++ )
	Qin[ i ].front = Qin[ i ].rear = 0;

	//insert the source vertex in the first queue
	d[ s ] = 0;
	Qin[ 0 ].q[ 0 ] = s;
	Qin[ 0 ].rear = 1;
	Qin[ 0 ].q[ 1 ] = 0;

	//total size of the queue is 1 at this point
	tsize = 1;
	
	
    //maintains queue size in parallel
	cilk::reducer_opadd< int > rtsize;

	#ifdef CILKVIEWPLOT
	cilk_for ( int i = 0; i < p; i++ ) nextAdjSize[ i ] = 0;
	adjSizePerThread = 1;
	#endif

	//While there is any vertex left in the queue
	
	while ( tsize > 0 )
	{
		QinC = Qin;  //current queue points to the beginning of the queue array
		QinT = Qin + p; // end queue

		diameter++;

		Qseg = max( minqseg, ( tsize >> minnseg ) ); //choose the queue segment size

		for ( int i = 0; i < p - 1; i++ )
			cilk_spawn Parallel_BFS_Thread( d, diameter, i );  //spawn all threads

		Parallel_BFS_Thread( d, diameter, p - 1 );
		cilk_sync; //sync all threads

		//Swap Qin and Qout
		Q *temp;
		temp = Qin;
		Qin = Qout;
		Qout = temp;

		rtsize.set_value( 0 );

		//in parallel compute the current length of the queue
		cilk_for ( int i = 0; i < p; i++ )
		{   
			Qout[ i ].front = Qout[ i ].rear = 0;
			rtsize += ( Qin[ i ].rear - Qin[ i ].front );			
		}				

		tsize = rtsize.get_value( );

		//also compute out of those how many each thread should compute 
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
{  // int nonzero=0;
	cilk::reducer_opadd< unsigned long long > chksum;
	cilk_for ( int i = 1; i < (n+1); i++ ){
		if(flag==1) {
			if(i!=src)
				chksum+=n;	
            // nonzero++;				
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

	
    //get inputs from command line
	char *pv = getParamVal( argc, argv, ( char * ) "-i" ); 
	if ( pv != NULL ) freopen( pv, "r" , stdin ); //name of the input file

	pv = getParamVal( argc, argv, ( char * ) "-o" ); 
	if ( pv != NULL ) freopen( pv, "a" , stdout ); //name for the output file

	#ifdef CILKVIEWPLOT	
	pv = getParamVal( argc, argv, ( char * ) "-p" ); //number of threads
	if ( pv != NULL ) p = atoi( pv );
	else p = MAX_P;
	#else
		p = __cilkrts_get_nworkers();  //number of threads
	#endif

	//three integers giving the number of vertices (n), number of edges (m), and the number of source vertices (r), respectively
	cin>>n;
	cin>>m;
	cin>>r;
    r=100;
	//Allocate memory for the graph
	G.adjMat = new int[ m + n + 1 ];
	G.count  = new int[ n + 1 ];
	G.offset = new int*[ n + 1 ];

	int *ofs = new int[ n + 1 ];
	int **edgeList = new int*[ 2 ];

	for ( int i = 0; i < 2; i++ )
		edgeList[ i ] = new int[ m ];

	cilk_for ( int i = 0; i < n + 1; i++ ) 
		G.count[ i ] = 0;

	//take input from the file and read the edges
	for ( int i = 0; i < m; i++ )
	{
		cin >> edgeList[ 0 ][ i ];
		G.count[ edgeList[ 0 ][ i ] ]++;
		cin >> edgeList[ 1 ][ i ];
	}

    //compute the degree of each vertex, the starting point of adjacency list for each vertex
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
    //sort the edges, end each vertex's adjacency list with a 0 
	for ( int i = 1; i < n + 1; i++ )
	{
		int k = ofs[ i ];
		G.adjMat[ k ] = 0;

		#ifdef SORT_EDGES
		std::sort( G.adjMat + k - G.count[ i ], G.adjMat + k ); // should use a parallel sorting algorithm
		#endif
	}
    //clear memory elements
	for ( int i = 0; i < 2; i++ )
		delete [] edgeList[ i ];

		delete [] edgeList;
		delete [] ofs;

	//source vertices
	source=new int [r];
	for (int i=0;i<r;i++){
		cin>>source[i];
		//source[i] = ( rand( ) % n ) + 1;	
	}

	int *dist=new int [n+1];
	if(dist==NULL) {cout<<"Allocation failed in line 61 for size"<<n<<endl; exit(1);}
	//current level queues
	Qin=new Q[p];
	//next level queues
	Qout=new Q[p];

	//initialize the queue variables and allocate memory for them
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

	int zerovtx=0;
	int flag=0;
	double start=0, end=0;
	
    //minimum queue segment size
	minqseg = 64;
	minnseg = -1;
	int t = p * p;
	while ( t )
	{
		minnseg++;
		t >>= 1;
	} 

	mintsize = minqseg * ( 1L << minnseg );	
	#ifdef CILKVIEWPLOT
	cilk::cilkview cv;     
	cv.start( );
	#endif

	//run parallel BFS for each source
	for(int i=0;i<r;i++){
		flag=0;	 
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
	return 0;
}

