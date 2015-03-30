/*
LICENSING: Copyright (c) 2013, Jesmin Jahan Tithi and Dr. Rezaul Chowdhury

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, 
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

/*
This is a parallel recursive divide and conquer based Breadth First Search (BFS) Program that uses randomized work-stealing and lock and atomic instruction free mechanism for dynamic load-balancing. 
It takes a directed graph as input and a number of source vertices, and for each source vertex it executes BFS from that source and produces the distance of 
each other vertex in the graph reachable from that source vertex. 

*/

#include<iostream>
#include<algorithm>
#include<cmath>
#include<cilk/reducer_opadd.h>
#include<sys/types.h>
#include<sys/timeb.h>
#include<time.h>
#include<cilk/cilk.h>
#include<offload.h>

#include <malloc.h>

using namespace std;


//Align edges to 64 bit boundary for making them cache efficient 
#ifndef ALN
  #define ALN 64
#endif

//sort edges turned on by default
#define SORT_EDGES
#define QSize 2048  //Initial queue capacity
#define base 64    //Threshold after which there will be no more division
#define threshold 750 //Threshold that defines a high degree vertex


int p;  //Number of threads
int n,m; //Number of vertices and edges
volatile int tsize=0; //total size of the queue

int *dist; //distance array
int *source; //source array


int diameter=0; // 


//Graph structure 
struct Graph{	
	int count; //degree
	int *offset; //adjacency list starting point in the adjMat array
};


int *adjMat; // adjacency list
Graph *G;    // The graph 

//Queue structure
class Q{
	public:
	  int* q; //actual queue
      int size; //capacity
      int front, rear; //front and rear position


	//default queue constructor
	Q(){
		size=QSize;
		front=0;
		rear=0;
		q=NULL;
		q=(int*)malloc(size*sizeof(int));	
	}

	//set size of the 
	void setSize(int s){size=s;}

	//extend the queue
	void extend( void )
	{
		size <<= 1;
		q = ( int * ) realloc( q, size * sizeof( int ) );
	}
	//print the queue content. For debug purpose only
	void print(){
		for(int i=front;i<rear;i++) cout<<q[i]<<" ";
		cout<<endl;
	}
	//destructor
	~Q()
	{
		q=NULL;
	}
};
//Arrays for input and output queues and queues that hold high degree vertices
Q *Qin, *Qout, *Qs;

//keeps track of whether you need to go to phase2= whether you have any high degree vertex to explore
volatile int ph2=0;

/*
Function that mainly executes BFS. Each thread starts exploring vertices from its own queue. 
Once its own queue becomes empty, it will try at most plogp times to pick a random victim thread and try to steal a segment from it and explore vertices from it. 
It will try to do so as long as there is some unvisited vertex in the queue.
*/
void Parallel_BFS_Thread(int dis, int *d, int qid, int s_id, int e_id){
	int u, v;
	if(e_id<=s_id) return; //if you got an invalid segement, return
	int id=__cilkrts_get_worker_number(); //return the id of the current thread
	
    //qid denotes the input queue
	//id denotes the output queue

	Q *Qo = ( Q * ) ( Qout + id ); //threads private output queue
	int *qo = ( Qo->q + Qo->rear ); //rear pointer
	int *qot = ( Qo->q + Qo->size ); 

	Q *Qos = ( Q * ) ( Qs + id ); //Output queue for putting high degree vertices
	int *qos = ( Qos->q + Qos->rear ); //rear pointer
	int *qots = ( Qos->q + Qos->size ); 

	//
	int *qi;
	Graph *g;

	//do bfs
	    //pointer to the input queue
		qi = ( int * ) ( Qin[ qid].q + s_id);
		
		//you have unvisited vertices
		while (s_id<e_id )
		{	       
			//read a vertex from queue
			u = *qi++;
			s_id++;
			
			g = ( Graph * ) ( G + u );
			//if this is a very high degree vertex, put that in Qs for later exploration 
			if ( g->count > threshold ) 
			{
				*qos++ = u;
				d[ u ] = p;   // assumption: p < n

				if ( qos < qots ) continue;
				int r = Qos->size;	
				Qos->extend( );
				qos = ( Qos->q + r );
				qots = ( Qos->q + Qos->size );	
				continue;
			}

			//Otherwise explore the adjacency list of the vertex
			int *adj = g->offset; 
			while ( v = *adj++ ) 
			{
				if ( d[ v ] < n ) continue;
				d[ v ] = dis;
				*qo++ = v;
				if ( qo < qot ) continue;
				int r = Qo->size;	
				Qo->extend( );
				qo = ( Qo->q + r );
				qot = ( Qo->q + Qo->size );			
			}	
		}//end while	 


	*qo = 0;  //end the output queue with a zero      
	Qo->rear = ( int ) ( qo - Qo->q ); //fix the rear for the queue

	*qos=0; //end the output queue with a zero 
	Qos->rear = ( int ) ( qos - Qos->q ); //fix the rear for the queue	

	if ( Qs[ id ].front < Qs[ id ].rear ) ph2 = 1;	//if you have any vertex in Qs, you have to run ph2 for this BFS level

}
/*
It first checks, whether the number of vertices in its queue is more than a threshold. If yes, it splits the queue into two parts and spawns 
another thread to work on one of those parts whereas, it handles the rest.
*/
void Parallel_BFS_ThreadR(int dis,int *d, int qid, int s_id, int e_id)
{
    int currSize=e_id-s_id;
	if((currSize)<=base)
		Parallel_BFS_Thread(dis,d, qid, s_id, e_id);
	else
	{
	  int half=s_id+(currSize>>1);
	  cilk_spawn Parallel_BFS_ThreadR(dis,d, qid, s_id, half);
	  Parallel_BFS_ThreadR(dis,d, qid, half, e_id);
	  cilk_sync;
	}

}

/*

You will launch p threads only once after you are done with low-degree vertices, and all of them will continue to run independently.
Each thread will scan the Qs's from the beginning one vertex at a time. For each vertex u thread i will only processes entries from index 
i * s to index min( ( i + 1 ) * s, G.count[ u ] ) - 1  of u's adjacency list, where s = G.count[ u ] / p. 
You do not need to spawn and sync for each high-degree vertex.

 */
//Exploring high degree vertex by splitting adjacency lists equally among the threads
void Parallel_BFS_Thread2(int id, int dis,int *d){

	Q *Qo = ( Q * ) ( Qout + id ); //Thread's private output queue

	int *qo = ( Qo->q + Qo->rear ); //rear
	int *qot = ( Qo->q + Qo->size );  //capacity
	int chunk, startQ, endQ; //chunk size, start exploration point, end exploration point
	int u, v;
	int *adjS, *adjE; 
	Q *Q_s = Qs;
	Graph *g;

	//for all p queues
	for ( int i = 0; i < p; i++ )
	{   
		
		int *qi = ( Q_s++ )->q;

		//As long as there is some vertex in the queue
		while ( u = *qi++ )
		{
			//we use distance i in this case, the distance will be fixed in size the main BFS function
			if ( d[ u ] < i ) continue;
			d[ u ] = i;

			g = ( Graph * ) ( G + u );

			//divide the adjacency list of the vertex into p chunks
			int c = g->count;
			chunk = ceil( ( c * 1.0 ) / p ); 
			startQ = id * chunk;  //starting position for this thread
			c -= startQ;
			endQ = min( chunk, c ); //ending position for this thread

			adjS = ( int * ) ( g->offset + startQ ); //starting pointer
			adjE = ( int * ) ( adjS + endQ );	     //ending pointer

			//while there are some vertex in the adjacency list, explore them
			while ( adjS < adjE )
			{

				v = *adjS++;
				if ( d[ v ] < n ) continue;
				d[ v ] = dis;
				*qo++ = v;

				//double the queue size if you hit the capacity
				if ( qo < qot ) continue;
				int r = Qo->size;	
				Qo->extend( );
				qo = ( Qo->q + r );
				qot = ( Qo->q + Qo->size );	
			}	  
		}


	}

	*qo = 0; //end the queue with an end marker
	Qo->rear = ( int ) ( qo - Qo->q ); //fix the rear pointer
}

/*
The main BFS function that initializes the distance array and input output queues and launches all threads to run parallel_BFS_Threads
*/
void parallelBFS(int s, int * d){

	
	diameter = 0;
	//initialize distance array
	cilk_for ( int i = 0; i < n + 1; i++ ) d[ i ] = n;

	
	//insert the source vertex in the first queue and set its distance to 0
	d[ s ]=0;
	Qin[ 0 ].q[ 0 ] = s;
	Qin[ 0 ].rear = 1;
	Qin[ 0 ].q[ 1 ] = 0;


	//total size of the queue is 1 at this point
	tsize=1;
	//while there is still any vertex left in the queue

	while(tsize>0){
		diameter++;
		//initialize front and rear of all queues
	
		cilk_for(int i=0;i<p;i++)
		{
						
			Qout[i].front=0;
			Qout[i].rear=0;
			Qs[i].rear=0;
			Qs[i].front=0;
			Qin[i].q[Qin[i].rear]=0;

		}
		//initialize phase 2 = 0
		ph2 = 0;
		
	/*	for(int i=0;i<p-1;i++)
		{
             
			if (Qin[i].rear>Qin[i].front)
				cilk_spawn Parallel_BFS_ThreadR(diameter,d, i, 0, Qin[i].rear);  
		}
		Parallel_BFS_ThreadR( diameter,d, p-1, 0, Qin[p-1].rear);  
		cilk_sync;
		
    */
	//spwan p threads to work on exploring the vertices
	    cilk_for(int i=0;i<p;i++)
		{
             
			if (Qin[i].rear>Qin[i].front)
				Parallel_BFS_ThreadR(diameter,d, i, 0, Qin[i].rear);  
		}
		
	
      //  cout<<"Just in front of ph2: diameter: "<<diameter<<endl;
		//if you have high degree vertex, explore them
		if ( ph2 )
		{
			for(int i=0;i<p-1;i++)
			{

				cilk_spawn Parallel_BFS_Thread2( i, diameter,d);  


			}
			Parallel_BFS_Thread2( p-1,diameter,d); 
			cilk_sync;

			//fix the distances of the high degree vertices
			cilk_for ( int i = 0; i < p; i++ )
			{
				int *q = Qs[ i ].q;
				int u;

				while ( u = *q++ ) d[ u ] = diameter - 1;
			}

		}

		//swap input and output queues (current and next level queues)
		Q * temp;
		temp=Qin;
		Qin=Qout;
		Qout=temp;

		//see whether there is any vertex in the current queue
		tsize=0;
		cilk_for (int i=0;i<p;i++)
		{ 

			if ( Qin[i].rear > Qin[i].front ) tsize = 1;

		}
	}
}




//function to check the sanity of the result
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
//utility functions to get the timing
int getMilliCount(){
	timeb tb;
	ftime(&tb);
	int nCount = tb.millitm + (tb.time & 0xfffff) * 1000;
	return nCount;
}

int getMilliSpan(int nTimeStart){
	int nSpan = getMilliCount() - nTimeStart;
	if(nSpan < 0)
		nSpan += 0x100000 * 1000;
	return nSpan;
}


int main(int argc,char **argv){

	p = __cilkrts_get_nworkers();  //number of threads
  

	//take inputs
	int r;
	cin>>n; //#vertex
	cin>>m; //#edges
	cin>>r; //#sources
//	r=1;	
	
	cout<<"V:"<<n<<"E:"<<m<<endl;
	
	//allocate memory for the graph
	G  = new Graph[ n + 1 ];
	int *ofs = new int[ n + 1 ];
	int **edgeList = new int*[ 2 ];
	for ( int i = 0; i < 2; i++ ) 
	{
		edgeList[ i ] = new int[ m ];
	//	memset(edgeList[ i ], 0, sizeof(int)*m);
	}
	
	cilk_for ( int i = 0; i < n + 1; i++ ) G[ i ].count = 0; //initialize all degrees to zero
	
	//take edges from file and initialize the graph and also compute the degree of each vertex
	for ( int i = 0; i < m; i++ )
	{
		
		cin >> edgeList[ 0 ][ i ];
		cin >> edgeList[ 1 ][ i ];
	
		G[ edgeList[ 0 ][ i ] ].count++;
		
	}
   
	int exs = ALN / sizeof( int );

	//Pad adjMat to be a multiple of ALN factor
	posix_memalign( ( void ** ) &adjMat, ALN, ( m + exs * n + 1 ) * sizeof( int ) ); 
	//adjMat = new int[ m + n + 1 ];


	//find the offset in adjMat for each vertex. offset basically stores the starting position of adjacency list of each vertex i, in the adjacency list.
	ofs[ 1 ] = 0;
	G[ 1 ].offset = ( int * ) ( adjMat + ofs[ 1 ] );
	for ( int i = 2; i < n + 1; i++ )
	{
		ofs[ i ] = ofs[ i - 1 ] + G[ i - 1 ].count + 1; 
		int pad = ( G[ i - 1 ].count + 1 ) % exs; //how much you need to pad to be a multiple of alignment factor
		if ( pad ) ofs[ i ] += ( exs - pad );
		G[ i ].offset = ( int * ) ( adjMat + ofs[ i ] ); 
	}  

	
	for ( int i = 0; i < m; i++ )
	{
		int j = edgeList[ 0 ][ i ];
		int k = ofs[ j ];
		adjMat[ k ] = edgeList[ 1 ][ i ];
		ofs[ j ] = k + 1;
	}

	//end each vertex's adjacency matrix with a 0
	for ( int i = 1; i < n + 1; i++ )
	{
		int k = ofs[ i ];
		adjMat[ k ] = 0;
		#ifdef SORT_EDGES
		std::sort( adjMat + k - G[ i ].count, adjMat + k ); // should use a parallel sorting algorithm
		#endif
	}


	for ( int i = 0; i < 2; i++ )
		delete [] edgeList[ i ];

	delete [] edgeList;
	delete [] ofs;
	
	cout<<"Done Graph Creation!"<<endl;
	source=new int [r];
	
	//Take source vertices as input to run BFS with them
	for (int i=0;i<r;i++){
		cin>>source[i];	
	}

	//allocate distance array
	int *dist=new int [n+1];


	Qin=new Q[p]; //current level queue /input queue
	Qout=new Q[p]; //next level queue /output queue
	Qs=new Q[p];   //queue for storing high degree vetices
    cout<<"------------------------------Starting BFS----------------------"<<endl;
	double start=0, end=0;
	
	int zerovtx=0; //# of zero degree vertex
	int flag=0;    
	//run BFS for all source vertex one by one
	for(int i=0;i<r;i++)
	{
		flag=0;	 
		if(G[source[i]].count>0){
			start = getMilliCount();
			parallelBFS(source[i],dist);
			end=end+getMilliSpan(start);
			fflush(stdout);
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
		
	cout<<p<<","<<(float)end/1000<<endl;

	//free memory
	delete []dist;
	delete []source;
    delete[]G;
	free( adjMat ); 
	for (int i=0;i<p;i++){
		free(Qin[i].q);
	}
	delete []Qin;
	Qin=NULL;
	return 0;
}
