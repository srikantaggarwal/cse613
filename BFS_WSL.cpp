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
This is a parallel Breadth First Search (BFS) Program that uses randomized work-stealing and lock and atomic instruction free mechanism for dynamic load-balancing. It takes a directed graph as input and a number of source vertices, and for each source vertex it executes BFS from that source and produces the distance of 
each other vertex in the graph reachable from that source vertex. 
*/

#include<iostream>
#include<algorithm>
#include<cmath>
#include <sys/types.h>
#include <sys/timeb.h>
#include<time.h>
#include<cilk/cilk.h>
#include<cilk/reducer_opadd.h>
#include <malloc.h>

using namespace std;


#ifndef ALN
  #define ALN 64
#endif


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

int plogp;//=48;
int nsteal; //MAX_STEAL_ATTEMPTS

int *seed;  //random seeds for each thread
int *stealing; //flags that indicate the current status of a thread

typedef struct seg{
int index, front, rear;
}segment;

int diameter=0;
struct Graph{	
	int count;
	int *offset;
};

int *adjMat;
Graph *G;

class Q{
public:
	int* q;
	int size;
	int front, rear;


Q(){
	size=QSize;
	front=0;
	rear=0;
	q=NULL;
	q=(int*)malloc(size*sizeof(int));	
//        posix_memalign( ( void ** ) &q, ALN, size * sizeof( int ) ); 
}

void setSize(int s){size=s;}

void extend( void )
{
   size <<= 1;
   q = ( int * ) realloc( q, size * sizeof( int ) );
}

void print(){
	for(int i=front;i<rear;i++) cout<<q[i]<<" ";
    cout<<endl;
}
~Q(){
		q=NULL;

	}
};
Q *Qin, *Qout, *Qs;
segment *S;
volatile int ph2=0;

void Parallel_BFS_Thread(int id, int dis,int *d){
int t=0;
int victim;
int half;
int u, v;
int psize=0;

segment *seg1=&S[id];

Q *Qo = ( Q * ) ( Qout + id );
int *qo = ( Qo->q + Qo->rear );
int *qot = ( Qo->q + Qo->size ); 

Q *Qos = ( Q * ) ( Qs + id );
int *qos = ( Qos->q + Qos->rear );
int *qots = ( Qos->q + Qos->size ); 

int *qi, *f;
Graph *g;

 while(1){
	//do bfs
	    f = &( seg1->front );
        qi = ( int * ) ( Qin[ seg1->index ].q + *f );
	    stealing[ id ] = 0;
   	    while ( u = *qi )
	    {	       
		*qi++ = 0;
		*f++;
		g = ( Graph * ) ( G + u );
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
		//select a random victim
	    stealing[ id ] = 1;
	
        int lseed = seed[ id ];
	    for ( t = 0; t < nsteal; t++ )
        {
		
            lseed = ( 214013 * lseed + 2531011 );    
            victim = ( ( lseed >> 16 ) & 0x7FFF ) % p;  
        	if ( stealing[ victim ] ) continue;
			
			//if(victim==id) continue;
  
        	segment *vseg = &S[ victim ];
  
        	int vi = vseg->index;
        	int vf = vseg->front;
        	int vr = vseg->rear;
  
        	if ( vr > Qin[ vi ].rear ) continue;
  
        	psize = ( vr - vf );
  
        	if ( psize < base ) continue;
  
        	int half = ( psize >> 1 );
  
        	seg1->index = vi;
        	seg1->front = vf + half;
        	seg1->rear = vr;
  
        	vseg->rear = seg1->front;	
  
        	break;		
        				    				
           }	
		
	     seed[ id ] = lseed; 
	     if ( t == nsteal ) break;	  	   	  
        }
	  	
	*qo = 0;        
      	Qo->rear = ( int ) ( qo - Qo->q );

	*qos=0;
	Qos->rear = ( int ) ( qos - Qos->q );	
	
	if ( Qs[ id ].front < Qs[ id ].rear ) ph2 = 1;	
}


/*

You will launch p threads only once after you are done with low-degree vertices, and all of them will continue to run independently. Each thread will scan the Qs's from the beginning one vertex at a time. For each vertex u thread i will only processes entries from index i * s to index min( ( i + 1 ) * s, G.count[ u ] ) - 1 (or something like that) of u's adjacency list, where s = G.count[ u ] / p. You do not need to spawn and sync for each high-degree vertex.

*/

void Parallel_BFS_Thread2(int id, int dis,int *d){

Q *Qo = ( Q * ) ( Qout + id );

int *qo = ( Qo->q + Qo->rear );
int *qot = ( Qo->q + Qo->size );  
int chunk, startQ, endQ;
int u, v;
int *adjS, *adjE;
Q *Q_s = Qs;
Graph *g;

for ( int i = 0; i < p; i++ )
{   
    	int *qi = ( Q_s++ )->q;

	while ( u = *qi++ )
	{
         if ( d[ u ] < i ) continue;
         d[ u ] = i;
         
 	 g = ( Graph * ) ( G + u );
		         
	 int c = g->count;
	 chunk = ceil( ( c * 1.0 ) / p ); 
	 startQ = id * chunk;
	 c -= startQ;
	 endQ = min( chunk, c );
	
         adjS = ( int * ) ( g->offset + startQ );
         adjE = ( int * ) ( adjS + endQ );	
         
      	 while ( adjS < adjE )
      	 {
	  
		        v = *adjS++;
			if ( d[ v ] < n ) continue;
			d[ v ] = dis;
			*qo++ = v;
			if ( qo < qot ) continue;
			int r = Qo->size;	
			Qo->extend( );
			qo = ( Qo->q + r );
			qot = ( Qo->q + Qo->size );	
	 }	  
	}
	

}

*qo = 0;
Qo->rear = ( int ) ( qo - Qo->q );
}


void parallelBFS(int s, int * d){

	nsteal = plogp;
	diameter = 0;

	cilk_for ( int i = 0; i < n + 1; i++ ) d[ i ] = n;

	 d[ s ]=0;
     Qin[ 0 ].q[ 0 ] = s;
	 Qin[ 0 ].rear = 1;
	 Qin[ 0 ].q[ 1 ] = 0;
	
	
	//Find total size of the queue
	tsize=1;
	
	while(tsize>0){
	    diameter++;
		cilk_for(int i=0;i<p;i++)
		{
				S[i].front=Qin[i].front;
				int r=S[i].rear=Qin[i].rear;
				S[i].index=i;	
                Qin[i].q[r]=0;		
			    stealing[ i ] = 1;	
				Qout[i].front=Qout[i].rear=Qs[i].rear=Qs[i].front=0;
              	
		}
        ph2 = 0;
		for(int i=0;i<p-1;i++)
		{
				
				cilk_spawn Parallel_BFS_Thread( i, diameter,d);  
		}
		Parallel_BFS_Thread( p-1,diameter,d);  
		cilk_sync;
		
		if ( ph2 )
		  {
        		for(int i=0;i<p-1;i++)
        		{
        				
        				cilk_spawn Parallel_BFS_Thread2( i, diameter,d);  
        			
        			
        		}
        		Parallel_BFS_Thread2( p-1,diameter,d); 
        		cilk_sync;
        		
        		cilk_for ( int i = 0; i < p; i++ )
        		  {
        		    int *q = Qs[ i ].q;
        		    int u;
        		    
        		    while ( u = *q++ ) d[ u ] = diameter - 1;
        		  }
        		
		  }
				
		Q * temp;
		temp=Qin;
		Qin=Qout;
		Qout=temp;
      
		tsize=0;
		cilk_for (int i=0;i<p;i++)
		{ 
		    
			if ( Qin[i].rear > Qin[i].front ) tsize = 1;
			
		}
	}
}





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

        //p = cilk::current_worker_count( );
	    p = __cilkrts_get_nworkers();
        plogp = -1;
        int t = p;
        while ( t )
          {
            plogp++;
            t >>= 1;
          } 
       plogp *= p;  
	   
        srand ( time(NULL) );
	   // srand(20012712);
        int r;
		cin>>n;
		cin>>m;
		cin>>r;
      //  r=100;	
        G  = new Graph[ n + 1 ];
        int *ofs = new int[ n + 1 ];
        int **edgeList = new int*[ 2 ];
	
	    for ( int i = 0; i < 2; i++ ) edgeList[ i ] = new int[ m ];
	
	    cilk_for ( int i = 0; i < n + 1; i++ ) G[ i ].count = 0;

	for ( int i = 0; i < m; i++ )
    {
	     cin >> edgeList[ 0 ][ i ];
	     G[ edgeList[ 0 ][ i ] ].count++;
	     cin >> edgeList[ 1 ][ i ];
    }

        int exs = ALN / sizeof( int );

        posix_memalign( ( void ** ) &adjMat, ALN, ( m + exs * n + 1 ) * sizeof( int ) ); 
//        adjMat = new int[ m + n + 1 ];

        ofs[ 1 ] = 0;
        G[ 1 ].offset = ( int * ) ( adjMat + ofs[ 1 ] );
	for ( int i = 2; i < n + 1; i++ )
	  {
            ofs[ i ] = ofs[ i - 1 ] + G[ i - 1 ].count + 1; 
            int pad = ( G[ i - 1 ].count + 1 ) % exs;
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
	
	Qout=new Q[p];
	Qs=new Q[p];
	source=new int [r];
	for (int i=0;i<r;i++){
		cin>>source[i];	
	 }
	 
	 int *dist=new int [n+1];
	 Qin=new Q[p];
	 S=new segment[p];

	 seed = new int[p];
	 stealing = new int[p];
     for ( int i = 0; i < p; i++ ) seed[ i ] = rand( );
	 
	//cout<<"Threads,"<<"Time(s),"<<"plogp,"<<"dia,"<<"plogp*dia*p"<<endl; 
	
  //  for(int k=1;k<6;k=k+1)	
	{
	// plogp=k;
	 double start=0, end=0;
	// int dia=0;
	 int zerovtx=0;
	 int flag=0;
	 
   	 for(int i=0;i<r;i++){
     flag=0;	 
	 if(G[source[i]].count>0){
	     
		 start = getMilliCount();
		 parallelBFS(source[i],dist);
		 end=end+getMilliSpan(start);
		// fflush(stdout);
	 }
	 else 
	 {
		zerovtx++; 
		flag=1;
		diameter=1;
	  }
	//  dia+=(diameter-1);
#ifdef DEBUG
	  cout<<diameter-1<<" "; 
	  cout<<computeChecksum(dist, flag, source[i] )<<endl;
#endif
	}
   	cout<<"Threads: "<<p; 	
	printf(" Run time: %f seconds\n", (float)end/1000);
//	cout<<" Steal Attempts before exiting:"<<dia<<endl;;
//	cout<<"Num of disconnected sources: "<<zerovtx<<endl;

	
//	cout<<p<<","<<(float)end/1000<<","<<plogp<<","<<dia<<","<<plogp*dia*p<<endl;
    }

	delete []dist;
		 
     delete []source;
	 delete[]G;
         free( adjMat ); 
//         delete[]adjMat;
	 for (int i=0;i<p;i++){
		free(Qin[i].q);
	}
	 delete []Qin;
	 Qin=NULL;

	delete []seed;
	delete []stealing;
	return 0;
}
