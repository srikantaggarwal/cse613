CC=icpc
CFLAGS=-O3 -Wall -Werror -ansi-alias -ip -opt-subscript-in-range -opt-prefetch=4 -fomit-frame-pointer -funroll-all-loops -restrict -vec-report -parallel -xhost

all: 
	$(CC) $(CFLAGS) -o pbfs_clf BFS_CL.cpp 
	$(CC) $(CFLAGS) -o pbfs_dlf BFS_DL.cpp
	$(CC) $(CFLAGS) -o pbfswsl BFS_WSL.cpp 
	$(CC) $(CFLAGS) -o pbfswsldq BFS_WSLDQ.cpp 

clean:
	rm -f pbfs_dlf pbfs_clf pbfswsl pbfswsldq
	rm -f output-hw*
	rm -f error-hw*
