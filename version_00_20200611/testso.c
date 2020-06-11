#!/usr/local/bin/tcc -run  ./jitcc_1.so

// works:  #!/usr/local/bin/tcc -run  ./jitcc_1.so
// works:  #!/usr/local/bin/tcc -run  -L. -ljitcc_1    // if renamed to  'libjitcc_1.so'


#include  <stdio.h>
#include  <stdlib.h>
#include  <string.h>
#include  <unistd.h>

#include  "./jitcc.h"


int
main( int argc, char **argv ) {


 int  rv,
      charc;
 FILE * fh = NULL;


  // fh = fopen( "./debug_output_file.txt", "w+b" );

           // char*inputfilename, char*outfname, FILE*dbgfh/NULL
  rv = jitcc( "./TEST_inputfile.c",  "./zzz.so",   NULL );
//rv = jitcc( "./TEST_inputfile.c",  "./zzz.so",   fh   );

  printf( "\n RV:  %d\n", rv );

  if( rv > -1 ) {
     fh = fdopen( rv, "r+b" );
     if( !fh ) { 
        printf( "\nerr fdopen\n" );
        return -1;
     }
     (void) rewind( fh );  // JJX  ! Important to have this !
     while( EOF != ( charc = fgetc( fh )))  printf( "%c", charc );
  }

 return 0;
}

