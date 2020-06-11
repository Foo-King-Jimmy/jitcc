#!/usr/local/bin/tcc -run  -L. -ljitcc_1
   // works:  #!/usr/local/bin/tcc -run  ./libjitcc_1.so
   // works:  #!/usr/local/bin/tcc -run  -L. -ljitcc_1

#include  <stdio.h>
#include  <stdlib.h>
#include  <string.h>
#include  <unistd.h>

#include  "./x24/jitcc.h"

int
Main( int argc, char **argv ) {

 int rv;

// inp str outp str, fil*dbg

  rv = jitcc( NULL, NULL, NULL );
  printf( "\n RV: %d\n", rv );


JJx  // a deliberate error, comment it out to test if C file is flawless


/*
  if     ( -1 == rv ) printf( "\n-1\n" );
  if else( -2 == rv ) printf( "\n-2 warning\n" );
  if else(  0 <= rv ) {
  }
*/


 return 0;
}

