/* ident: libjitcc.h */

#ifndef   JITCC_H
#define   JITCC_H


#define   _GNU_SOURCE

#include  <sys/mman.h>

#ifndef   JITCC_API
#define   JITCC_API
#endif

#define   JITCC_MEM   1    /**  output will be run in memory  **/
#define   JITCC_DLL   3    /**  shared (dynamic) library [ DEFAULT ]  **/
#define   JITCC_OBJ   4    /**  object file  **/

 JITCC_API  int jitcc ( const char *   /* inputfile  */  ,
                        const char *   /* outputfile */  ,
                              FILE *   /* dbgfh      */  );


#endif   /**  JITCC_H  **/

