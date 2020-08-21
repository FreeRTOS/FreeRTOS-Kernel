#include "FreeRTOSConfig.h"
#include <stdlib.h>

	static  long         brk_siz  =  0;
//	#if  configTOTAL_HEAP_SIZE != 0
	typedef int          _heep_t;
	#define ROUNDUP(s)   (((s)+sizeof(_heep_t)-1)&~(sizeof(_heep_t)-1))
	static  _heep_t      _heep[ROUNDUP(configTOTAL_HEAP_SIZE)/sizeof(_heep_t)];
	#define              _heep_size      ROUNDUP(configTOTAL_HEAP_SIZE)
/*	#else
	extern  char        *_heep;
	extern  long        _heep_size;
	#endif
*/	
	extern  char  *sbrk(int  size)
	{
	   if  (brk_siz  +  size  >  _heep_size  ||  brk_siz  +  size  <  0)

          return((char*)-1);
	   brk_siz  +=  size;
	   return(  (char*)_heep  +  brk_siz  -  size);
	}

