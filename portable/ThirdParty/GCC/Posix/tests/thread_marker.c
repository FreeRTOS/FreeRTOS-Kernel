/* SPDX-License-Identifier: MIT */

/* Include the implementation to exercise its private TLS helpers unchanged.
 * Unused scheduler sections are discarded by the linker. */
#include "../port.c"

static const char * pcScenario;
static void * pvMarker;
static int iAllocations;
static int iFrees;
static int iStores;

extern void * __real_malloc( size_t xSize );
extern void __real_free( void * pvPointer );
extern int __real_pthread_key_create( pthread_key_t * pxKey,
                                      void ( * pxDestructor )( void * ) );
extern int __real_pthread_setspecific( pthread_key_t xKey,
                                       const void * pvValue );

int __wrap_pthread_key_create( pthread_key_t * pxKey,
                               void ( * pxDestructor )( void * ) )
{
    if( ( strcmp( pcScenario, "key_create" ) == 0 ) || ( strcmp( pcScenario, "key_query" ) == 0 ) )
    {
        return EAGAIN;
    }

    return __real_pthread_key_create( pxKey, pxDestructor );
}

void * __wrap_malloc( size_t xSize )
{
    if( xSize == 1 )
    {
        iAllocations++;

        if( strcmp( pcScenario, "allocation" ) == 0 )
        {
            return NULL;
        }

        pvMarker = __real_malloc( xSize );
        return pvMarker;
    }

    return __real_malloc( xSize );
}

void __wrap_free( void * pvPointer )
{
    if( ( pvPointer != NULL ) && ( pvPointer == pvMarker ) )
    {
        iFrees++;
    }

    __real_free( pvPointer );
}

int __wrap_pthread_setspecific( pthread_key_t xKey,
                                const void * pvValue )
{
    iStores++;

    if( strcmp( pcScenario, "setspecific" ) == 0 )
    {
        return ENOMEM;
    }

    return __real_pthread_setspecific( xKey, pvValue );
}

void __wrap_abort( void )
{
    int iPassed = 0;

    if( ( strcmp( pcScenario, "key_create" ) == 0 ) || ( strcmp( pcScenario, "key_query" ) == 0 ) )
    {
        iPassed = ( iAllocations == 0 ) && ( iStores == 0 );
    }
    else if( strcmp( pcScenario, "allocation" ) == 0 )
    {
        iPassed = ( iAllocations == 1 ) && ( iStores == 0 );
    }
    else if( strcmp( pcScenario, "setspecific" ) == 0 )
    {
        iPassed = ( iAllocations == 1 ) && ( iStores == 1 ) && ( iFrees == 1 );
    }

    _Exit( iPassed ? EXIT_SUCCESS : EXIT_FAILURE );
}

static void * prvMarkedThread( void * pvUnused )
{
    ( void ) pvUnused;

    if( prvIsFreeRTOSThread() != pdFALSE )
    {
        return ( void * ) 1;
    }

    prvMarkAsFreeRTOSThread();
    return ( void * ) ( intptr_t ) ( prvIsFreeRTOSThread() != pdTRUE );
}

int main( int argc,
          char ** argv )
{
    pthread_t xThread;
    void * pvResult;

    if( argc != 2 )
    {
        return EXIT_FAILURE;
    }

    pcScenario = argv[ 1 ];

    if( strcmp( pcScenario, "success" ) == 0 )
    {
        if( pthread_create( &xThread, NULL, prvMarkedThread, NULL ) != 0 )
        {
            return EXIT_FAILURE;
        }

        if( pthread_join( xThread, &pvResult ) != 0 )
        {
            return EXIT_FAILURE;
        }

        return ( ( pvResult == NULL ) && ( iAllocations == 1 ) && ( iFrees == 1 ) &&
                 ( prvIsFreeRTOSThread() == pdFALSE ) ) ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    if( strcmp( pcScenario, "key_query" ) == 0 )
    {
        ( void ) prvIsFreeRTOSThread();
    }
    else
    {
        prvMarkAsFreeRTOSThread();
    }

    fprintf( stderr, "Continued after injected %s failure\n", pcScenario );
    return EXIT_FAILURE;
}
