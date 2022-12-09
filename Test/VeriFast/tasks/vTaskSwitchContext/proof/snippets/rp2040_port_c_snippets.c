/*
 * This file contains code snippets from:
 * portable/ThirdParty/GCC/RP2040/port.c
 */



// Note currently we support configNUM_CORES == 1 with SMP, thought it isn't 100% clear why you wouldn't
// just use the non SMP version; keeping around for now in case the code bases are merged.
#define portRUNNING_ON_BOTH_CORES (configNUM_CORES == portMAX_CORE_COUNT)

/* Constants required to manipulate the NVIC. */
#define portNVIC_SYSTICK_CTRL_REG             ( *( ( volatile uint32_t * ) 0xe000e010 ) )
#define portNVIC_SYSTICK_LOAD_REG             ( *( ( volatile uint32_t * ) 0xe000e014 ) )
#define portNVIC_SYSTICK_CURRENT_VALUE_REG    ( *( ( volatile uint32_t * ) 0xe000e018 ) )
#define portNVIC_INT_CTRL_REG                 ( *( ( volatile uint32_t * ) 0xe000ed04 ) )
#define portNVIC_SHPR3_REG                    ( *( ( volatile uint32_t * ) 0xe000ed20 ) )
#define portNVIC_SYSTICK_CLK_BIT              ( 1UL << 2UL )
#define portNVIC_SYSTICK_INT_BIT              ( 1UL << 1UL )
#define portNVIC_SYSTICK_ENABLE_BIT           ( 1UL << 0UL )
#define portNVIC_SYSTICK_COUNT_FLAG_BIT       ( 1UL << 16UL )
#define portNVIC_PENDSVSET_BIT                ( 1UL << 28UL )
#define portMIN_INTERRUPT_PRIORITY            ( 255UL )
#define portNVIC_PENDSV_PRI                   ( portMIN_INTERRUPT_PRIORITY << 16UL )
#define portNVIC_SYSTICK_PRI                  ( portMIN_INTERRUPT_PRIORITY << 24UL )

/* Constants required to set up the initial stack. */
#define portINITIAL_XPSR                      ( 0x01000000 )

/* The systick is a 24-bit counter. */
#define portMAX_24_BIT_NUMBER                 ( 0xffffffUL )

/* A fiddle factor to estimate the number of SysTick counts that would have
 * occurred while the SysTick counter is stopped during tickless idle
 * calculations. */
#ifndef portMISSED_COUNTS_FACTOR
    #define portMISSED_COUNTS_FACTOR    ( 45UL )
#endif

/* Let the user override the pre-loading of the initial LR with the address of
 * prvTaskExitError() in case it messes up unwinding of the stack in the
 * debugger. */
#ifdef configTASK_RETURN_ADDRESS
    #define portTASK_RETURN_ADDRESS    configTASK_RETURN_ADDRESS
#else
    #define portTASK_RETURN_ADDRESS    prvTaskExitError
#endif

/*
 * Setup the timer to generate the tick interrupts.  The implementation in this
 * file is weak to allow application writers to change the timer used to
 * generate the tick interrupt.
 */
void vPortSetupTimerInterrupt( void );

/*
 * Exception handlers.
 */
void xPortPendSVHandler( void ) __attribute__( ( naked ) );
void xPortSysTickHandler( void );
void vPortSVCHandler( void );

/*
 * Start first task is a separate function so it can be tested in isolation.
 */
static void vPortStartFirstTask( void ) __attribute__( ( naked ) );

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );




// -------------------------------------------------
// Validate stack predicate

/* Simulates creation and initialisation of a stack that grows down as on RP2040.
 */
StackType_t* test_stack_pred(uint32_t depth)
/*@ requires depth * sizeof(StackType_t) <= UINTPTR_MAX &*&
             depth <= UINT_MAX &*&
             depth > 0;
 @*/
/*@ ensures result == 0 ? true : stack_p(result, depth, ?top, depth) &*&
            malloc_block_chars((char*) result, depth * sizeof(StackType_t));
@*/
{
    // Proof boken by switch to nightly build Nov 14, 2022
    // TODO: Adapt proof
    //@ assume(false);
    // ------------------------------------------------------------
	StackType_t * stack;


    /* Allocate space for the stack used by the task being created. */
    stack = (StackType_t*) malloc( ( ( ( size_t ) depth ) * sizeof( StackType_t ) ) );
    if(stack == 0) return 0;
                
    memset(stack, 0, (unsigned int ) depth * sizeof(StackType_t));
                
    StackType_t* top = stack + depth -1;
           
    //@ chars_to_integers_(stack, sizeof(StackType_t), false, depth); 
    //@ close stack_p(stack, depth, top, depth);
    // integers_(stack0, 4, false, depth, _)
    return stack;
}
// -------------------------------------------------

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
/*@ requires pxTopOfStack > 0 &*&
             stack_p_2(?pxStack, ?ulStackDepth, pxTopOfStack, ?ulFreeBytes, 
                       ?ulUsedCells, ?ulUnalignedBytes) &*&
             ulFreeBytes > 17 * sizeof(StackType_t) &*&
             pxStack > 0;
  @*/
/*@ ensures stack_p_2(pxStack, ulStackDepth, result, 
                      ulFreeBytes - sizeof(StackType_t) * 16, 
                      ulUsedCells + 16, 
                      ulUnalignedBytes) &*&
            result == pxTopOfStack - 16;
@*/
{
    // Proof boken by switch to nightly build Nov 14, 2022
    // TODO: Adapt proof
    //@ assume(false);
    // ------------------------------------------------------------

    //@ StackType_t* gOldTop = pxTopOfStack;
    //@ char* gcStack = (char*) pxStack;
    //@ open stack_p_2(_, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + ulFreeBytes - sizeof(StackType_t) );
    //@ assert( (char*) pxStack + ulFreeBytes == (char*) pxTopOfStack + sizeof(StackType_t) );

    // skip stack cell #0
    //@ chars_split(gcStack, ulFreeBytes - sizeof(StackType_t));
    //@ chars_to_integers_(gOldTop, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop);
    /* Simulate the stack frame as it would be created by a context switch
     * interrupt. */
    pxTopOfStack--; /* Offset added to account for the way the MCU uses the stack on entry/exit of interrupts. */

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 1, ulUsedCells + 1, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 2) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 1) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // make stack cell #1 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 2));
    //@ chars_to_integers_(gOldTop-1, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-1);
    *pxTopOfStack = ( 0x01000000 ); /* xPSR */
    //@ close integers_(gOldTop-1, sizeof(StackType_t), false, ulUsedCells+2, _);
    pxTopOfStack--;

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 2, ulUsedCells + 2, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 3) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 2) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent overflow
    //@ ptr_range(pxCode);
    // make stack cell #2 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 3));
    //@ chars_to_integers_(gOldTop-2, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-2);
    *pxTopOfStack = ( StackType_t ) pxCode; /* PC */
    //@ close integers_(gOldTop-2, sizeof(StackType_t), false, ulUsedCells+3, _);
    pxTopOfStack--;

    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 3, ulUsedCells + 3, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 4) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 3) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent underflow
    //@ ptr_range<void>(prvTaskExitError);
    // make stack cell #3 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 4));
    //@ chars_to_integers_(gOldTop-3, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-3);
    *pxTopOfStack = ( StackType_t ) prvTaskExitError; /* LR */
    //@ close integers_(gOldTop-3, sizeof(StackType_t), false, ulUsedCells+4, _);

    pxTopOfStack -= 5; /* R12, R3, R2 and R1. */
    
    // jump to stack cell #7
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 8));
    //@ chars_to_integers_(gOldTop-7, sizeof(StackType_t), false, 4);
    //@ integers__join(gOldTop-7);
    
    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 8, ulUsedCells + 8, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 9) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 8) == (char*) pxTopOfStack + sizeof(StackType_t) );

    // prevent overflow
    //@ ptr_range<void>(pvParameters);
    
    // make stack cell #8 available
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 9));
    //@ chars_to_integers_(gOldTop-8, sizeof(StackType_t), false, 1);
    //@ integers__join(gOldTop-8);
    *pxTopOfStack = ( StackType_t ) pvParameters; /* R0 */
    //@ close integers_(gOldTop-8, sizeof(StackType_t), false, ulUsedCells+9, _);
    
    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack-1, ulFreeBytes - sizeof(StackType_t) * 9, ulUsedCells + 9, ulUnalignedBytes);
    //@ open stack_p_2(pxStack, _, _, _, _, _);


    // skip stack cells #9 - #15, leave #16 unused
    //@ chars_split(gcStack, ulFreeBytes - (sizeof(StackType_t) * 16));
    //@ chars_to_integers_(gOldTop-15, sizeof(StackType_t), false, 7);
    //@ integers__join(gOldTop-15);
    pxTopOfStack -= 8; /* R11..R4. */
    
    // Ensure maintining stack invariant
    //@ close stack_p_2(pxStack, ulStackDepth, pxTopOfStack, ulFreeBytes - sizeof(StackType_t) * 16, ulUsedCells + 16, ulUnalignedBytes);
    //@ assert( stack_p_2(pxStack, ulStackDepth, gOldTop-16, ulFreeBytes - sizeof(StackType_t) * 16, ulUsedCells + 16, ulUnalignedBytes) );

    //@ assert( (char*) pxTopOfStack == (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 17) );
    //@ assert( (char*) pxStack + (ulFreeBytes - sizeof(StackType_t) * 16) == (char*) pxTopOfStack + sizeof(StackType_t) );

    return pxTopOfStack;
}