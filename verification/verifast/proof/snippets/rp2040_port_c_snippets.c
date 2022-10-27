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
             stack_p(?pxStack, ?ulStackDepth, pxTopOfStack, ulStackDepth) &*&
             ulStackDepth > 16;
  @*/
//@ ensures stack_p(pxStack, ulStackDepth, pxTopOfStack-16, ulStackDepth-16);
{
    //@ StackType_t* oldTop = pxTopOfStack;
    //@ open stack_p(pxStack, ulStackDepth, pxTopOfStack, ulStackDepth);
    ///@ close stack_p(pxStack, ulStackDepth, pxTopOfStack-1, ulStackDepth-1);
    ///@ getTopOfStack(pxStack, pxTopOfStack-1);
    //@ integers__split(pxStack, ulStackDepth-2);

    /* Simulate the stack frame as it would be created by a context switch
     * interrupt. */
    pxTopOfStack--;                                          /* Offset added to account for the way the MCU uses the stack on entry/exit of interrupts. */
    *pxTopOfStack = portINITIAL_XPSR;                        /* xPSR */
    pxTopOfStack--;
    //@ close integers_(oldTop-1, sizeof(StackType_t), false, 2, _);
    //@ integers__join(pxStack);
    //@ ptr_range<void>(pxCode);
    //@ integers__split(pxStack, ulStackDepth-3);
    *pxTopOfStack = ( StackType_t ) pxCode;                  /* PC */
    //@ close integers_(oldTop-2, sizeof(StackType_t), false, 3, _);
    pxTopOfStack--;
    //@ ptr_range<void>(prvTaskExitError);
    //@ integers__join(pxStack);
    //@ integers__split(pxStack, ulStackDepth-4);
    *pxTopOfStack = ( StackType_t ) portTASK_RETURN_ADDRESS; /* LR */
    //@ close integers_(oldTop-3, sizeof(StackType_t), false, 4, _);
    //@ integers__join(pxStack);
    pxTopOfStack -= 5;                                       /* R12, R3, R2 and R1. */
    //@ ptr_range<void>(pvParameters);
    //@ integers__split(pxStack, ulStackDepth-9);
    *pxTopOfStack = ( StackType_t ) pvParameters;            /* R0 */
    //@ close integers_(oldTop-8, sizeof(StackType_t), false, 9, _);
    //@ integers__join(pxStack);
    pxTopOfStack -= 8;                                       /* R11..R4. */
    //@ close stack_p(pxStack, ulStackDepth, pxTopOfStack, ulStackDepth-16);
    return pxTopOfStack;
}