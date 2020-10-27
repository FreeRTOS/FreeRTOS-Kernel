/*****************************************************************************
 * @file port.h
 * @author Sandro Gantenbein (sandro.gantenbein@pm.me)
 * @brief 
 * @version 0.1
 * @date 2020-10-27
 * 
 * @copyright Copyright (c) 2020
 * 
 *****************************************************************************/

#ifndef FW_BSW_OS_SOURCE_PORTABLE_GCC_TRICORE_PORT_H_
#define FW_BSW_OS_SOURCE_PORTABLE_GCC_TRICORE_PORT_H_

//These definitions seem to be missing within the TC3xx include files
//Compile the project with the "-fdollars-in-identifiers" option!!

#define $FCX 0xFE38
#define $ICR 0xFE2C
#define $PCXI 0xFE00
#define $PSW 0xFE04
#define $SYSCON 0xFE14

extern void vTrapSysCallYield( int iTrapIdentification );

#endif /* FW_BSW_OS_SOURCE_PORTABLE_GCC_TRICORE_PORT_H_ */
