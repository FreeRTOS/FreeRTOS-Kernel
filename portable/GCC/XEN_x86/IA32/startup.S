/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Set to 1 to enable functionality */
#define __SHOW_KERNEL_PARAMS__ 0

/* Local definitions boot loader */
#define MULTIBOOT_SIGNATURE		0x2BADB002
#define MULTIBOOT_BOOTINFO_MMAP		0x00000040

/* Local definitions for GD table */
#define	GDT_ENTRIES			8
#define	GDT_ENTRY_SIZE			8
#define	GDT_BYTES			(GDT_ENTRIES * GDT_ENTRY_SIZE)

 	/* Globals and externs */
	.global _mboot_hdr
	.global _start
	.global _restart

	.extern bootsign
	.extern bootinfo

	.extern __text_start
	.extern __text_end
	.extern __data_vma
	.extern __data_lma
	.extern __data_start
	.extern __data_end
	.extern __bss_start
	.extern __bss_end
	.extern __stack_for_main

	.global __text_start
	.global __text_end
	.global __data_vma
	.global __data_lma
	.global __data_start
	.global __data_end
	.global __bss_start
	.global __bss_end
         .globl shared_info, hypercall_page
	.global grant_table
	.global argo_ring
	.global rdtsc_low
	.global rdtsc_high

	.extern setsegs
	.extern kernel_load_check
	.extern main
	.extern init_serial

 	/* Local constants for multiboot section */
  	.set ALIGN,    	1<<0             	/* align loaded modules on page boundaries */
	.set MEMINFO,  	1<<1             	/* provide memory map */
	.set MAGIC,    	0x1BADB002       	/* 'magic number' lets bootloader find the header */
	.set FLAGS, 	ALIGN|MEMINFO  		/* this is the multiboot 'flag' field */
	.set CHECKSUM, 	-(MAGIC + FLAGS) 	/* checksum of above */

	/* Set-up GDT */
	.section .data

	.align	16
	.globl	gdt
	gdt:	.space	GDT_BYTES
	gdtr:	.word	(GDT_BYTES-1)		/* sizeof _gdt -1 (in bytes) */
	.long	gdt							/* global pointer to the gdt */

	/* Start of application text */
	.section .text.entry

	/* Skip mb header */
	jmp _start

	.align 4
	/* Multiboot header */
	_mboot_hdr:
	.long MAGIC							/* offset = 0 */
	.long FLAGS							/* offset = 4 */
	.long CHECKSUM						/* offset = 8 */
 	.long _mboot_hdr					/* should be header address - offset = 12 */
	.long __text_start					/* load address (start of text) - offset = 16 */
	.long __bss_start					/* load end address (end of data) - offset = 20*/
	.long __bss_end 					/* bss end address - offset = 24*/
	.long _start						/* entry_addr - offset = 28*/

#define ELFNOTE(name, type, desc)           \
    .pushsection .note.name               ; \
    .align 4                              ; \
    .long 2f - 1f       /* namesz */      ; \
    .long 4f - 3f       /* descsz */      ; \
    .long type          /* type   */      ; \
1:.asciz #name          /* name   */      ; \
2:.align 4                                ; \
3:desc                  /* desc   */      ; \
4:.align 4                                ; \
    .popsection

#define XEN_ELFNOTE_PHYS32_ENTRY 18
ELFNOTE(Xen, XEN_ELFNOTE_PHYS32_ENTRY, .long _start)

        /* Unpleasant -- the PTE that maps this page is actually overwritten */
        /* to map the real shared-info page! :-)                             */
        .align 4096
shared_info:
        .fill 4096,1,0

hypercall_page:
        .fill 4096,1,0
grant_table:
	.fill 4096*2,1,0
argo_ring:
	.fill 4096*5,1,0
rdtsc_low:
        .fill 4,1,0
rdtsc_high:
        .fill 4,1,0


	/* Start of executable code */
	_start:

	_restart:

	/* Initialise the stack pointer */
	movl $__stack_for_main, %esp

    /* Reset EFLAGS. */
    pushl $0
    popf

        rdtsc                           # Reads TSC -> %edx:%eax
        movl %eax, rdtsc_low            # Store lower 32 bits
        movl %edx, rdtsc_high           # Store upper 32 bits
 	/* Set up the global descriptor table */
	call	setsegs
	lgdt	gdtr
	ljmp	$0x8, $gdt1					/* CS descriptor 1 */
	gdt1:
	movl	$0x10, %eax					/* DS descriptor 2 */
	movw	%ax, %ds
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movl	$0x18, %eax					/* SS descriptor 3 */
	movw	%ax, %ss

    /* Clear interrupt flag */
	cli

    /* Initialise platform */

    /* Show kernel parameters and call main, or just call main */
	#if (__SHOW_KERNEL_PARAMS__ == 1)
	    /*---------------------------------------------------------------------
	    	On successful OS load EAX should contain 0x2BADB002
	       	EBX should contain the physical address of multiboot info structure

	       	Push the pointers to the multiboot information structure
	       	and the magic number on the stack and check values returned
	    ----------------------------------------------------------------------*/
	    movl	bootsign, %eax
		movl	bootinfo, %ebx
	    pushl   %ebx		/* Multiboot information */
	    pushl   %eax 		/* Magic number */
	    call show_kernel_parameters
	#else
	    /*---------------------------------------------------------------------
	    	Call main() routine
	    ----------------------------------------------------------------------*/
                call  init_serial
	        pushl %ebx		/* Multiboot information */
	 	call  main
    #endif

	/* Should not get here, but just in case - loop forever */
	cli
	_local_loop:
	hlt
	jmp _local_loop

	/*-------------------------------------------------------------------------
	                  GLOBAL ASSEMBLY LANGUAGE ROUTINES
	--------------------------------------------------------------------------*/

 	/* halt */
 	.globl	halt
	halt:
	jmp halt
	ret

	/* inb */
	.globl	inb
	inb:	movl	4(%esp), %edx
	xorl	%eax, %eax	# clr eax
	inb	%dx, %al
	ret

	/* inw */
	.globl	inw
	inw:	movl	4(%esp), %edx
	xorl	%eax, %eax	# clr eax
	inw		%dx, %ax
	ret

	/* inl */
	.globl  inl
	inl:	movl	4(%esp), %edx
	xorl	%eax, %eax
	inl		%dx, %eax
	ret

	/* outb */
	.globl	outb
	outb:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outb	%al, %dx
	ret

	/* outw */
	.globl	outw
	outw:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outw	%ax, %dx
	ret

	/* outl */
	.globl	outl
	outl:	movl	4(%esp), %edx
	movl	8(%esp), %eax
	outl	%eax, %dx
	ret

.end
