 ; main
 ; 
 ; Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 ;
 ; SPDX-License-Identifier: MIT
 ;
 ; Permission is hereby granted, free of charge, to any person obtaining a copy of
 ; this software and associated documentation files (the "Software"), to deal in
 ; the Software without restriction, including without limitation the rights to
 ; use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 ; the Software, and to permit persons to whom the Software is furnished to do so,
 ; subject to the following conditions:
 ;
 ; The above copyright notice and this permission notice shall be included in all
 ; copies or substantial portions of the Software.
 ;
 ; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 ; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 ; FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 ; COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 ; IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 ; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ;

global start
global mboot_info
global pml4
global pud
global wakeup
global hypercall_page
global shared_info
extern long_mode_start
global grant_table
global argo_ring
global rdtsc_low
global rdtsc_high

section .text
bits 32
start:
	mov esp, stack_top
	rdtsc
	mov [rdtsc_low], eax
        mov [rdtsc_high], edx
        mov [mboot_info], ebx
	call setup_page_tables
	call enable_paging

	lgdt [Gdt64KernelPtr]
	jmp 8:long_mode_start

	hlt

setup_page_tables:
        lea eax, [pud]              ; Load the address of pud into eax
        mov edx, 0x0                ; Upper 32-bits of the address (since we're in 32-bit mode, this is 0)
        or eax, 0x3                 ; OR the lower 32-bits of the address with 0x3
        mov [pml4], eax             ; Store the lower 32-bits in pml4[0] (low)
        mov [pml4+4], edx           ; Store the upper 32-bits in pml4[0] (high, which is 0)

        ; Set pud[0] = 0x0000000083 (64-bit value, split into two 32-bit parts)
        mov eax, 0x83               ; Load the lower 32-bits of 0x0000000083 into eax
        mov edx, 0x0                ; Upper 32-bits of the value (0x00000000)
        mov [pud], eax              ; Store the lower 32-bits in pud[0] (low)
        mov [pud+4], edx            ; Store the upper 32-bits in pud[0] (high)
        ret


enable_paging:
	; pass page table location to cpu
	mov eax, pml4
	mov cr3, eax

	; enable PAE
	mov eax, cr4
	or eax, 1 << 5
	mov cr4, eax

	; enable long mode
	mov ecx, 0xC0000080
	rdmsr
	or eax, 1 << 8
	wrmsr

	; enable paging
	mov eax, cr0
	or eax, 1 << 31
	mov cr0, eax
        mov eax, cr0

	ret

section .bss
align 4096
hypercall_page:
    resb 4096
shared_info:
    resb 4096
grant_table:
    resb 4096 * 2
argo_ring:
    resb 4096 * 5

section .bss
align 4096
pml4:
	resb 4096
pud:
	resb 4096*512
stack_bottom:
	resb 16384 * 4
stack_top:

section .rodata
Gdt64Kernel:
    dq 0
    dq 0x0020980000000000

Gdt64KernelLen: equ $-Gdt64Kernel

Gdt64KernelPtr: dw Gdt64KernelLen-1
          dd Gdt64Kernel

extern main
extern serial_send
extern init_serial
extern mboot_info

section .data
mboot_info:
        dd 0
rdtsc_low: 
        dd 0
rdtsc_high:
        dd 0
global Tss

Gdt64:
    dq 0
    dq 0x0020980000000000
    dq 0x0020920000000000
    dq 0x0020f80000000000
    dq 0x0000f20000000000

TssDesc:
    dw TssLen-1
    dw 0
    db 0
    db 0x89
    db 0
    db 0
    dq 0

Gdt64Len: equ $-Gdt64

Gdt64Ptr: dw Gdt64Len-1
          dq Gdt64

Tss:
    dd 0
    dq 0xffff800000190000
    times 88 db 0
    dd TssLen

TssLen: equ $-Tss

section .text
bits 64
long_mode_start:

    ; Load 64-bit GDT Descriptor in Global Descriptor Table Register
    mov rax,Gdt64Ptr
    lgdt [rax]

    ; Load TSS address into Tss Descriptor
    mov rax,Tss
    mov rdi,TssDesc
    mov [rdi+2],ax
    shr rax,16
    mov [rdi+4],al
    shr rax,8
    mov [rdi+7],al
    shr rax,8
    mov [rdi+8],eax
    mov ax,0x28

    ; activate Tss
    ltr ax

    ; enable SSE instructions
    mov rax, cr0
    bts rax, 1
    btr rax, 2
    mov cr0, rax
    mov rax, cr4
    bts rax, 9
    bts rax, 10
    mov cr4, rax
    finit

    ; enable avx if available
    mov eax, 1
    cpuid
    bt ecx, 28

    jnc avx_not_supported
avx_supported:
    mov rax, cr4
    bts rax, 18
    mov cr4, rax
    xor ecx, ecx
    xgetbv
    bts rax, 0
    bts rax, 1
    bts rax, 2
    xsetbv
avx_not_supported:

    ; load null into all data segment registers
    mov ax, 0x10
    mov ss, ax
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax

    call init_serial
    cmp word[mboot_info], 0
    je err
    ; load mboot_info in parameter (rdi)
    ; and call main
    mov rdi, 0
    mov edi, [mboot_info]
    call main
    
    hlt

err:
    hlt
    jmp err
