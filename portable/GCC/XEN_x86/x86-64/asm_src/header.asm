 ; header
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

MB2_ARCH  EQU 0                                 ; 0 = x86/x86-64
MB2_LEN   EQU (mbend-mbhead)
MB2_MAGIC EQU 0xe85250d6

section .multiboot_header align=4096
mbhead:
        dd MB2_MAGIC                            ; Multiboot2 magic number
        dd MB2_ARCH                             ; Architecture
        dd MB2_LEN                              ; Multiboot header length
        dd 0x100000000 - MB2_LEN - MB2_ARCH - MB2_MAGIC
                                                ; Checksum

mb2_tag_info_start:
        dw 1                                    ; multiboot information request
        dw 0
        dd mb2_tag_info_end - mb2_tag_info_start
        dd 1
        dd 2
        dd 6
mb2_tag_info_end:

        align 8
mb2_tag_end_start:
        dw 0                                    ; last tag
        dw 0
        dd mb2_tag_end_end - mb2_tag_end_start
mb2_tag_end_end:

mbend:
