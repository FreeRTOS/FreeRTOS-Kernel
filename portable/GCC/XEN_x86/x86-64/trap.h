/* trap 
 * 
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */


#ifndef _TRAP_H_
#define _TRAP_H_

#include "stdint.h"

#define TRAP_PIC_TIMER          32
#define TRAP_YIELD              33
#define TRAP_HYPERVISOR_EVENT   37
#define TRAP_SPURIOUS           39
#define TRAP_SCI                41
#define TRAP_TIMER              50
#define TRAP_SYSCALL            128

typedef uint64_t (*SYSTEMCALL)(uint64_t *argptr);

struct TSS {
    uint32_t res0;
    uint64_t rsp0;
    uint64_t rsp1;
    uint64_t rsp2;
    uint64_t res1;
    uint64_t ist1;
    uint64_t ist2;
    uint64_t ist3;
    uint64_t ist4;
    uint64_t ist5;
    uint64_t ist6;
    uint64_t ist7;
    uint64_t res2;
    uint16_t res3;
    uint16_t iopb;
} __attribute__((packed));

struct IdtEntry{
    uint16_t low;
    uint16_t selector;
    uint8_t res0;
    uint8_t attr;
    uint16_t mid;
    uint32_t high;
    uint32_t res1;
};

struct IdtPtr {
    uint16_t limit;
    uint64_t addr;
} __attribute__((packed));

struct TrapFrame {
    int64_t r15;
    int64_t r14;
    int64_t r13;
    int64_t r12;
    int64_t r11;
    int64_t r10;
    int64_t r9;
    int64_t r8;
    int64_t rbp;
    int64_t rdi;
    int64_t rsi;
    int64_t rdx;
    int64_t rcx;
    int64_t rbx;
    int64_t rax;
    int64_t trapno;
    int64_t errorcode;
    int64_t rip;
    int64_t cs;
    int64_t rflags;
    int64_t rsp;
    int64_t ss;
};

static inline void eoi(void) {
    *(volatile unsigned int*)0xFEE000B0 = 0x0;
}

void sysint(void);
void vIDTInit(void);
void load_idt(struct IdtPtr *ptr);
unsigned char read_isr(void);
uint64_t read_cr2(void);
void TrapReturn(void);
uint64_t load_cr3();
void send_char_to_cli();
void starttask(void *);

void vector0(void);
void vector1(void);
void vector2(void);
void vector3(void);
void vector4(void);
void vector5(void);
void vector6(void);
void vector7(void);
void vector8(void);
void vector9(void);
void vector10(void);
void vector11(void);
void vector12(void);
void vector13(void);
void vector14(void);
void vector15(void);
void vector16(void);
void vector17(void);
void vector18(void);
void vector19(void);
void vector20(void);
void vector21(void);
void vector22(void);
void vector23(void);
void vector24(void);
void vector25(void);
void vector26(void);
void vector27(void);
void vector28(void);
void vector29(void);
void vector30(void);
void vector31(void);
void vector32(void);
void vector33(void);
void vector34(void);
void vector35(void);
void vector36(void);
void vector37(void);
void vector38(void);
void vector39(void);
void vector40(void);
void vector41(void);
void vector42(void);
void vector43(void);
void vector44(void);
void vector45(void);
void vector46(void);
void vector47(void);
void vector48(void);
void vector49(void);
void vector50(void);
void vector51(void);
void vector52(void);
void vector53(void);
void vector54(void);
void vector55(void);
void vector56(void);
void vector57(void);
void vector58(void);
void vector59(void);
void vector60(void);
void vector61(void);
void vector62(void);
void vector63(void);
void vector64(void);
void vector65(void);
void vector66(void);
void vector67(void);
void vector68(void);
void vector69(void);
void vector70(void);
void vector71(void);
void vector72(void);
void vector73(void);
void vector74(void);
void vector75(void);
void vector76(void);
void vector77(void);
void vector78(void);
void vector79(void);
void vector80(void);
void vector81(void);
void vector82(void);
void vector83(void);
void vector84(void);
void vector85(void);
void vector86(void);
void vector87(void);
void vector88(void);
void vector89(void);
void vector90(void);
void vector91(void);
void vector92(void);
void vector93(void);
void vector94(void);
void vector95(void);
void vector96(void);
void vector97(void);
void vector98(void);
void vector99(void);
void vector100(void);
void vector101(void);
void vector102(void);
void vector103(void);
void vector104(void);
void vector105(void);
void vector106(void);
void vector107(void);
void vector108(void);
void vector109(void);
void vector110(void);
void vector111(void);
void vector112(void);
void vector113(void);
void vector114(void);
void vector115(void);
void vector116(void);
void vector117(void);
void vector118(void);
void vector119(void);
void vector120(void);
void vector121(void);
void vector122(void);
void vector123(void);
void vector124(void);
void vector125(void);
void vector126(void);
void vector127(void);
void vector128(void);
void vector129(void);
void vector130(void);
void vector131(void);
void vector132(void);
void vector133(void);
void vector134(void);
void vector135(void);
void vector136(void);
void vector137(void);
void vector138(void);
void vector139(void);
void vector140(void);
void vector141(void);
void vector142(void);
void vector143(void);
void vector144(void);
void vector145(void);
void vector146(void);
void vector147(void);
void vector148(void);
void vector149(void);
void vector150(void);
void vector151(void);
void vector152(void);
void vector153(void);
void vector154(void);
void vector155(void);
void vector156(void);
void vector157(void);
void vector158(void);
void vector159(void);
void vector160(void);
void vector161(void);
void vector162(void);
void vector163(void);
void vector164(void);
void vector165(void);
void vector166(void);
void vector167(void);
void vector168(void);
void vector169(void);
void vector170(void);
void vector171(void);
void vector172(void);
void vector173(void);
void vector174(void);
void vector175(void);
void vector176(void);
void vector177(void);
void vector178(void);
void vector179(void);
void vector180(void);
void vector181(void);
void vector182(void);
void vector183(void);
void vector184(void);
void vector185(void);
void vector186(void);
void vector187(void);
void vector188(void);
void vector189(void);
void vector190(void);
void vector191(void);
void vector192(void);
void vector193(void);
void vector194(void);
void vector195(void);
void vector196(void);
void vector197(void);
void vector198(void);
void vector199(void);
void vector200(void);
void vector201(void);
void vector202(void);
void vector203(void);
void vector204(void);
void vector205(void);
void vector206(void);
void vector207(void);
void vector208(void);
void vector209(void);
void vector210(void);
void vector211(void);
void vector212(void);
void vector213(void);
void vector214(void);
void vector215(void);
void vector216(void);
void vector217(void);
void vector218(void);
void vector219(void);
void vector220(void);
void vector221(void);
void vector222(void);
void vector223(void);
void vector224(void);
void vector225(void);
void vector226(void);
void vector227(void);
void vector228(void);
void vector229(void);
void vector230(void);
void vector231(void);
void vector232(void);
void vector233(void);
void vector234(void);
void vector235(void);
void vector236(void);
void vector237(void);
void vector238(void);
void vector239(void);
void vector240(void);
void vector241(void);
void vector242(void);
void vector243(void);
void vector244(void);
void vector245(void);
void vector246(void);
void vector247(void);
void vector248(void);
void vector249(void);
void vector250(void);
void vector251(void);
void vector252(void);
void vector253(void);
void vector254(void);
void vector255(void);

#endif
