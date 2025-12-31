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


#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE
#include "trap.h"
#include "io.h"
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "IRQ.h"
#include "ioapic.h"
#include "stdio.h"
#include "hypervisor.h"
#include "time.h"
#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE

void vSystemCall(struct TrapFrame *tf);
void vInitSystemCall(void);
void process_sci(void);
void vFreeAllPages(uint64_t *p);

static struct IdtPtr idt_pointer;
static struct IdtEntry vectors[256];
extern uint64_t pml4;
/* pxCurrentTCB saved by FreeRTOS Kernel */
extern StackType_t *pxCurrentTCB;
/* Tss defined in assembly files */
extern struct TSS Tss;
extern uint32_t ulPortYieldPending;
extern uint32_t ulInterruptNesting;
extern uint32_t xTaskUsesFPU;
extern uint8_t *pucPortTaskFPUContextBuffer;

static void vInstallHandler(struct IdtEntry *entry, uint64_t addr, uint8_t attribute)
{
    entry->low = (uint16_t)addr;
    entry->selector = 8;
    entry->attr = attribute;
    entry->mid = (uint16_t)(addr>>16);
    entry->high = (uint32_t)(addr>>32);
}

void vIDTInit(void)
{
    vInitSystemCall();
    vInstallHandler(&vectors[0],(uint64_t)vector0,0x8eUL);
    vInstallHandler(&vectors[1],(uint64_t)vector1,0x8eUL);
    vInstallHandler(&vectors[2],(uint64_t)vector2,0x8eUL);
    vInstallHandler(&vectors[3],(uint64_t)vector3,0x8eUL);
    vInstallHandler(&vectors[4],(uint64_t)vector4,0x8eUL);
    vInstallHandler(&vectors[5],(uint64_t)vector5,0x8eUL);
    vInstallHandler(&vectors[6],(uint64_t)vector6,0x8eUL);
    vInstallHandler(&vectors[7],(uint64_t)vector7,0x8eUL);
    vInstallHandler(&vectors[8],(uint64_t)vector8,0x8eUL);
    vInstallHandler(&vectors[10],(uint64_t)vector10,0x8eUL);
    vInstallHandler(&vectors[11],(uint64_t)vector11,0x8eUL);
    vInstallHandler(&vectors[12],(uint64_t)vector12,0x8eUL);
    vInstallHandler(&vectors[13],(uint64_t)vector13,0x8eUL);
    vInstallHandler(&vectors[14],(uint64_t)vector14,0x8eUL);
    vInstallHandler(&vectors[16],(uint64_t)vector16,0x8eUL);
    vInstallHandler(&vectors[17],(uint64_t)vector17,0x8eUL);
    vInstallHandler(&vectors[18],(uint64_t)vector18,0x8eUL);
    vInstallHandler(&vectors[19],(uint64_t)vector19,0x8eUL);
    vInstallHandler(&vectors[32],(uint64_t)vector32,0x8eUL);
    vInstallHandler(&vectors[33],(uint64_t)vector33,0x8eUL);
    vInstallHandler(&vectors[34],(uint64_t)vector34,0x8eUL);
    vInstallHandler(&vectors[35],(uint64_t)vector35,0x8eUL);
    vInstallHandler(&vectors[36],(uint64_t)vector36,0x8eUL);
    vInstallHandler(&vectors[37],(uint64_t)vector37,0x8eUL);
    vInstallHandler(&vectors[38],(uint64_t)vector38,0x8eUL);
    vInstallHandler(&vectors[39],(uint64_t)vector39,0x8eUL);
    vInstallHandler(&vectors[40],(uint64_t)vector40,0x8eUL);
    vInstallHandler(&vectors[41],(uint64_t)vector41,0x8eUL);
    vInstallHandler(&vectors[42],(uint64_t)vector42,0x8eUL);
    vInstallHandler(&vectors[43],(uint64_t)vector43,0x8eUL);
    vInstallHandler(&vectors[44],(uint64_t)vector44,0x8eUL);
    vInstallHandler(&vectors[45],(uint64_t)vector45,0x8eUL);
    vInstallHandler(&vectors[46],(uint64_t)vector46,0x8eUL);
    vInstallHandler(&vectors[47],(uint64_t)vector47,0x8eUL);
    vInstallHandler(&vectors[48],(uint64_t)vector48,0x8eUL);
    vInstallHandler(&vectors[49],(uint64_t)vector49,0x8eUL);
    vInstallHandler(&vectors[50],(uint64_t)vector50,0x8eUL);
    vInstallHandler(&vectors[51],(uint64_t)vector51,0x8eUL);
    vInstallHandler(&vectors[52],(uint64_t)vector52,0x8eUL);
    vInstallHandler(&vectors[53],(uint64_t)vector53,0x8eUL);
    vInstallHandler(&vectors[54],(uint64_t)vector54,0x8eUL);
    vInstallHandler(&vectors[55],(uint64_t)vector55,0x8eUL);
    vInstallHandler(&vectors[56],(uint64_t)vector56,0x8eUL);
    vInstallHandler(&vectors[57],(uint64_t)vector57,0x8eUL);
    vInstallHandler(&vectors[58],(uint64_t)vector58,0x8eUL);
    vInstallHandler(&vectors[59],(uint64_t)vector59,0x8eUL);
    vInstallHandler(&vectors[60],(uint64_t)vector60,0x8eUL);
    vInstallHandler(&vectors[61],(uint64_t)vector61,0x8eUL);
    vInstallHandler(&vectors[62],(uint64_t)vector62,0x8eUL);
    vInstallHandler(&vectors[63],(uint64_t)vector63,0x8eUL);
    vInstallHandler(&vectors[64],(uint64_t)vector64,0x8eUL);
    vInstallHandler(&vectors[65],(uint64_t)vector65,0x8eUL);
    vInstallHandler(&vectors[66],(uint64_t)vector66,0x8eUL);
    vInstallHandler(&vectors[67],(uint64_t)vector67,0x8eUL);
    vInstallHandler(&vectors[68],(uint64_t)vector68,0x8eUL);
    vInstallHandler(&vectors[69],(uint64_t)vector69,0x8eUL);
    vInstallHandler(&vectors[70],(uint64_t)vector70,0x8eUL);
    vInstallHandler(&vectors[71],(uint64_t)vector71,0x8eUL);
    vInstallHandler(&vectors[72],(uint64_t)vector72,0x8eUL);
    vInstallHandler(&vectors[73],(uint64_t)vector73,0x8eUL);
    vInstallHandler(&vectors[74],(uint64_t)vector74,0x8eUL);
    vInstallHandler(&vectors[75],(uint64_t)vector75,0x8eUL);
    vInstallHandler(&vectors[76],(uint64_t)vector76,0x8eUL);
    vInstallHandler(&vectors[77],(uint64_t)vector77,0x8eUL);
    vInstallHandler(&vectors[78],(uint64_t)vector78,0x8eUL);
    vInstallHandler(&vectors[79],(uint64_t)vector79,0x8eUL);
    vInstallHandler(&vectors[80],(uint64_t)vector80,0x8eUL);
    vInstallHandler(&vectors[81],(uint64_t)vector81,0x8eUL);
    vInstallHandler(&vectors[82],(uint64_t)vector82,0x8eUL);
    vInstallHandler(&vectors[83],(uint64_t)vector83,0x8eUL);
    vInstallHandler(&vectors[84],(uint64_t)vector84,0x8eUL);
    vInstallHandler(&vectors[85],(uint64_t)vector85,0x8eUL);
    vInstallHandler(&vectors[86],(uint64_t)vector86,0x8eUL);
    vInstallHandler(&vectors[87],(uint64_t)vector87,0x8eUL);
    vInstallHandler(&vectors[88],(uint64_t)vector88,0x8eUL);
    vInstallHandler(&vectors[89],(uint64_t)vector89,0x8eUL);
    vInstallHandler(&vectors[90],(uint64_t)vector90,0x8eUL);
    vInstallHandler(&vectors[91],(uint64_t)vector91,0x8eUL);
    vInstallHandler(&vectors[92],(uint64_t)vector92,0x8eUL);
    vInstallHandler(&vectors[93],(uint64_t)vector93,0x8eUL);
    vInstallHandler(&vectors[94],(uint64_t)vector94,0x8eUL);
    vInstallHandler(&vectors[95],(uint64_t)vector95,0x8eUL);
    vInstallHandler(&vectors[96],(uint64_t)vector96,0x8eUL);
    vInstallHandler(&vectors[97],(uint64_t)vector97,0x8eUL);
    vInstallHandler(&vectors[98],(uint64_t)vector98,0x8eUL);
    vInstallHandler(&vectors[99],(uint64_t)vector99,0x8eUL);
    vInstallHandler(&vectors[100],(uint64_t)vector100,0x8eUL);
    vInstallHandler(&vectors[101],(uint64_t)vector101,0x8eUL);
    vInstallHandler(&vectors[102],(uint64_t)vector102,0x8eUL);
    vInstallHandler(&vectors[103],(uint64_t)vector103,0x8eUL);
    vInstallHandler(&vectors[104],(uint64_t)vector104,0x8eUL);
    vInstallHandler(&vectors[105],(uint64_t)vector105,0x8eUL);
    vInstallHandler(&vectors[106],(uint64_t)vector106,0x8eUL);
    vInstallHandler(&vectors[107],(uint64_t)vector107,0x8eUL);
    vInstallHandler(&vectors[108],(uint64_t)vector108,0x8eUL);
    vInstallHandler(&vectors[109],(uint64_t)vector109,0x8eUL);
    vInstallHandler(&vectors[110],(uint64_t)vector110,0x8eUL);
    vInstallHandler(&vectors[111],(uint64_t)vector111,0x8eUL);
    vInstallHandler(&vectors[112],(uint64_t)vector112,0x8eUL);
    vInstallHandler(&vectors[113],(uint64_t)vector113,0x8eUL);
    vInstallHandler(&vectors[114],(uint64_t)vector114,0x8eUL);
    vInstallHandler(&vectors[115],(uint64_t)vector115,0x8eUL);
    vInstallHandler(&vectors[116],(uint64_t)vector116,0x8eUL);
    vInstallHandler(&vectors[117],(uint64_t)vector117,0x8eUL);
    vInstallHandler(&vectors[118],(uint64_t)vector118,0x8eUL);
    vInstallHandler(&vectors[119],(uint64_t)vector119,0x8eUL);
    vInstallHandler(&vectors[120],(uint64_t)vector120,0x8eUL);
    vInstallHandler(&vectors[121],(uint64_t)vector121,0x8eUL);
    vInstallHandler(&vectors[122],(uint64_t)vector122,0x8eUL);
    vInstallHandler(&vectors[123],(uint64_t)vector123,0x8eUL);
    vInstallHandler(&vectors[124],(uint64_t)vector124,0x8eUL);
    vInstallHandler(&vectors[125],(uint64_t)vector125,0x8eUL);
    vInstallHandler(&vectors[126],(uint64_t)vector126,0x8eUL);
    vInstallHandler(&vectors[127],(uint64_t)vector127,0x8eUL);
    vInstallHandler(&vectors[129],(uint64_t)vector129,0x8eUL);
    vInstallHandler(&vectors[130],(uint64_t)vector130,0x8eUL);
    vInstallHandler(&vectors[131],(uint64_t)vector131,0x8eUL);
    vInstallHandler(&vectors[132],(uint64_t)vector132,0x8eUL);
    vInstallHandler(&vectors[133],(uint64_t)vector133,0x8eUL);
    vInstallHandler(&vectors[134],(uint64_t)vector134,0x8eUL);
    vInstallHandler(&vectors[135],(uint64_t)vector135,0x8eUL);
    vInstallHandler(&vectors[136],(uint64_t)vector136,0x8eUL);
    vInstallHandler(&vectors[137],(uint64_t)vector137,0x8eUL);
    vInstallHandler(&vectors[138],(uint64_t)vector138,0x8eUL);
    vInstallHandler(&vectors[139],(uint64_t)vector139,0x8eUL);
    vInstallHandler(&vectors[140],(uint64_t)vector140,0x8eUL);
    vInstallHandler(&vectors[141],(uint64_t)vector141,0x8eUL);
    vInstallHandler(&vectors[142],(uint64_t)vector142,0x8eUL);
    vInstallHandler(&vectors[143],(uint64_t)vector143,0x8eUL);
    vInstallHandler(&vectors[144],(uint64_t)vector144,0x8eUL);
    vInstallHandler(&vectors[145],(uint64_t)vector145,0x8eUL);
    vInstallHandler(&vectors[146],(uint64_t)vector146,0x8eUL);
    vInstallHandler(&vectors[147],(uint64_t)vector147,0x8eUL);
    vInstallHandler(&vectors[148],(uint64_t)vector148,0x8eUL);
    vInstallHandler(&vectors[149],(uint64_t)vector149,0x8eUL);
    vInstallHandler(&vectors[150],(uint64_t)vector150,0x8eUL);
    vInstallHandler(&vectors[151],(uint64_t)vector151,0x8eUL);
    vInstallHandler(&vectors[152],(uint64_t)vector152,0x8eUL);
    vInstallHandler(&vectors[153],(uint64_t)vector153,0x8eUL);
    vInstallHandler(&vectors[154],(uint64_t)vector154,0x8eUL);
    vInstallHandler(&vectors[155],(uint64_t)vector155,0x8eUL);
    vInstallHandler(&vectors[156],(uint64_t)vector156,0x8eUL);
    vInstallHandler(&vectors[157],(uint64_t)vector157,0x8eUL);
    vInstallHandler(&vectors[158],(uint64_t)vector158,0x8eUL);
    vInstallHandler(&vectors[159],(uint64_t)vector159,0x8eUL);
    vInstallHandler(&vectors[160],(uint64_t)vector160,0x8eUL);
    vInstallHandler(&vectors[161],(uint64_t)vector161,0x8eUL);
    vInstallHandler(&vectors[162],(uint64_t)vector162,0x8eUL);
    vInstallHandler(&vectors[163],(uint64_t)vector163,0x8eUL);
    vInstallHandler(&vectors[164],(uint64_t)vector164,0x8eUL);
    vInstallHandler(&vectors[165],(uint64_t)vector165,0x8eUL);
    vInstallHandler(&vectors[166],(uint64_t)vector166,0x8eUL);
    vInstallHandler(&vectors[167],(uint64_t)vector167,0x8eUL);
    vInstallHandler(&vectors[168],(uint64_t)vector168,0x8eUL);
    vInstallHandler(&vectors[169],(uint64_t)vector169,0x8eUL);
    vInstallHandler(&vectors[170],(uint64_t)vector170,0x8eUL);
    vInstallHandler(&vectors[171],(uint64_t)vector171,0x8eUL);
    vInstallHandler(&vectors[172],(uint64_t)vector172,0x8eUL);
    vInstallHandler(&vectors[173],(uint64_t)vector173,0x8eUL);
    vInstallHandler(&vectors[174],(uint64_t)vector174,0x8eUL);
    vInstallHandler(&vectors[175],(uint64_t)vector175,0x8eUL);
    vInstallHandler(&vectors[176],(uint64_t)vector176,0x8eUL);
    vInstallHandler(&vectors[177],(uint64_t)vector177,0x8eUL);
    vInstallHandler(&vectors[178],(uint64_t)vector178,0x8eUL);
    vInstallHandler(&vectors[179],(uint64_t)vector179,0x8eUL);
    vInstallHandler(&vectors[180],(uint64_t)vector180,0x8eUL);
    vInstallHandler(&vectors[181],(uint64_t)vector181,0x8eUL);
    vInstallHandler(&vectors[182],(uint64_t)vector182,0x8eUL);
    vInstallHandler(&vectors[183],(uint64_t)vector183,0x8eUL);
    vInstallHandler(&vectors[184],(uint64_t)vector184,0x8eUL);
    vInstallHandler(&vectors[185],(uint64_t)vector185,0x8eUL);
    vInstallHandler(&vectors[186],(uint64_t)vector186,0x8eUL);
    vInstallHandler(&vectors[187],(uint64_t)vector187,0x8eUL);
    vInstallHandler(&vectors[188],(uint64_t)vector188,0x8eUL);
    vInstallHandler(&vectors[189],(uint64_t)vector189,0x8eUL);
    vInstallHandler(&vectors[190],(uint64_t)vector190,0x8eUL);
    vInstallHandler(&vectors[191],(uint64_t)vector191,0x8eUL);
    vInstallHandler(&vectors[192],(uint64_t)vector192,0x8eUL);
    vInstallHandler(&vectors[193],(uint64_t)vector193,0x8eUL);
    vInstallHandler(&vectors[194],(uint64_t)vector194,0x8eUL);
    vInstallHandler(&vectors[195],(uint64_t)vector195,0x8eUL);
    vInstallHandler(&vectors[196],(uint64_t)vector196,0x8eUL);
    vInstallHandler(&vectors[197],(uint64_t)vector197,0x8eUL);
    vInstallHandler(&vectors[198],(uint64_t)vector198,0x8eUL);
    vInstallHandler(&vectors[199],(uint64_t)vector199,0x8eUL);
    vInstallHandler(&vectors[200],(uint64_t)vector200,0x8eUL);
    vInstallHandler(&vectors[201],(uint64_t)vector201,0x8eUL);
    vInstallHandler(&vectors[202],(uint64_t)vector202,0x8eUL);
    vInstallHandler(&vectors[203],(uint64_t)vector203,0x8eUL);
    vInstallHandler(&vectors[204],(uint64_t)vector204,0x8eUL);
    vInstallHandler(&vectors[205],(uint64_t)vector205,0x8eUL);
    vInstallHandler(&vectors[206],(uint64_t)vector206,0x8eUL);
    vInstallHandler(&vectors[207],(uint64_t)vector207,0x8eUL);
    vInstallHandler(&vectors[208],(uint64_t)vector208,0x8eUL);
    vInstallHandler(&vectors[209],(uint64_t)vector209,0x8eUL);
    vInstallHandler(&vectors[210],(uint64_t)vector210,0x8eUL);
    vInstallHandler(&vectors[211],(uint64_t)vector211,0x8eUL);
    vInstallHandler(&vectors[212],(uint64_t)vector212,0x8eUL);
    vInstallHandler(&vectors[213],(uint64_t)vector213,0x8eUL);
    vInstallHandler(&vectors[214],(uint64_t)vector214,0x8eUL);
    vInstallHandler(&vectors[215],(uint64_t)vector215,0x8eUL);
    vInstallHandler(&vectors[216],(uint64_t)vector216,0x8eUL);
    vInstallHandler(&vectors[217],(uint64_t)vector217,0x8eUL);
    vInstallHandler(&vectors[218],(uint64_t)vector218,0x8eUL);
    vInstallHandler(&vectors[219],(uint64_t)vector219,0x8eUL);
    vInstallHandler(&vectors[220],(uint64_t)vector220,0x8eUL);
    vInstallHandler(&vectors[221],(uint64_t)vector221,0x8eUL);
    vInstallHandler(&vectors[222],(uint64_t)vector222,0x8eUL);
    vInstallHandler(&vectors[223],(uint64_t)vector223,0x8eUL);
    vInstallHandler(&vectors[224],(uint64_t)vector224,0x8eUL);
    vInstallHandler(&vectors[225],(uint64_t)vector225,0x8eUL);
    vInstallHandler(&vectors[226],(uint64_t)vector226,0x8eUL);
    vInstallHandler(&vectors[227],(uint64_t)vector227,0x8eUL);
    vInstallHandler(&vectors[228],(uint64_t)vector228,0x8eUL);
    vInstallHandler(&vectors[229],(uint64_t)vector229,0x8eUL);
    vInstallHandler(&vectors[230],(uint64_t)vector230,0x8eUL);
    vInstallHandler(&vectors[231],(uint64_t)vector231,0x8eUL);
    vInstallHandler(&vectors[232],(uint64_t)vector232,0x8eUL);
    vInstallHandler(&vectors[233],(uint64_t)vector233,0x8eUL);
    vInstallHandler(&vectors[234],(uint64_t)vector234,0x8eUL);
    vInstallHandler(&vectors[235],(uint64_t)vector235,0x8eUL);
    vInstallHandler(&vectors[236],(uint64_t)vector236,0x8eUL);
    vInstallHandler(&vectors[237],(uint64_t)vector237,0x8eUL);
    vInstallHandler(&vectors[238],(uint64_t)vector238,0x8eUL);
    vInstallHandler(&vectors[239],(uint64_t)vector239,0x8eUL);
    vInstallHandler(&vectors[240],(uint64_t)vector240,0x8eUL);
    vInstallHandler(&vectors[241],(uint64_t)vector241,0x8eUL);
    vInstallHandler(&vectors[242],(uint64_t)vector242,0x8eUL);
    vInstallHandler(&vectors[243],(uint64_t)vector243,0x8eUL);
    vInstallHandler(&vectors[244],(uint64_t)vector244,0x8eUL);
    vInstallHandler(&vectors[245],(uint64_t)vector245,0x8eUL);
    vInstallHandler(&vectors[246],(uint64_t)vector246,0x8eUL);
    vInstallHandler(&vectors[247],(uint64_t)vector247,0x8eUL);
    vInstallHandler(&vectors[248],(uint64_t)vector248,0x8eUL);
    vInstallHandler(&vectors[249],(uint64_t)vector249,0x8eUL);
    vInstallHandler(&vectors[250],(uint64_t)vector250,0x8eUL);
    vInstallHandler(&vectors[251],(uint64_t)vector251,0x8eUL);
    vInstallHandler(&vectors[252],(uint64_t)vector252,0x8eUL);
    vInstallHandler(&vectors[253],(uint64_t)vector253,0x8eUL);
    vInstallHandler(&vectors[0x80],(uint64_t)sysint,0xeeUL);
    vInstallHandler(&vectors[254],(uint64_t)vector254,0xeeUL);
    vInstallHandler(&vectors[255],(uint64_t)vector255,0xeeUL);

    idt_pointer.limit = sizeof(vectors)-1;
    idt_pointer.addr = (uint64_t)vectors;
    load_idt(&idt_pointer);
    init_irq_handlers();
}

static void vScheduleTCB(StackType_t **nextTCB) {
    struct TrapFrame *tf = (struct TrapFrame *)(*nextTCB);
    xMPU_SETTINGS * xMPUSettings = (xMPU_SETTINGS *) (nextTCB+1);
    Tss.rsp0 = (uint64_t) xMPUSettings->kernel_stack;
    load_cr3(xMPUSettings->pgd);
    starttask(*nextTCB);
}

static void vYieldHandler(struct TrapFrame *tf)
{
    StackType_t **prevTCB = (StackType_t **) pxCurrentTCB;
    *prevTCB = (StackType_t *) tf;
    vTaskSwitchContext();
    StackType_t **nextTCB = (StackType_t **)pxCurrentTCB;
    if (nextTCB != prevTCB) {
        vScheduleTCB(nextTCB);
    }
    return;
}

static void vTimerHandler(struct TrapFrame *tf)
{
    if (pxCurrentTCB !=NULL) {
        StackType_t **prevTCB = (StackType_t **)pxCurrentTCB;
        BaseType_t rc = xTaskIncrementTick();
        if (rc == pdTRUE) {
            vTaskSwitchContext();
            StackType_t **nextTCB = (StackType_t **)pxCurrentTCB;
            if (prevTCB != nextTCB) {
                *prevTCB = (StackType_t *) tf;
                eoi();
                vScheduleTCB(nextTCB);
            }
        }
    }
}

void vHandler(struct TrapFrame *tf)
{
    unsigned char isr_value;

    switch (tf->trapno) {
    case TRAP_YIELD:
    {
        vYieldHandler(tf);
        break;
    }

    case TRAP_PIC_TIMER:
        eoi();
        break;

    case TRAP_HYPERVISOR_EVENT:
	do_hypervisor_callback(0);
        eoi();
	break;

    case TRAP_SPURIOUS:
        isr_value = read_isr();
        if ((isr_value&(1<<7)) != 0) {
            eoi();
        }
        break;

    case TRAP_SCI:
    {
        process_sci();
        eoi();
	break;
    }

    case TRAP_TIMER:
    {
        vTimerHandler(tf);
        eoi();
        break;
    }

    case TRAP_SYSCALL:
        vSystemCall(tf);
        break;

    default:
        if (tf->trapno > TRAP_PIC_TIMER) {
            if ( (ulInterruptNesting == (uint32_t)0) && xTaskUsesFPU) {
                asm volatile(" fxsave %0 "::"m"(pucPortTaskFPUContextBuffer));
            }
            ulInterruptNesting++;
            uint32_t irq = tf->trapno - TRAP_PIC_TIMER;
            INT_HANDLER irq_handler = get_int_handler(irq);
            if (irq_handler != NULL) {
                irq_handler();
            }
            eoi();
            ulInterruptNesting--;
            if ( (ulInterruptNesting == (uint32_t)0) && xTaskUsesFPU) {
                 asm volatile(" fxrstor %0 "::"m"(pucPortTaskFPUContextBuffer));
            }
            if ((ulInterruptNesting ==(uint32_t) 0) && ulPortYieldPending) {
                ulPortYieldPending = 0;
                vYieldHandler(tf);
            }
            break;
        }
        printk("\n[Error %d at ring %d] errorcode:%d cr2:%p rflags: %p ss:%p\n", tf->trapno, (tf->cs & 3), tf->errorcode, read_cr2(),tf->rflags,tf->ss);
        printk("Registers:rip=%p rsp=%p rbp=%p\n", tf->rip, tf->rsp, tf->rbp);
        printk("Registers:rax=%p rbx=%p rcx=%p rdx=%p rsi=%p rdi=%p\n", tf->rax,tf->rbx,tf->rcx,tf->rdx,tf->rsi,tf->rdi);
        printk("Registers:r8=%p r9=%p r10=%p r11=%p r12=%p r13=%p r14=%p r15=%p\n", tf->r8,tf->r9,tf->r10,tf->r11,tf->r12,tf->r13,tf->r14,tf->r15);
        if ((tf->cs & 3) != 0) {
            xMPU_SETTINGS * xMPUSettings = (xMPU_SETTINGS *) (pxCurrentTCB+1);
            Tss.rsp0 = (uint64_t) xMPUSettings->kernel_stack;
            vFreeAllPages((uint64_t *) xMPUSettings->pgd);
            load_cr3(&pml4);
            eoi();
            vTaskDelete((TaskHandle_t)pxCurrentTCB);
        }
	vAssertCalled(__FILE__,__LINE__);
    }

}
