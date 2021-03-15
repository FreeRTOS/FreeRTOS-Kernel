//  ----------------------------------------------------------------------------
//          ATMEL Microcontroller Software Support  -  ROUSSET  -
//  ----------------------------------------------------------------------------
//  DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
//  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
//  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
//  DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
//  OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
//  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
//  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
//  EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//  ----------------------------------------------------------------------------
// File Name           : AT91SAM7X128.h
// Object              : AT91SAM7X128 definitions
// Generated           : AT91 SW Application Group  05/20/2005 (16:22:23)
// 
// CVS Reference       : /AT91SAM7X128.pl/1.14/Tue May 10 12:12:05 2005//
// CVS Reference       : /SYS_SAM7X.pl/1.3/Tue Feb  1 17:01:43 2005//
// CVS Reference       : /MC_SAM7X.pl/1.2/Fri May 20 14:13:04 2005//
// CVS Reference       : /PMC_SAM7X.pl/1.4/Tue Feb  8 13:58:10 2005//
// CVS Reference       : /RSTC_SAM7X.pl/1.1/Tue Feb  1 16:16:26 2005//
// CVS Reference       : /UDP_SAM7X.pl/1.1/Tue May 10 11:35:35 2005//
// CVS Reference       : /PWM_SAM7X.pl/1.1/Tue May 10 11:53:07 2005//
// CVS Reference       : /AIC_6075B.pl/1.3/Fri May 20 14:01:30 2005//
// CVS Reference       : /PIO_6057A.pl/1.2/Thu Feb  3 10:18:28 2005//
// CVS Reference       : /RTTC_6081A.pl/1.2/Tue Nov  9 14:43:58 2004//
// CVS Reference       : /PITC_6079A.pl/1.2/Tue Nov  9 14:43:56 2004//
// CVS Reference       : /WDTC_6080A.pl/1.3/Tue Nov  9 14:44:00 2004//
// CVS Reference       : /VREG_6085B.pl/1.1/Tue Feb  1 16:05:48 2005//
// CVS Reference       : /PDC_6074C.pl/1.2/Thu Feb  3 08:48:54 2005//
// CVS Reference       : /DBGU_6059D.pl/1.1/Mon Jan 31 13:15:32 2005//
// CVS Reference       : /SPI_6088D.pl/1.3/Fri May 20 14:08:59 2005//
// CVS Reference       : /US_6089C.pl/1.1/Mon Jul 12 18:23:26 2004//
// CVS Reference       : /SSC_6078A.pl/1.1/Tue Jul 13 07:45:40 2004//
// CVS Reference       : /TWI_6061A.pl/1.1/Tue Jul 13 07:38:06 2004//
// CVS Reference       : /TC_6082A.pl/1.7/Fri Mar 11 12:52:17 2005//
// CVS Reference       : /CAN_6019B.pl/1.1/Tue Mar  8 12:42:22 2005//
// CVS Reference       : /EMACB_6119A.pl/1.5/Thu Feb  3 15:52:04 2005//
// CVS Reference       : /ADC_6051C.pl/1.1/Fri Oct 17 09:12:38 2003//
// CVS Reference       : /AES_6149A.pl/1.10/Mon Feb  7 09:44:25 2005//
// CVS Reference       : /DES3_6150A.pl/1.1/Mon Jan 17 08:34:31 2005//
//  ----------------------------------------------------------------------------

#ifndef AT91SAM7X128_H
#define AT91SAM7X128_H

typedef volatile unsigned int AT91_REG;// Hardware register definition

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR System Peripherals
// *****************************************************************************
typedef struct _AT91S_SYS {
	AT91_REG	 AIC_SMR[32]; 	// Source Mode Register
	AT91_REG	 AIC_SVR[32]; 	// Source Vector Register
	AT91_REG	 AIC_IVR; 	// IRQ Vector Register
	AT91_REG	 AIC_FVR; 	// FIQ Vector Register
	AT91_REG	 AIC_ISR; 	// Interrupt Status Register
	AT91_REG	 AIC_IPR; 	// Interrupt Pending Register
	AT91_REG	 AIC_IMR; 	// Interrupt Mask Register
	AT91_REG	 AIC_CISR; 	// Core Interrupt Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 AIC_IECR; 	// Interrupt Enable Command Register
	AT91_REG	 AIC_IDCR; 	// Interrupt Disable Command Register
	AT91_REG	 AIC_ICCR; 	// Interrupt Clear Command Register
	AT91_REG	 AIC_ISCR; 	// Interrupt Set Command Register
	AT91_REG	 AIC_EOICR; 	// End of Interrupt Command Register
	AT91_REG	 AIC_SPU; 	// Spurious Vector Register
	AT91_REG	 AIC_DCR; 	// Debug Control Register (Protect)
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 AIC_FFER; 	// Fast Forcing Enable Register
	AT91_REG	 AIC_FFDR; 	// Fast Forcing Disable Register
	AT91_REG	 AIC_FFSR; 	// Fast Forcing Status Register
	AT91_REG	 Reserved2[45]; 	// 
	AT91_REG	 DBGU_CR; 	// Control Register
	AT91_REG	 DBGU_MR; 	// Mode Register
	AT91_REG	 DBGU_IER; 	// Interrupt Enable Register
	AT91_REG	 DBGU_IDR; 	// Interrupt Disable Register
	AT91_REG	 DBGU_IMR; 	// Interrupt Mask Register
	AT91_REG	 DBGU_CSR; 	// Channel Status Register
	AT91_REG	 DBGU_RHR; 	// Receiver Holding Register
	AT91_REG	 DBGU_THR; 	// Transmitter Holding Register
	AT91_REG	 DBGU_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 Reserved3[7]; 	// 
	AT91_REG	 DBGU_CIDR; 	// Chip ID Register
	AT91_REG	 DBGU_EXID; 	// Chip ID Extension Register
	AT91_REG	 DBGU_FNTR; 	// Force NTRST Register
	AT91_REG	 Reserved4[45]; 	// 
	AT91_REG	 DBGU_RPR; 	// Receive Pointer Register
	AT91_REG	 DBGU_RCR; 	// Receive Counter Register
	AT91_REG	 DBGU_TPR; 	// Transmit Pointer Register
	AT91_REG	 DBGU_TCR; 	// Transmit Counter Register
	AT91_REG	 DBGU_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 DBGU_RNCR; 	// Receive Next Counter Register
	AT91_REG	 DBGU_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 DBGU_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 DBGU_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 DBGU_PTSR; 	// PDC Transfer Status Register
	AT91_REG	 Reserved5[54]; 	// 
	AT91_REG	 PIOA_PER; 	// PIO Enable Register
	AT91_REG	 PIOA_PDR; 	// PIO Disable Register
	AT91_REG	 PIOA_PSR; 	// PIO Status Register
	AT91_REG	 Reserved6[1]; 	// 
	AT91_REG	 PIOA_OER; 	// Output Enable Register
	AT91_REG	 PIOA_ODR; 	// Output Disable Registerr
	AT91_REG	 PIOA_OSR; 	// Output Status Register
	AT91_REG	 Reserved7[1]; 	// 
	AT91_REG	 PIOA_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIOA_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIOA_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved8[1]; 	// 
	AT91_REG	 PIOA_SODR; 	// Set Output Data Register
	AT91_REG	 PIOA_CODR; 	// Clear Output Data Register
	AT91_REG	 PIOA_ODSR; 	// Output Data Status Register
	AT91_REG	 PIOA_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIOA_IER; 	// Interrupt Enable Register
	AT91_REG	 PIOA_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIOA_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIOA_ISR; 	// Interrupt Status Register
	AT91_REG	 PIOA_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIOA_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIOA_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved9[1]; 	// 
	AT91_REG	 PIOA_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIOA_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIOA_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved10[1]; 	// 
	AT91_REG	 PIOA_ASR; 	// Select A Register
	AT91_REG	 PIOA_BSR; 	// Select B Register
	AT91_REG	 PIOA_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved11[9]; 	// 
	AT91_REG	 PIOA_OWER; 	// Output Write Enable Register
	AT91_REG	 PIOA_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIOA_OWSR; 	// Output Write Status Register
	AT91_REG	 Reserved12[85]; 	// 
	AT91_REG	 PIOB_PER; 	// PIO Enable Register
	AT91_REG	 PIOB_PDR; 	// PIO Disable Register
	AT91_REG	 PIOB_PSR; 	// PIO Status Register
	AT91_REG	 Reserved13[1]; 	// 
	AT91_REG	 PIOB_OER; 	// Output Enable Register
	AT91_REG	 PIOB_ODR; 	// Output Disable Registerr
	AT91_REG	 PIOB_OSR; 	// Output Status Register
	AT91_REG	 Reserved14[1]; 	// 
	AT91_REG	 PIOB_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIOB_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIOB_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved15[1]; 	// 
	AT91_REG	 PIOB_SODR; 	// Set Output Data Register
	AT91_REG	 PIOB_CODR; 	// Clear Output Data Register
	AT91_REG	 PIOB_ODSR; 	// Output Data Status Register
	AT91_REG	 PIOB_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIOB_IER; 	// Interrupt Enable Register
	AT91_REG	 PIOB_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIOB_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIOB_ISR; 	// Interrupt Status Register
	AT91_REG	 PIOB_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIOB_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIOB_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved16[1]; 	// 
	AT91_REG	 PIOB_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIOB_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIOB_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved17[1]; 	// 
	AT91_REG	 PIOB_ASR; 	// Select A Register
	AT91_REG	 PIOB_BSR; 	// Select B Register
	AT91_REG	 PIOB_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved18[9]; 	// 
	AT91_REG	 PIOB_OWER; 	// Output Write Enable Register
	AT91_REG	 PIOB_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIOB_OWSR; 	// Output Write Status Register
	AT91_REG	 Reserved19[341]; 	// 
	AT91_REG	 PMC_SCER; 	// System Clock Enable Register
	AT91_REG	 PMC_SCDR; 	// System Clock Disable Register
	AT91_REG	 PMC_SCSR; 	// System Clock Status Register
	AT91_REG	 Reserved20[1]; 	// 
	AT91_REG	 PMC_PCER; 	// Peripheral Clock Enable Register
	AT91_REG	 PMC_PCDR; 	// Peripheral Clock Disable Register
	AT91_REG	 PMC_PCSR; 	// Peripheral Clock Status Register
	AT91_REG	 Reserved21[1]; 	// 
	AT91_REG	 PMC_MOR; 	// Main Oscillator Register
	AT91_REG	 PMC_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 Reserved22[1]; 	// 
	AT91_REG	 PMC_PLLR; 	// PLL Register
	AT91_REG	 PMC_MCKR; 	// Master Clock Register
	AT91_REG	 Reserved23[3]; 	// 
	AT91_REG	 PMC_PCKR[4]; 	// Programmable Clock Register
	AT91_REG	 Reserved24[4]; 	// 
	AT91_REG	 PMC_IER; 	// Interrupt Enable Register
	AT91_REG	 PMC_IDR; 	// Interrupt Disable Register
	AT91_REG	 PMC_SR; 	// Status Register
	AT91_REG	 PMC_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved25[36]; 	// 
	AT91_REG	 RSTC_RCR; 	// Reset Control Register
	AT91_REG	 RSTC_RSR; 	// Reset Status Register
	AT91_REG	 RSTC_RMR; 	// Reset Mode Register
	AT91_REG	 Reserved26[5]; 	// 
	AT91_REG	 RTTC_RTMR; 	// Real-time Mode Register
	AT91_REG	 RTTC_RTAR; 	// Real-time Alarm Register
	AT91_REG	 RTTC_RTVR; 	// Real-time Value Register
	AT91_REG	 RTTC_RTSR; 	// Real-time Status Register
	AT91_REG	 PITC_PIMR; 	// Period Interval Mode Register
	AT91_REG	 PITC_PISR; 	// Period Interval Status Register
	AT91_REG	 PITC_PIVR; 	// Period Interval Value Register
	AT91_REG	 PITC_PIIR; 	// Period Interval Image Register
	AT91_REG	 WDTC_WDCR; 	// Watchdog Control Register
	AT91_REG	 WDTC_WDMR; 	// Watchdog Mode Register
	AT91_REG	 WDTC_WDSR; 	// Watchdog Status Register
	AT91_REG	 Reserved27[5]; 	// 
	AT91_REG	 VREG_MR; 	// Voltage Regulator Mode Register
} AT91S_SYS, *AT91PS_SYS;


// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Advanced Interrupt Controller
// *****************************************************************************
typedef struct _AT91S_AIC {
	AT91_REG	 AIC_SMR[32]; 	// Source Mode Register
	AT91_REG	 AIC_SVR[32]; 	// Source Vector Register
	AT91_REG	 AIC_IVR; 	// IRQ Vector Register
	AT91_REG	 AIC_FVR; 	// FIQ Vector Register
	AT91_REG	 AIC_ISR; 	// Interrupt Status Register
	AT91_REG	 AIC_IPR; 	// Interrupt Pending Register
	AT91_REG	 AIC_IMR; 	// Interrupt Mask Register
	AT91_REG	 AIC_CISR; 	// Core Interrupt Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 AIC_IECR; 	// Interrupt Enable Command Register
	AT91_REG	 AIC_IDCR; 	// Interrupt Disable Command Register
	AT91_REG	 AIC_ICCR; 	// Interrupt Clear Command Register
	AT91_REG	 AIC_ISCR; 	// Interrupt Set Command Register
	AT91_REG	 AIC_EOICR; 	// End of Interrupt Command Register
	AT91_REG	 AIC_SPU; 	// Spurious Vector Register
	AT91_REG	 AIC_DCR; 	// Debug Control Register (Protect)
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 AIC_FFER; 	// Fast Forcing Enable Register
	AT91_REG	 AIC_FFDR; 	// Fast Forcing Disable Register
	AT91_REG	 AIC_FFSR; 	// Fast Forcing Status Register
} AT91S_AIC, *AT91PS_AIC;

// -------- AIC_SMR : (AIC Offset: 0x0) Control Register -------- 
#define AT91C_AIC_PRIOR       ((unsigned int) 0x7 <<  0) // (AIC) Priority Level
#define 	AT91C_AIC_PRIOR_LOWEST               ((unsigned int) 0x0) // (AIC) Lowest priority level
#define 	AT91C_AIC_PRIOR_HIGHEST              ((unsigned int) 0x7) // (AIC) Highest priority level
#define AT91C_AIC_SRCTYPE     ((unsigned int) 0x3 <<  5) // (AIC) Interrupt Source Type
#define 	AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL       ((unsigned int) 0x0 <<  5) // (AIC) Internal Sources Code Label High-level Sensitive
#define 	AT91C_AIC_SRCTYPE_EXT_LOW_LEVEL        ((unsigned int) 0x0 <<  5) // (AIC) External Sources Code Label Low-level Sensitive
#define 	AT91C_AIC_SRCTYPE_INT_POSITIVE_EDGE    ((unsigned int) 0x1 <<  5) // (AIC) Internal Sources Code Label Positive Edge triggered
#define 	AT91C_AIC_SRCTYPE_EXT_NEGATIVE_EDGE    ((unsigned int) 0x1 <<  5) // (AIC) External Sources Code Label Negative Edge triggered
#define 	AT91C_AIC_SRCTYPE_HIGH_LEVEL           ((unsigned int) 0x2 <<  5) // (AIC) Internal Or External Sources Code Label High-level Sensitive
#define 	AT91C_AIC_SRCTYPE_POSITIVE_EDGE        ((unsigned int) 0x3 <<  5) // (AIC) Internal Or External Sources Code Label Positive Edge triggered
// -------- AIC_CISR : (AIC Offset: 0x114) AIC Core Interrupt Status Register -------- 
#define AT91C_AIC_NFIQ        ((unsigned int) 0x1 <<  0) // (AIC) NFIQ Status
#define AT91C_AIC_NIRQ        ((unsigned int) 0x1 <<  1) // (AIC) NIRQ Status
// -------- AIC_DCR : (AIC Offset: 0x138) AIC Debug Control Register (Protect) -------- 
#define AT91C_AIC_DCR_PROT    ((unsigned int) 0x1 <<  0) // (AIC) Protection Mode
#define AT91C_AIC_DCR_GMSK    ((unsigned int) 0x1 <<  1) // (AIC) General Mask

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Peripheral DMA Controller
// *****************************************************************************
typedef struct _AT91S_PDC {
	AT91_REG	 PDC_RPR; 	// Receive Pointer Register
	AT91_REG	 PDC_RCR; 	// Receive Counter Register
	AT91_REG	 PDC_TPR; 	// Transmit Pointer Register
	AT91_REG	 PDC_TCR; 	// Transmit Counter Register
	AT91_REG	 PDC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 PDC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 PDC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 PDC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 PDC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 PDC_PTSR; 	// PDC Transfer Status Register
} AT91S_PDC, *AT91PS_PDC;

// -------- PDC_PTCR : (PDC Offset: 0x20) PDC Transfer Control Register -------- 
#define AT91C_PDC_RXTEN       ((unsigned int) 0x1 <<  0) // (PDC) Receiver Transfer Enable
#define AT91C_PDC_RXTDIS      ((unsigned int) 0x1 <<  1) // (PDC) Receiver Transfer Disable
#define AT91C_PDC_TXTEN       ((unsigned int) 0x1 <<  8) // (PDC) Transmitter Transfer Enable
#define AT91C_PDC_TXTDIS      ((unsigned int) 0x1 <<  9) // (PDC) Transmitter Transfer Disable
// -------- PDC_PTSR : (PDC Offset: 0x24) PDC Transfer Status Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Debug Unit
// *****************************************************************************
typedef struct _AT91S_DBGU {
	AT91_REG	 DBGU_CR; 	// Control Register
	AT91_REG	 DBGU_MR; 	// Mode Register
	AT91_REG	 DBGU_IER; 	// Interrupt Enable Register
	AT91_REG	 DBGU_IDR; 	// Interrupt Disable Register
	AT91_REG	 DBGU_IMR; 	// Interrupt Mask Register
	AT91_REG	 DBGU_CSR; 	// Channel Status Register
	AT91_REG	 DBGU_RHR; 	// Receiver Holding Register
	AT91_REG	 DBGU_THR; 	// Transmitter Holding Register
	AT91_REG	 DBGU_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 Reserved0[7]; 	// 
	AT91_REG	 DBGU_CIDR; 	// Chip ID Register
	AT91_REG	 DBGU_EXID; 	// Chip ID Extension Register
	AT91_REG	 DBGU_FNTR; 	// Force NTRST Register
	AT91_REG	 Reserved1[45]; 	// 
	AT91_REG	 DBGU_RPR; 	// Receive Pointer Register
	AT91_REG	 DBGU_RCR; 	// Receive Counter Register
	AT91_REG	 DBGU_TPR; 	// Transmit Pointer Register
	AT91_REG	 DBGU_TCR; 	// Transmit Counter Register
	AT91_REG	 DBGU_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 DBGU_RNCR; 	// Receive Next Counter Register
	AT91_REG	 DBGU_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 DBGU_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 DBGU_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 DBGU_PTSR; 	// PDC Transfer Status Register
} AT91S_DBGU, *AT91PS_DBGU;

// -------- DBGU_CR : (DBGU Offset: 0x0) Debug Unit Control Register -------- 
#define AT91C_US_RSTRX        ((unsigned int) 0x1 <<  2) // (DBGU) Reset Receiver
#define AT91C_US_RSTTX        ((unsigned int) 0x1 <<  3) // (DBGU) Reset Transmitter
#define AT91C_US_RXEN         ((unsigned int) 0x1 <<  4) // (DBGU) Receiver Enable
#define AT91C_US_RXDIS        ((unsigned int) 0x1 <<  5) // (DBGU) Receiver Disable
#define AT91C_US_TXEN         ((unsigned int) 0x1 <<  6) // (DBGU) Transmitter Enable
#define AT91C_US_TXDIS        ((unsigned int) 0x1 <<  7) // (DBGU) Transmitter Disable
#define AT91C_US_RSTSTA       ((unsigned int) 0x1 <<  8) // (DBGU) Reset Status Bits
// -------- DBGU_MR : (DBGU Offset: 0x4) Debug Unit Mode Register -------- 
#define AT91C_US_PAR          ((unsigned int) 0x7 <<  9) // (DBGU) Parity type
#define 	AT91C_US_PAR_EVEN                 ((unsigned int) 0x0 <<  9) // (DBGU) Even Parity
#define 	AT91C_US_PAR_ODD                  ((unsigned int) 0x1 <<  9) // (DBGU) Odd Parity
#define 	AT91C_US_PAR_SPACE                ((unsigned int) 0x2 <<  9) // (DBGU) Parity forced to 0 (Space)
#define 	AT91C_US_PAR_MARK                 ((unsigned int) 0x3 <<  9) // (DBGU) Parity forced to 1 (Mark)
#define 	AT91C_US_PAR_NONE                 ((unsigned int) 0x4 <<  9) // (DBGU) No Parity
#define 	AT91C_US_PAR_MULTI_DROP           ((unsigned int) 0x6 <<  9) // (DBGU) Multi-drop mode
#define AT91C_US_CHMODE       ((unsigned int) 0x3 << 14) // (DBGU) Channel Mode
#define 	AT91C_US_CHMODE_NORMAL               ((unsigned int) 0x0 << 14) // (DBGU) Normal Mode: The USART channel operates as an RX/TX USART.
#define 	AT91C_US_CHMODE_AUTO                 ((unsigned int) 0x1 << 14) // (DBGU) Automatic Echo: Receiver Data Input is connected to the TXD pin.
#define 	AT91C_US_CHMODE_LOCAL                ((unsigned int) 0x2 << 14) // (DBGU) Local Loopback: Transmitter Output Signal is connected to Receiver Input Signal.
#define 	AT91C_US_CHMODE_REMOTE               ((unsigned int) 0x3 << 14) // (DBGU) Remote Loopback: RXD pin is internally connected to TXD pin.
// -------- DBGU_IER : (DBGU Offset: 0x8) Debug Unit Interrupt Enable Register -------- 
#define AT91C_US_RXRDY        ((unsigned int) 0x1 <<  0) // (DBGU) RXRDY Interrupt
#define AT91C_US_TXRDY        ((unsigned int) 0x1 <<  1) // (DBGU) TXRDY Interrupt
#define AT91C_US_ENDRX        ((unsigned int) 0x1 <<  3) // (DBGU) End of Receive Transfer Interrupt
#define AT91C_US_ENDTX        ((unsigned int) 0x1 <<  4) // (DBGU) End of Transmit Interrupt
#define AT91C_US_OVRE         ((unsigned int) 0x1 <<  5) // (DBGU) Overrun Interrupt
#define AT91C_US_FRAME        ((unsigned int) 0x1 <<  6) // (DBGU) Framing Error Interrupt
#define AT91C_US_PARE         ((unsigned int) 0x1 <<  7) // (DBGU) Parity Error Interrupt
#define AT91C_US_TXEMPTY      ((unsigned int) 0x1 <<  9) // (DBGU) TXEMPTY Interrupt
#define AT91C_US_TXBUFE       ((unsigned int) 0x1 << 11) // (DBGU) TXBUFE Interrupt
#define AT91C_US_RXBUFF       ((unsigned int) 0x1 << 12) // (DBGU) RXBUFF Interrupt
#define AT91C_US_COMM_TX      ((unsigned int) 0x1 << 30) // (DBGU) COMM_TX Interrupt
#define AT91C_US_COMM_RX      ((unsigned int) 0x1 << 31) // (DBGU) COMM_RX Interrupt
// -------- DBGU_IDR : (DBGU Offset: 0xc) Debug Unit Interrupt Disable Register -------- 
// -------- DBGU_IMR : (DBGU Offset: 0x10) Debug Unit Interrupt Mask Register -------- 
// -------- DBGU_CSR : (DBGU Offset: 0x14) Debug Unit Channel Status Register -------- 
// -------- DBGU_FNTR : (DBGU Offset: 0x48) Debug Unit FORCE_NTRST Register -------- 
#define AT91C_US_FORCE_NTRST  ((unsigned int) 0x1 <<  0) // (DBGU) Force NTRST in JTAG

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Parallel Input Output Controler
// *****************************************************************************
typedef struct _AT91S_PIO {
	AT91_REG	 PIO_PER; 	// PIO Enable Register
	AT91_REG	 PIO_PDR; 	// PIO Disable Register
	AT91_REG	 PIO_PSR; 	// PIO Status Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 PIO_OER; 	// Output Enable Register
	AT91_REG	 PIO_ODR; 	// Output Disable Registerr
	AT91_REG	 PIO_OSR; 	// Output Status Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 PIO_IFER; 	// Input Filter Enable Register
	AT91_REG	 PIO_IFDR; 	// Input Filter Disable Register
	AT91_REG	 PIO_IFSR; 	// Input Filter Status Register
	AT91_REG	 Reserved2[1]; 	// 
	AT91_REG	 PIO_SODR; 	// Set Output Data Register
	AT91_REG	 PIO_CODR; 	// Clear Output Data Register
	AT91_REG	 PIO_ODSR; 	// Output Data Status Register
	AT91_REG	 PIO_PDSR; 	// Pin Data Status Register
	AT91_REG	 PIO_IER; 	// Interrupt Enable Register
	AT91_REG	 PIO_IDR; 	// Interrupt Disable Register
	AT91_REG	 PIO_IMR; 	// Interrupt Mask Register
	AT91_REG	 PIO_ISR; 	// Interrupt Status Register
	AT91_REG	 PIO_MDER; 	// Multi-driver Enable Register
	AT91_REG	 PIO_MDDR; 	// Multi-driver Disable Register
	AT91_REG	 PIO_MDSR; 	// Multi-driver Status Register
	AT91_REG	 Reserved3[1]; 	// 
	AT91_REG	 PIO_PPUDR; 	// Pull-up Disable Register
	AT91_REG	 PIO_PPUER; 	// Pull-up Enable Register
	AT91_REG	 PIO_PPUSR; 	// Pull-up Status Register
	AT91_REG	 Reserved4[1]; 	// 
	AT91_REG	 PIO_ASR; 	// Select A Register
	AT91_REG	 PIO_BSR; 	// Select B Register
	AT91_REG	 PIO_ABSR; 	// AB Select Status Register
	AT91_REG	 Reserved5[9]; 	// 
	AT91_REG	 PIO_OWER; 	// Output Write Enable Register
	AT91_REG	 PIO_OWDR; 	// Output Write Disable Register
	AT91_REG	 PIO_OWSR; 	// Output Write Status Register
} AT91S_PIO, *AT91PS_PIO;


// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Clock Generator Controler
// *****************************************************************************
typedef struct _AT91S_CKGR {
	AT91_REG	 CKGR_MOR; 	// Main Oscillator Register
	AT91_REG	 CKGR_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 CKGR_PLLR; 	// PLL Register
} AT91S_CKGR, *AT91PS_CKGR;

// -------- CKGR_MOR : (CKGR Offset: 0x0) Main Oscillator Register -------- 
#define AT91C_CKGR_MOSCEN     ((unsigned int) 0x1 <<  0) // (CKGR) Main Oscillator Enable
#define AT91C_CKGR_OSCBYPASS  ((unsigned int) 0x1 <<  1) // (CKGR) Main Oscillator Bypass
#define AT91C_CKGR_OSCOUNT    ((unsigned int) 0xFF <<  8) // (CKGR) Main Oscillator Start-up Time
// -------- CKGR_MCFR : (CKGR Offset: 0x4) Main Clock Frequency Register -------- 
#define AT91C_CKGR_MAINF      ((unsigned int) 0xFFFF <<  0) // (CKGR) Main Clock Frequency
#define AT91C_CKGR_MAINRDY    ((unsigned int) 0x1 << 16) // (CKGR) Main Clock Ready
// -------- CKGR_PLLR : (CKGR Offset: 0xc) PLL B Register -------- 
#define AT91C_CKGR_DIV        ((unsigned int) 0xFF <<  0) // (CKGR) Divider Selected
#define 	AT91C_CKGR_DIV_0                    ((unsigned int) 0x0) // (CKGR) Divider output is 0
#define 	AT91C_CKGR_DIV_BYPASS               ((unsigned int) 0x1) // (CKGR) Divider is bypassed
#define AT91C_CKGR_PLLCOUNT   ((unsigned int) 0x3F <<  8) // (CKGR) PLL Counter
#define AT91C_CKGR_OUT        ((unsigned int) 0x3 << 14) // (CKGR) PLL Output Frequency Range
#define 	AT91C_CKGR_OUT_0                    ((unsigned int) 0x0 << 14) // (CKGR) Please refer to the PLL datasheet
#define 	AT91C_CKGR_OUT_1                    ((unsigned int) 0x1 << 14) // (CKGR) Please refer to the PLL datasheet
#define 	AT91C_CKGR_OUT_2                    ((unsigned int) 0x2 << 14) // (CKGR) Please refer to the PLL datasheet
#define 	AT91C_CKGR_OUT_3                    ((unsigned int) 0x3 << 14) // (CKGR) Please refer to the PLL datasheet
#define AT91C_CKGR_MUL        ((unsigned int) 0x7FF << 16) // (CKGR) PLL Multiplier
#define AT91C_CKGR_USBDIV     ((unsigned int) 0x3 << 28) // (CKGR) Divider for USB Clocks
#define 	AT91C_CKGR_USBDIV_0                    ((unsigned int) 0x0 << 28) // (CKGR) Divider output is PLL clock output
#define 	AT91C_CKGR_USBDIV_1                    ((unsigned int) 0x1 << 28) // (CKGR) Divider output is PLL clock output divided by 2
#define 	AT91C_CKGR_USBDIV_2                    ((unsigned int) 0x2 << 28) // (CKGR) Divider output is PLL clock output divided by 4

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Power Management Controler
// *****************************************************************************
typedef struct _AT91S_PMC {
	AT91_REG	 PMC_SCER; 	// System Clock Enable Register
	AT91_REG	 PMC_SCDR; 	// System Clock Disable Register
	AT91_REG	 PMC_SCSR; 	// System Clock Status Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 PMC_PCER; 	// Peripheral Clock Enable Register
	AT91_REG	 PMC_PCDR; 	// Peripheral Clock Disable Register
	AT91_REG	 PMC_PCSR; 	// Peripheral Clock Status Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 PMC_MOR; 	// Main Oscillator Register
	AT91_REG	 PMC_MCFR; 	// Main Clock  Frequency Register
	AT91_REG	 Reserved2[1]; 	// 
	AT91_REG	 PMC_PLLR; 	// PLL Register
	AT91_REG	 PMC_MCKR; 	// Master Clock Register
	AT91_REG	 Reserved3[3]; 	// 
	AT91_REG	 PMC_PCKR[4]; 	// Programmable Clock Register
	AT91_REG	 Reserved4[4]; 	// 
	AT91_REG	 PMC_IER; 	// Interrupt Enable Register
	AT91_REG	 PMC_IDR; 	// Interrupt Disable Register
	AT91_REG	 PMC_SR; 	// Status Register
	AT91_REG	 PMC_IMR; 	// Interrupt Mask Register
} AT91S_PMC, *AT91PS_PMC;

// -------- PMC_SCER : (PMC Offset: 0x0) System Clock Enable Register -------- 
#define AT91C_PMC_PCK         ((unsigned int) 0x1 <<  0) // (PMC) Processor Clock
#define AT91C_PMC_UDP         ((unsigned int) 0x1 <<  7) // (PMC) USB Device Port Clock
#define AT91C_PMC_PCK0        ((unsigned int) 0x1 <<  8) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK1        ((unsigned int) 0x1 <<  9) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK2        ((unsigned int) 0x1 << 10) // (PMC) Programmable Clock Output
#define AT91C_PMC_PCK3        ((unsigned int) 0x1 << 11) // (PMC) Programmable Clock Output
// -------- PMC_SCDR : (PMC Offset: 0x4) System Clock Disable Register -------- 
// -------- PMC_SCSR : (PMC Offset: 0x8) System Clock Status Register -------- 
// -------- CKGR_MOR : (PMC Offset: 0x20) Main Oscillator Register -------- 
// -------- CKGR_MCFR : (PMC Offset: 0x24) Main Clock Frequency Register -------- 
// -------- CKGR_PLLR : (PMC Offset: 0x2c) PLL B Register -------- 
// -------- PMC_MCKR : (PMC Offset: 0x30) Master Clock Register -------- 
#define AT91C_PMC_CSS         ((unsigned int) 0x3 <<  0) // (PMC) Programmable Clock Selection
#define 	AT91C_PMC_CSS_SLOW_CLK             ((unsigned int) 0x0) // (PMC) Slow Clock is selected
#define 	AT91C_PMC_CSS_MAIN_CLK             ((unsigned int) 0x1) // (PMC) Main Clock is selected
#define 	AT91C_PMC_CSS_PLL_CLK              ((unsigned int) 0x3) // (PMC) Clock from PLL is selected
#define AT91C_PMC_PRES        ((unsigned int) 0x7 <<  2) // (PMC) Programmable Clock Prescaler
#define 	AT91C_PMC_PRES_CLK                  ((unsigned int) 0x0 <<  2) // (PMC) Selected clock
#define 	AT91C_PMC_PRES_CLK_2                ((unsigned int) 0x1 <<  2) // (PMC) Selected clock divided by 2
#define 	AT91C_PMC_PRES_CLK_4                ((unsigned int) 0x2 <<  2) // (PMC) Selected clock divided by 4
#define 	AT91C_PMC_PRES_CLK_8                ((unsigned int) 0x3 <<  2) // (PMC) Selected clock divided by 8
#define 	AT91C_PMC_PRES_CLK_16               ((unsigned int) 0x4 <<  2) // (PMC) Selected clock divided by 16
#define 	AT91C_PMC_PRES_CLK_32               ((unsigned int) 0x5 <<  2) // (PMC) Selected clock divided by 32
#define 	AT91C_PMC_PRES_CLK_64               ((unsigned int) 0x6 <<  2) // (PMC) Selected clock divided by 64
// -------- PMC_PCKR : (PMC Offset: 0x40) Programmable Clock Register -------- 
// -------- PMC_IER : (PMC Offset: 0x60) PMC Interrupt Enable Register -------- 
#define AT91C_PMC_MOSCS       ((unsigned int) 0x1 <<  0) // (PMC) MOSC Status/Enable/Disable/Mask
#define AT91C_PMC_LOCK        ((unsigned int) 0x1 <<  2) // (PMC) PLL Status/Enable/Disable/Mask
#define AT91C_PMC_MCKRDY      ((unsigned int) 0x1 <<  3) // (PMC) MCK_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK0RDY     ((unsigned int) 0x1 <<  8) // (PMC) PCK0_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK1RDY     ((unsigned int) 0x1 <<  9) // (PMC) PCK1_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK2RDY     ((unsigned int) 0x1 << 10) // (PMC) PCK2_RDY Status/Enable/Disable/Mask
#define AT91C_PMC_PCK3RDY     ((unsigned int) 0x1 << 11) // (PMC) PCK3_RDY Status/Enable/Disable/Mask
// -------- PMC_IDR : (PMC Offset: 0x64) PMC Interrupt Disable Register -------- 
// -------- PMC_SR : (PMC Offset: 0x68) PMC Status Register -------- 
// -------- PMC_IMR : (PMC Offset: 0x6c) PMC Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Reset Controller Interface
// *****************************************************************************
typedef struct _AT91S_RSTC {
	AT91_REG	 RSTC_RCR; 	// Reset Control Register
	AT91_REG	 RSTC_RSR; 	// Reset Status Register
	AT91_REG	 RSTC_RMR; 	// Reset Mode Register
} AT91S_RSTC, *AT91PS_RSTC;

// -------- RSTC_RCR : (RSTC Offset: 0x0) Reset Control Register -------- 
#define AT91C_RSTC_PROCRST    ((unsigned int) 0x1 <<  0) // (RSTC) Processor Reset
#define AT91C_RSTC_PERRST     ((unsigned int) 0x1 <<  2) // (RSTC) Peripheral Reset
#define AT91C_RSTC_EXTRST     ((unsigned int) 0x1 <<  3) // (RSTC) External Reset
#define AT91C_RSTC_KEY        ((unsigned int) 0xFF << 24) // (RSTC) Password
// -------- RSTC_RSR : (RSTC Offset: 0x4) Reset Status Register -------- 
#define AT91C_RSTC_URSTS      ((unsigned int) 0x1 <<  0) // (RSTC) User Reset Status
#define AT91C_RSTC_BODSTS     ((unsigned int) 0x1 <<  1) // (RSTC) Brownout Detection Status
#define AT91C_RSTC_RSTTYP     ((unsigned int) 0x7 <<  8) // (RSTC) Reset Type
#define 	AT91C_RSTC_RSTTYP_POWERUP              ((unsigned int) 0x0 <<  8) // (RSTC) Power-up Reset. VDDCORE rising.
#define 	AT91C_RSTC_RSTTYP_WAKEUP               ((unsigned int) 0x1 <<  8) // (RSTC) WakeUp Reset. VDDCORE rising.
#define 	AT91C_RSTC_RSTTYP_WATCHDOG             ((unsigned int) 0x2 <<  8) // (RSTC) Watchdog Reset. Watchdog overflow occured.
#define 	AT91C_RSTC_RSTTYP_SOFTWARE             ((unsigned int) 0x3 <<  8) // (RSTC) Software Reset. Processor reset required by the software.
#define 	AT91C_RSTC_RSTTYP_USER                 ((unsigned int) 0x4 <<  8) // (RSTC) User Reset. NRST pin detected low.
#define 	AT91C_RSTC_RSTTYP_BROWNOUT             ((unsigned int) 0x5 <<  8) // (RSTC) Brownout Reset occured.
#define AT91C_RSTC_NRSTL      ((unsigned int) 0x1 << 16) // (RSTC) NRST pin level
#define AT91C_RSTC_SRCMP      ((unsigned int) 0x1 << 17) // (RSTC) Software Reset Command in Progress.
// -------- RSTC_RMR : (RSTC Offset: 0x8) Reset Mode Register -------- 
#define AT91C_RSTC_URSTEN     ((unsigned int) 0x1 <<  0) // (RSTC) User Reset Enable
#define AT91C_RSTC_URSTIEN    ((unsigned int) 0x1 <<  4) // (RSTC) User Reset Interrupt Enable
#define AT91C_RSTC_ERSTL      ((unsigned int) 0xF <<  8) // (RSTC) User Reset Enable
#define AT91C_RSTC_BODIEN     ((unsigned int) 0x1 << 16) // (RSTC) Brownout Detection Interrupt Enable

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Real Time Timer Controller Interface
// *****************************************************************************
typedef struct _AT91S_RTTC {
	AT91_REG	 RTTC_RTMR; 	// Real-time Mode Register
	AT91_REG	 RTTC_RTAR; 	// Real-time Alarm Register
	AT91_REG	 RTTC_RTVR; 	// Real-time Value Register
	AT91_REG	 RTTC_RTSR; 	// Real-time Status Register
} AT91S_RTTC, *AT91PS_RTTC;

// -------- RTTC_RTMR : (RTTC Offset: 0x0) Real-time Mode Register -------- 
#define AT91C_RTTC_RTPRES     ((unsigned int) 0xFFFF <<  0) // (RTTC) Real-time Timer Prescaler Value
#define AT91C_RTTC_ALMIEN     ((unsigned int) 0x1 << 16) // (RTTC) Alarm Interrupt Enable
#define AT91C_RTTC_RTTINCIEN  ((unsigned int) 0x1 << 17) // (RTTC) Real Time Timer Increment Interrupt Enable
#define AT91C_RTTC_RTTRST     ((unsigned int) 0x1 << 18) // (RTTC) Real Time Timer Restart
// -------- RTTC_RTAR : (RTTC Offset: 0x4) Real-time Alarm Register -------- 
#define AT91C_RTTC_ALMV       ((unsigned int) 0x0 <<  0) // (RTTC) Alarm Value
// -------- RTTC_RTVR : (RTTC Offset: 0x8) Current Real-time Value Register -------- 
#define AT91C_RTTC_CRTV       ((unsigned int) 0x0 <<  0) // (RTTC) Current Real-time Value
// -------- RTTC_RTSR : (RTTC Offset: 0xc) Real-time Status Register -------- 
#define AT91C_RTTC_ALMS       ((unsigned int) 0x1 <<  0) // (RTTC) Real-time Alarm Status
#define AT91C_RTTC_RTTINC     ((unsigned int) 0x1 <<  1) // (RTTC) Real-time Timer Increment

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Periodic Interval Timer Controller Interface
// *****************************************************************************
typedef struct _AT91S_PITC {
	AT91_REG	 PITC_PIMR; 	// Period Interval Mode Register
	AT91_REG	 PITC_PISR; 	// Period Interval Status Register
	AT91_REG	 PITC_PIVR; 	// Period Interval Value Register
	AT91_REG	 PITC_PIIR; 	// Period Interval Image Register
} AT91S_PITC, *AT91PS_PITC;

// -------- PITC_PIMR : (PITC Offset: 0x0) Periodic Interval Mode Register -------- 
#define AT91C_PITC_PIV        ((unsigned int) 0xFFFFF <<  0) // (PITC) Periodic Interval Value
#define AT91C_PITC_PITEN      ((unsigned int) 0x1 << 24) // (PITC) Periodic Interval Timer Enabled
#define AT91C_PITC_PITIEN     ((unsigned int) 0x1 << 25) // (PITC) Periodic Interval Timer Interrupt Enable
// -------- PITC_PISR : (PITC Offset: 0x4) Periodic Interval Status Register -------- 
#define AT91C_PITC_PITS       ((unsigned int) 0x1 <<  0) // (PITC) Periodic Interval Timer Status
// -------- PITC_PIVR : (PITC Offset: 0x8) Periodic Interval Value Register -------- 
#define AT91C_PITC_CPIV       ((unsigned int) 0xFFFFF <<  0) // (PITC) Current Periodic Interval Value
#define AT91C_PITC_PICNT      ((unsigned int) 0xFFF << 20) // (PITC) Periodic Interval Counter
// -------- PITC_PIIR : (PITC Offset: 0xc) Periodic Interval Image Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Watchdog Timer Controller Interface
// *****************************************************************************
typedef struct _AT91S_WDTC {
	AT91_REG	 WDTC_WDCR; 	// Watchdog Control Register
	AT91_REG	 WDTC_WDMR; 	// Watchdog Mode Register
	AT91_REG	 WDTC_WDSR; 	// Watchdog Status Register
} AT91S_WDTC, *AT91PS_WDTC;

// -------- WDTC_WDCR : (WDTC Offset: 0x0) Periodic Interval Image Register -------- 
#define AT91C_WDTC_WDRSTT     ((unsigned int) 0x1 <<  0) // (WDTC) Watchdog Restart
#define AT91C_WDTC_KEY        ((unsigned int) 0xFF << 24) // (WDTC) Watchdog KEY Password
// -------- WDTC_WDMR : (WDTC Offset: 0x4) Watchdog Mode Register -------- 
#define AT91C_WDTC_WDV        ((unsigned int) 0xFFF <<  0) // (WDTC) Watchdog Timer Restart
#define AT91C_WDTC_WDFIEN     ((unsigned int) 0x1 << 12) // (WDTC) Watchdog Fault Interrupt Enable
#define AT91C_WDTC_WDRSTEN    ((unsigned int) 0x1 << 13) // (WDTC) Watchdog Reset Enable
#define AT91C_WDTC_WDRPROC    ((unsigned int) 0x1 << 14) // (WDTC) Watchdog Timer Restart
#define AT91C_WDTC_WDDIS      ((unsigned int) 0x1 << 15) // (WDTC) Watchdog Disable
#define AT91C_WDTC_WDD        ((unsigned int) 0xFFF << 16) // (WDTC) Watchdog Delta Value
#define AT91C_WDTC_WDDBGHLT   ((unsigned int) 0x1 << 28) // (WDTC) Watchdog Debug Halt
#define AT91C_WDTC_WDIDLEHLT  ((unsigned int) 0x1 << 29) // (WDTC) Watchdog Idle Halt
// -------- WDTC_WDSR : (WDTC Offset: 0x8) Watchdog Status Register -------- 
#define AT91C_WDTC_WDUNF      ((unsigned int) 0x1 <<  0) // (WDTC) Watchdog Underflow
#define AT91C_WDTC_WDERR      ((unsigned int) 0x1 <<  1) // (WDTC) Watchdog Error

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Voltage Regulator Mode Controller Interface
// *****************************************************************************
typedef struct _AT91S_VREG {
	AT91_REG	 VREG_MR; 	// Voltage Regulator Mode Register
} AT91S_VREG, *AT91PS_VREG;

// -------- VREG_MR : (VREG Offset: 0x0) Voltage Regulator Mode Register -------- 
#define AT91C_VREG_PSTDBY     ((unsigned int) 0x1 <<  0) // (VREG) Voltage Regulator Power Standby Mode

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Memory Controller Interface
// *****************************************************************************
typedef struct _AT91S_MC {
	AT91_REG	 MC_RCR; 	// MC Remap Control Register
	AT91_REG	 MC_ASR; 	// MC Abort Status Register
	AT91_REG	 MC_AASR; 	// MC Abort Address Status Register
	AT91_REG	 Reserved0[21]; 	// 
	AT91_REG	 MC_FMR; 	// MC Flash Mode Register
	AT91_REG	 MC_FCR; 	// MC Flash Command Register
	AT91_REG	 MC_FSR; 	// MC Flash Status Register
} AT91S_MC, *AT91PS_MC;

// -------- MC_RCR : (MC Offset: 0x0) MC Remap Control Register -------- 
#define AT91C_MC_RCB          ((unsigned int) 0x1 <<  0) // (MC) Remap Command Bit
// -------- MC_ASR : (MC Offset: 0x4) MC Abort Status Register -------- 
#define AT91C_MC_UNDADD       ((unsigned int) 0x1 <<  0) // (MC) Undefined Addess Abort Status
#define AT91C_MC_MISADD       ((unsigned int) 0x1 <<  1) // (MC) Misaligned Addess Abort Status
#define AT91C_MC_ABTSZ        ((unsigned int) 0x3 <<  8) // (MC) Abort Size Status
#define 	AT91C_MC_ABTSZ_BYTE                 ((unsigned int) 0x0 <<  8) // (MC) Byte
#define 	AT91C_MC_ABTSZ_HWORD                ((unsigned int) 0x1 <<  8) // (MC) Half-word
#define 	AT91C_MC_ABTSZ_WORD                 ((unsigned int) 0x2 <<  8) // (MC) Word
#define AT91C_MC_ABTTYP       ((unsigned int) 0x3 << 10) // (MC) Abort Type Status
#define 	AT91C_MC_ABTTYP_DATAR                ((unsigned int) 0x0 << 10) // (MC) Data Read
#define 	AT91C_MC_ABTTYP_DATAW                ((unsigned int) 0x1 << 10) // (MC) Data Write
#define 	AT91C_MC_ABTTYP_FETCH                ((unsigned int) 0x2 << 10) // (MC) Code Fetch
#define AT91C_MC_MST0         ((unsigned int) 0x1 << 16) // (MC) Master 0 Abort Source
#define AT91C_MC_MST1         ((unsigned int) 0x1 << 17) // (MC) Master 1 Abort Source
#define AT91C_MC_SVMST0       ((unsigned int) 0x1 << 24) // (MC) Saved Master 0 Abort Source
#define AT91C_MC_SVMST1       ((unsigned int) 0x1 << 25) // (MC) Saved Master 1 Abort Source
// -------- MC_FMR : (MC Offset: 0x60) MC Flash Mode Register -------- 
#define AT91C_MC_FRDY         ((unsigned int) 0x1 <<  0) // (MC) Flash Ready
#define AT91C_MC_LOCKE        ((unsigned int) 0x1 <<  2) // (MC) Lock Error
#define AT91C_MC_PROGE        ((unsigned int) 0x1 <<  3) // (MC) Programming Error
#define AT91C_MC_NEBP         ((unsigned int) 0x1 <<  7) // (MC) No Erase Before Programming
#define AT91C_MC_FWS          ((unsigned int) 0x3 <<  8) // (MC) Flash Wait State
#define 	AT91C_MC_FWS_0FWS                 ((unsigned int) 0x0 <<  8) // (MC) 1 cycle for Read, 2 for Write operations
#define 	AT91C_MC_FWS_1FWS                 ((unsigned int) 0x1 <<  8) // (MC) 2 cycles for Read, 3 for Write operations
#define 	AT91C_MC_FWS_2FWS                 ((unsigned int) 0x2 <<  8) // (MC) 3 cycles for Read, 4 for Write operations
#define 	AT91C_MC_FWS_3FWS                 ((unsigned int) 0x3 <<  8) // (MC) 4 cycles for Read, 4 for Write operations
#define AT91C_MC_FMCN         ((unsigned int) 0xFF << 16) // (MC) Flash Microsecond Cycle Number
// -------- MC_FCR : (MC Offset: 0x64) MC Flash Command Register -------- 
#define AT91C_MC_FCMD         ((unsigned int) 0xF <<  0) // (MC) Flash Command
#define 	AT91C_MC_FCMD_START_PROG           ((unsigned int) 0x1) // (MC) Starts the programming of th epage specified by PAGEN.
#define 	AT91C_MC_FCMD_LOCK                 ((unsigned int) 0x2) // (MC) Starts a lock sequence of the sector defined by the bits 4 to 7 of the field PAGEN.
#define 	AT91C_MC_FCMD_PROG_AND_LOCK        ((unsigned int) 0x3) // (MC) The lock sequence automatically happens after the programming sequence is completed.
#define 	AT91C_MC_FCMD_UNLOCK               ((unsigned int) 0x4) // (MC) Starts an unlock sequence of the sector defined by the bits 4 to 7 of the field PAGEN.
#define 	AT91C_MC_FCMD_ERASE_ALL            ((unsigned int) 0x8) // (MC) Starts the erase of the entire flash.If at least a page is locked, the command is cancelled.
#define 	AT91C_MC_FCMD_SET_GP_NVM           ((unsigned int) 0xB) // (MC) Set General Purpose NVM bits.
#define 	AT91C_MC_FCMD_CLR_GP_NVM           ((unsigned int) 0xD) // (MC) Clear General Purpose NVM bits.
#define 	AT91C_MC_FCMD_SET_SECURITY         ((unsigned int) 0xF) // (MC) Set Security Bit.
#define AT91C_MC_PAGEN        ((unsigned int) 0x3FF <<  8) // (MC) Page Number
#define AT91C_MC_KEY          ((unsigned int) 0xFF << 24) // (MC) Writing Protect Key
// -------- MC_FSR : (MC Offset: 0x68) MC Flash Command Register -------- 
#define AT91C_MC_SECURITY     ((unsigned int) 0x1 <<  4) // (MC) Security Bit Status
#define AT91C_MC_GPNVM0       ((unsigned int) 0x1 <<  8) // (MC) Sector 0 Lock Status
#define AT91C_MC_GPNVM1       ((unsigned int) 0x1 <<  9) // (MC) Sector 1 Lock Status
#define AT91C_MC_GPNVM2       ((unsigned int) 0x1 << 10) // (MC) Sector 2 Lock Status
#define AT91C_MC_GPNVM3       ((unsigned int) 0x1 << 11) // (MC) Sector 3 Lock Status
#define AT91C_MC_GPNVM4       ((unsigned int) 0x1 << 12) // (MC) Sector 4 Lock Status
#define AT91C_MC_GPNVM5       ((unsigned int) 0x1 << 13) // (MC) Sector 5 Lock Status
#define AT91C_MC_GPNVM6       ((unsigned int) 0x1 << 14) // (MC) Sector 6 Lock Status
#define AT91C_MC_GPNVM7       ((unsigned int) 0x1 << 15) // (MC) Sector 7 Lock Status
#define AT91C_MC_LOCKS0       ((unsigned int) 0x1 << 16) // (MC) Sector 0 Lock Status
#define AT91C_MC_LOCKS1       ((unsigned int) 0x1 << 17) // (MC) Sector 1 Lock Status
#define AT91C_MC_LOCKS2       ((unsigned int) 0x1 << 18) // (MC) Sector 2 Lock Status
#define AT91C_MC_LOCKS3       ((unsigned int) 0x1 << 19) // (MC) Sector 3 Lock Status
#define AT91C_MC_LOCKS4       ((unsigned int) 0x1 << 20) // (MC) Sector 4 Lock Status
#define AT91C_MC_LOCKS5       ((unsigned int) 0x1 << 21) // (MC) Sector 5 Lock Status
#define AT91C_MC_LOCKS6       ((unsigned int) 0x1 << 22) // (MC) Sector 6 Lock Status
#define AT91C_MC_LOCKS7       ((unsigned int) 0x1 << 23) // (MC) Sector 7 Lock Status
#define AT91C_MC_LOCKS8       ((unsigned int) 0x1 << 24) // (MC) Sector 8 Lock Status
#define AT91C_MC_LOCKS9       ((unsigned int) 0x1 << 25) // (MC) Sector 9 Lock Status
#define AT91C_MC_LOCKS10      ((unsigned int) 0x1 << 26) // (MC) Sector 10 Lock Status
#define AT91C_MC_LOCKS11      ((unsigned int) 0x1 << 27) // (MC) Sector 11 Lock Status
#define AT91C_MC_LOCKS12      ((unsigned int) 0x1 << 28) // (MC) Sector 12 Lock Status
#define AT91C_MC_LOCKS13      ((unsigned int) 0x1 << 29) // (MC) Sector 13 Lock Status
#define AT91C_MC_LOCKS14      ((unsigned int) 0x1 << 30) // (MC) Sector 14 Lock Status
#define AT91C_MC_LOCKS15      ((unsigned int) 0x1 << 31) // (MC) Sector 15 Lock Status

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Serial Parallel Interface
// *****************************************************************************
typedef struct _AT91S_SPI {
	AT91_REG	 SPI_CR; 	// Control Register
	AT91_REG	 SPI_MR; 	// Mode Register
	AT91_REG	 SPI_RDR; 	// Receive Data Register
	AT91_REG	 SPI_TDR; 	// Transmit Data Register
	AT91_REG	 SPI_SR; 	// Status Register
	AT91_REG	 SPI_IER; 	// Interrupt Enable Register
	AT91_REG	 SPI_IDR; 	// Interrupt Disable Register
	AT91_REG	 SPI_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved0[4]; 	// 
	AT91_REG	 SPI_CSR[4]; 	// Chip Select Register
	AT91_REG	 Reserved1[48]; 	// 
	AT91_REG	 SPI_RPR; 	// Receive Pointer Register
	AT91_REG	 SPI_RCR; 	// Receive Counter Register
	AT91_REG	 SPI_TPR; 	// Transmit Pointer Register
	AT91_REG	 SPI_TCR; 	// Transmit Counter Register
	AT91_REG	 SPI_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 SPI_RNCR; 	// Receive Next Counter Register
	AT91_REG	 SPI_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 SPI_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 SPI_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 SPI_PTSR; 	// PDC Transfer Status Register
} AT91S_SPI, *AT91PS_SPI;

// -------- SPI_CR : (SPI Offset: 0x0) SPI Control Register -------- 
#define AT91C_SPI_SPIEN       ((unsigned int) 0x1 <<  0) // (SPI) SPI Enable
#define AT91C_SPI_SPIDIS      ((unsigned int) 0x1 <<  1) // (SPI) SPI Disable
#define AT91C_SPI_SWRST       ((unsigned int) 0x1 <<  7) // (SPI) SPI Software reset
#define AT91C_SPI_LASTXFER    ((unsigned int) 0x1 << 24) // (SPI) SPI Last Transfer
// -------- SPI_MR : (SPI Offset: 0x4) SPI Mode Register -------- 
#define AT91C_SPI_MSTR        ((unsigned int) 0x1 <<  0) // (SPI) Master/Slave Mode
#define AT91C_SPI_PS          ((unsigned int) 0x1 <<  1) // (SPI) Peripheral Select
#define 	AT91C_SPI_PS_FIXED                ((unsigned int) 0x0 <<  1) // (SPI) Fixed Peripheral Select
#define 	AT91C_SPI_PS_VARIABLE             ((unsigned int) 0x1 <<  1) // (SPI) Variable Peripheral Select
#define AT91C_SPI_PCSDEC      ((unsigned int) 0x1 <<  2) // (SPI) Chip Select Decode
#define AT91C_SPI_FDIV        ((unsigned int) 0x1 <<  3) // (SPI) Clock Selection
#define AT91C_SPI_MODFDIS     ((unsigned int) 0x1 <<  4) // (SPI) Mode Fault Detection
#define AT91C_SPI_LLB         ((unsigned int) 0x1 <<  7) // (SPI) Clock Selection
#define AT91C_SPI_PCS         ((unsigned int) 0xF << 16) // (SPI) Peripheral Chip Select
#define AT91C_SPI_DLYBCS      ((unsigned int) 0xFF << 24) // (SPI) Delay Between Chip Selects
// -------- SPI_RDR : (SPI Offset: 0x8) Receive Data Register -------- 
#define AT91C_SPI_RD          ((unsigned int) 0xFFFF <<  0) // (SPI) Receive Data
#define AT91C_SPI_RPCS        ((unsigned int) 0xF << 16) // (SPI) Peripheral Chip Select Status
// -------- SPI_TDR : (SPI Offset: 0xc) Transmit Data Register -------- 
#define AT91C_SPI_TD          ((unsigned int) 0xFFFF <<  0) // (SPI) Transmit Data
#define AT91C_SPI_TPCS        ((unsigned int) 0xF << 16) // (SPI) Peripheral Chip Select Status
// -------- SPI_SR : (SPI Offset: 0x10) Status Register -------- 
#define AT91C_SPI_RDRF        ((unsigned int) 0x1 <<  0) // (SPI) Receive Data Register Full
#define AT91C_SPI_TDRE        ((unsigned int) 0x1 <<  1) // (SPI) Transmit Data Register Empty
#define AT91C_SPI_MODF        ((unsigned int) 0x1 <<  2) // (SPI) Mode Fault Error
#define AT91C_SPI_OVRES       ((unsigned int) 0x1 <<  3) // (SPI) Overrun Error Status
#define AT91C_SPI_ENDRX       ((unsigned int) 0x1 <<  4) // (SPI) End of Receiver Transfer
#define AT91C_SPI_ENDTX       ((unsigned int) 0x1 <<  5) // (SPI) End of Receiver Transfer
#define AT91C_SPI_RXBUFF      ((unsigned int) 0x1 <<  6) // (SPI) RXBUFF Interrupt
#define AT91C_SPI_TXBUFE      ((unsigned int) 0x1 <<  7) // (SPI) TXBUFE Interrupt
#define AT91C_SPI_NSSR        ((unsigned int) 0x1 <<  8) // (SPI) NSSR Interrupt
#define AT91C_SPI_TXEMPTY     ((unsigned int) 0x1 <<  9) // (SPI) TXEMPTY Interrupt
#define AT91C_SPI_SPIENS      ((unsigned int) 0x1 << 16) // (SPI) Enable Status
// -------- SPI_IER : (SPI Offset: 0x14) Interrupt Enable Register -------- 
// -------- SPI_IDR : (SPI Offset: 0x18) Interrupt Disable Register -------- 
// -------- SPI_IMR : (SPI Offset: 0x1c) Interrupt Mask Register -------- 
// -------- SPI_CSR : (SPI Offset: 0x30) Chip Select Register -------- 
#define AT91C_SPI_CPOL        ((unsigned int) 0x1 <<  0) // (SPI) Clock Polarity
#define AT91C_SPI_NCPHA       ((unsigned int) 0x1 <<  1) // (SPI) Clock Phase
#define AT91C_SPI_CSAAT       ((unsigned int) 0x1 <<  3) // (SPI) Chip Select Active After Transfer
#define AT91C_SPI_BITS        ((unsigned int) 0xF <<  4) // (SPI) Bits Per Transfer
#define 	AT91C_SPI_BITS_8                    ((unsigned int) 0x0 <<  4) // (SPI) 8 Bits Per transfer
#define 	AT91C_SPI_BITS_9                    ((unsigned int) 0x1 <<  4) // (SPI) 9 Bits Per transfer
#define 	AT91C_SPI_BITS_10                   ((unsigned int) 0x2 <<  4) // (SPI) 10 Bits Per transfer
#define 	AT91C_SPI_BITS_11                   ((unsigned int) 0x3 <<  4) // (SPI) 11 Bits Per transfer
#define 	AT91C_SPI_BITS_12                   ((unsigned int) 0x4 <<  4) // (SPI) 12 Bits Per transfer
#define 	AT91C_SPI_BITS_13                   ((unsigned int) 0x5 <<  4) // (SPI) 13 Bits Per transfer
#define 	AT91C_SPI_BITS_14                   ((unsigned int) 0x6 <<  4) // (SPI) 14 Bits Per transfer
#define 	AT91C_SPI_BITS_15                   ((unsigned int) 0x7 <<  4) // (SPI) 15 Bits Per transfer
#define 	AT91C_SPI_BITS_16                   ((unsigned int) 0x8 <<  4) // (SPI) 16 Bits Per transfer
#define AT91C_SPI_SCBR        ((unsigned int) 0xFF <<  8) // (SPI) Serial Clock Baud Rate
#define AT91C_SPI_DLYBS       ((unsigned int) 0xFF << 16) // (SPI) Delay Before SPCK
#define AT91C_SPI_DLYBCT      ((unsigned int) 0xFF << 24) // (SPI) Delay Between Consecutive Transfers

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Usart
// *****************************************************************************
typedef struct _AT91S_USART {
	AT91_REG	 US_CR; 	// Control Register
	AT91_REG	 US_MR; 	// Mode Register
	AT91_REG	 US_IER; 	// Interrupt Enable Register
	AT91_REG	 US_IDR; 	// Interrupt Disable Register
	AT91_REG	 US_IMR; 	// Interrupt Mask Register
	AT91_REG	 US_CSR; 	// Channel Status Register
	AT91_REG	 US_RHR; 	// Receiver Holding Register
	AT91_REG	 US_THR; 	// Transmitter Holding Register
	AT91_REG	 US_BRGR; 	// Baud Rate Generator Register
	AT91_REG	 US_RTOR; 	// Receiver Time-out Register
	AT91_REG	 US_TTGR; 	// Transmitter Time-guard Register
	AT91_REG	 Reserved0[5]; 	// 
	AT91_REG	 US_FIDI; 	// FI_DI_Ratio Register
	AT91_REG	 US_NER; 	// Nb Errors Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 US_IF; 	// IRDA_FILTER Register
	AT91_REG	 Reserved2[44]; 	// 
	AT91_REG	 US_RPR; 	// Receive Pointer Register
	AT91_REG	 US_RCR; 	// Receive Counter Register
	AT91_REG	 US_TPR; 	// Transmit Pointer Register
	AT91_REG	 US_TCR; 	// Transmit Counter Register
	AT91_REG	 US_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 US_RNCR; 	// Receive Next Counter Register
	AT91_REG	 US_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 US_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 US_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 US_PTSR; 	// PDC Transfer Status Register
} AT91S_USART, *AT91PS_USART;

// -------- US_CR : (USART Offset: 0x0) Debug Unit Control Register -------- 
#define AT91C_US_STTBRK       ((unsigned int) 0x1 <<  9) // (USART) Start Break
#define AT91C_US_STPBRK       ((unsigned int) 0x1 << 10) // (USART) Stop Break
#define AT91C_US_STTTO        ((unsigned int) 0x1 << 11) // (USART) Start Time-out
#define AT91C_US_SENDA        ((unsigned int) 0x1 << 12) // (USART) Send Address
#define AT91C_US_RSTIT        ((unsigned int) 0x1 << 13) // (USART) Reset Iterations
#define AT91C_US_RSTNACK      ((unsigned int) 0x1 << 14) // (USART) Reset Non Acknowledge
#define AT91C_US_RETTO        ((unsigned int) 0x1 << 15) // (USART) Rearm Time-out
#define AT91C_US_DTREN        ((unsigned int) 0x1 << 16) // (USART) Data Terminal ready Enable
#define AT91C_US_DTRDIS       ((unsigned int) 0x1 << 17) // (USART) Data Terminal ready Disable
#define AT91C_US_RTSEN        ((unsigned int) 0x1 << 18) // (USART) Request to Send enable
#define AT91C_US_RTSDIS       ((unsigned int) 0x1 << 19) // (USART) Request to Send Disable
// -------- US_MR : (USART Offset: 0x4) Debug Unit Mode Register -------- 
#define AT91C_US_USMODE       ((unsigned int) 0xF <<  0) // (USART) Usart mode
#define 	AT91C_US_USMODE_NORMAL               ((unsigned int) 0x0) // (USART) Normal
#define 	AT91C_US_USMODE_RS485                ((unsigned int) 0x1) // (USART) RS485
#define 	AT91C_US_USMODE_HWHSH                ((unsigned int) 0x2) // (USART) Hardware Handshaking
#define 	AT91C_US_USMODE_MODEM                ((unsigned int) 0x3) // (USART) Modem
#define 	AT91C_US_USMODE_ISO7816_0            ((unsigned int) 0x4) // (USART) ISO7816 protocol: T = 0
#define 	AT91C_US_USMODE_ISO7816_1            ((unsigned int) 0x6) // (USART) ISO7816 protocol: T = 1
#define 	AT91C_US_USMODE_IRDA                 ((unsigned int) 0x8) // (USART) IrDA
#define 	AT91C_US_USMODE_SWHSH                ((unsigned int) 0xC) // (USART) Software Handshaking
#define AT91C_US_CLKS         ((unsigned int) 0x3 <<  4) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CLKS_CLOCK                ((unsigned int) 0x0 <<  4) // (USART) Clock
#define 	AT91C_US_CLKS_FDIV1                ((unsigned int) 0x1 <<  4) // (USART) fdiv1
#define 	AT91C_US_CLKS_SLOW                 ((unsigned int) 0x2 <<  4) // (USART) slow_clock (ARM)
#define 	AT91C_US_CLKS_EXT                  ((unsigned int) 0x3 <<  4) // (USART) External (SCK)
#define AT91C_US_CHRL         ((unsigned int) 0x3 <<  6) // (USART) Clock Selection (Baud Rate generator Input Clock
#define 	AT91C_US_CHRL_5_BITS               ((unsigned int) 0x0 <<  6) // (USART) Character Length: 5 bits
#define 	AT91C_US_CHRL_6_BITS               ((unsigned int) 0x1 <<  6) // (USART) Character Length: 6 bits
#define 	AT91C_US_CHRL_7_BITS               ((unsigned int) 0x2 <<  6) // (USART) Character Length: 7 bits
#define 	AT91C_US_CHRL_8_BITS               ((unsigned int) 0x3 <<  6) // (USART) Character Length: 8 bits
#define AT91C_US_SYNC         ((unsigned int) 0x1 <<  8) // (USART) Synchronous Mode Select
#define AT91C_US_NBSTOP       ((unsigned int) 0x3 << 12) // (USART) Number of Stop bits
#define 	AT91C_US_NBSTOP_1_BIT                ((unsigned int) 0x0 << 12) // (USART) 1 stop bit
#define 	AT91C_US_NBSTOP_15_BIT               ((unsigned int) 0x1 << 12) // (USART) Asynchronous (SYNC=0) 2 stop bits Synchronous (SYNC=1) 2 stop bits
#define 	AT91C_US_NBSTOP_2_BIT                ((unsigned int) 0x2 << 12) // (USART) 2 stop bits
#define AT91C_US_MSBF         ((unsigned int) 0x1 << 16) // (USART) Bit Order
#define AT91C_US_MODE9        ((unsigned int) 0x1 << 17) // (USART) 9-bit Character length
#define AT91C_US_CKLO         ((unsigned int) 0x1 << 18) // (USART) Clock Output Select
#define AT91C_US_OVER         ((unsigned int) 0x1 << 19) // (USART) Over Sampling Mode
#define AT91C_US_INACK        ((unsigned int) 0x1 << 20) // (USART) Inhibit Non Acknowledge
#define AT91C_US_DSNACK       ((unsigned int) 0x1 << 21) // (USART) Disable Successive NACK
#define AT91C_US_MAX_ITER     ((unsigned int) 0x1 << 24) // (USART) Number of Repetitions
#define AT91C_US_FILTER       ((unsigned int) 0x1 << 28) // (USART) Receive Line Filter
// -------- US_IER : (USART Offset: 0x8) Debug Unit Interrupt Enable Register -------- 
#define AT91C_US_RXBRK        ((unsigned int) 0x1 <<  2) // (USART) Break Received/End of Break
#define AT91C_US_TIMEOUT      ((unsigned int) 0x1 <<  8) // (USART) Receiver Time-out
#define AT91C_US_ITERATION    ((unsigned int) 0x1 << 10) // (USART) Max number of Repetitions Reached
#define AT91C_US_NACK         ((unsigned int) 0x1 << 13) // (USART) Non Acknowledge
#define AT91C_US_RIIC         ((unsigned int) 0x1 << 16) // (USART) Ring INdicator Input Change Flag
#define AT91C_US_DSRIC        ((unsigned int) 0x1 << 17) // (USART) Data Set Ready Input Change Flag
#define AT91C_US_DCDIC        ((unsigned int) 0x1 << 18) // (USART) Data Carrier Flag
#define AT91C_US_CTSIC        ((unsigned int) 0x1 << 19) // (USART) Clear To Send Input Change Flag
// -------- US_IDR : (USART Offset: 0xc) Debug Unit Interrupt Disable Register -------- 
// -------- US_IMR : (USART Offset: 0x10) Debug Unit Interrupt Mask Register -------- 
// -------- US_CSR : (USART Offset: 0x14) Debug Unit Channel Status Register -------- 
#define AT91C_US_RI           ((unsigned int) 0x1 << 20) // (USART) Image of RI Input
#define AT91C_US_DSR          ((unsigned int) 0x1 << 21) // (USART) Image of DSR Input
#define AT91C_US_DCD          ((unsigned int) 0x1 << 22) // (USART) Image of DCD Input
#define AT91C_US_CTS          ((unsigned int) 0x1 << 23) // (USART) Image of CTS Input

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Synchronous Serial Controller Interface
// *****************************************************************************
typedef struct _AT91S_SSC {
	AT91_REG	 SSC_CR; 	// Control Register
	AT91_REG	 SSC_CMR; 	// Clock Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 SSC_RCMR; 	// Receive Clock ModeRegister
	AT91_REG	 SSC_RFMR; 	// Receive Frame Mode Register
	AT91_REG	 SSC_TCMR; 	// Transmit Clock Mode Register
	AT91_REG	 SSC_TFMR; 	// Transmit Frame Mode Register
	AT91_REG	 SSC_RHR; 	// Receive Holding Register
	AT91_REG	 SSC_THR; 	// Transmit Holding Register
	AT91_REG	 Reserved1[2]; 	// 
	AT91_REG	 SSC_RSHR; 	// Receive Sync Holding Register
	AT91_REG	 SSC_TSHR; 	// Transmit Sync Holding Register
	AT91_REG	 Reserved2[2]; 	// 
	AT91_REG	 SSC_SR; 	// Status Register
	AT91_REG	 SSC_IER; 	// Interrupt Enable Register
	AT91_REG	 SSC_IDR; 	// Interrupt Disable Register
	AT91_REG	 SSC_IMR; 	// Interrupt Mask Register
	AT91_REG	 Reserved3[44]; 	// 
	AT91_REG	 SSC_RPR; 	// Receive Pointer Register
	AT91_REG	 SSC_RCR; 	// Receive Counter Register
	AT91_REG	 SSC_TPR; 	// Transmit Pointer Register
	AT91_REG	 SSC_TCR; 	// Transmit Counter Register
	AT91_REG	 SSC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 SSC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 SSC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 SSC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 SSC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 SSC_PTSR; 	// PDC Transfer Status Register
} AT91S_SSC, *AT91PS_SSC;

// -------- SSC_CR : (SSC Offset: 0x0) SSC Control Register -------- 
#define AT91C_SSC_RXEN        ((unsigned int) 0x1 <<  0) // (SSC) Receive Enable
#define AT91C_SSC_RXDIS       ((unsigned int) 0x1 <<  1) // (SSC) Receive Disable
#define AT91C_SSC_TXEN        ((unsigned int) 0x1 <<  8) // (SSC) Transmit Enable
#define AT91C_SSC_TXDIS       ((unsigned int) 0x1 <<  9) // (SSC) Transmit Disable
#define AT91C_SSC_SWRST       ((unsigned int) 0x1 << 15) // (SSC) Software Reset
// -------- SSC_RCMR : (SSC Offset: 0x10) SSC Receive Clock Mode Register -------- 
#define AT91C_SSC_CKS         ((unsigned int) 0x3 <<  0) // (SSC) Receive/Transmit Clock Selection
#define 	AT91C_SSC_CKS_DIV                  ((unsigned int) 0x0) // (SSC) Divided Clock
#define 	AT91C_SSC_CKS_TK                   ((unsigned int) 0x1) // (SSC) TK Clock signal
#define 	AT91C_SSC_CKS_RK                   ((unsigned int) 0x2) // (SSC) RK pin
#define AT91C_SSC_CKO         ((unsigned int) 0x7 <<  2) // (SSC) Receive/Transmit Clock Output Mode Selection
#define 	AT91C_SSC_CKO_NONE                 ((unsigned int) 0x0 <<  2) // (SSC) Receive/Transmit Clock Output Mode: None RK pin: Input-only
#define 	AT91C_SSC_CKO_CONTINOUS            ((unsigned int) 0x1 <<  2) // (SSC) Continuous Receive/Transmit Clock RK pin: Output
#define 	AT91C_SSC_CKO_DATA_TX              ((unsigned int) 0x2 <<  2) // (SSC) Receive/Transmit Clock only during data transfers RK pin: Output
#define AT91C_SSC_CKI         ((unsigned int) 0x1 <<  5) // (SSC) Receive/Transmit Clock Inversion
#define AT91C_SSC_START       ((unsigned int) 0xF <<  8) // (SSC) Receive/Transmit Start Selection
#define 	AT91C_SSC_START_CONTINOUS            ((unsigned int) 0x0 <<  8) // (SSC) Continuous, as soon as the receiver is enabled, and immediately after the end of transfer of the previous data.
#define 	AT91C_SSC_START_TX                   ((unsigned int) 0x1 <<  8) // (SSC) Transmit/Receive start
#define 	AT91C_SSC_START_LOW_RF               ((unsigned int) 0x2 <<  8) // (SSC) Detection of a low level on RF input
#define 	AT91C_SSC_START_HIGH_RF              ((unsigned int) 0x3 <<  8) // (SSC) Detection of a high level on RF input
#define 	AT91C_SSC_START_FALL_RF              ((unsigned int) 0x4 <<  8) // (SSC) Detection of a falling edge on RF input
#define 	AT91C_SSC_START_RISE_RF              ((unsigned int) 0x5 <<  8) // (SSC) Detection of a rising edge on RF input
#define 	AT91C_SSC_START_LEVEL_RF             ((unsigned int) 0x6 <<  8) // (SSC) Detection of any level change on RF input
#define 	AT91C_SSC_START_EDGE_RF              ((unsigned int) 0x7 <<  8) // (SSC) Detection of any edge on RF input
#define 	AT91C_SSC_START_0                    ((unsigned int) 0x8 <<  8) // (SSC) Compare 0
#define AT91C_SSC_STTDLY      ((unsigned int) 0xFF << 16) // (SSC) Receive/Transmit Start Delay
#define AT91C_SSC_PERIOD      ((unsigned int) 0xFF << 24) // (SSC) Receive/Transmit Period Divider Selection
// -------- SSC_RFMR : (SSC Offset: 0x14) SSC Receive Frame Mode Register -------- 
#define AT91C_SSC_DATLEN      ((unsigned int) 0x1F <<  0) // (SSC) Data Length
#define AT91C_SSC_LOOP        ((unsigned int) 0x1 <<  5) // (SSC) Loop Mode
#define AT91C_SSC_MSBF        ((unsigned int) 0x1 <<  7) // (SSC) Most Significant Bit First
#define AT91C_SSC_DATNB       ((unsigned int) 0xF <<  8) // (SSC) Data Number per Frame
#define AT91C_SSC_FSLEN       ((unsigned int) 0xF << 16) // (SSC) Receive/Transmit Frame Sync length
#define AT91C_SSC_FSOS        ((unsigned int) 0x7 << 20) // (SSC) Receive/Transmit Frame Sync Output Selection
#define 	AT91C_SSC_FSOS_NONE                 ((unsigned int) 0x0 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: None RK pin Input-only
#define 	AT91C_SSC_FSOS_NEGATIVE             ((unsigned int) 0x1 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Negative Pulse
#define 	AT91C_SSC_FSOS_POSITIVE             ((unsigned int) 0x2 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Positive Pulse
#define 	AT91C_SSC_FSOS_LOW                  ((unsigned int) 0x3 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Driver Low during data transfer
#define 	AT91C_SSC_FSOS_HIGH                 ((unsigned int) 0x4 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Driver High during data transfer
#define 	AT91C_SSC_FSOS_TOGGLE               ((unsigned int) 0x5 << 20) // (SSC) Selected Receive/Transmit Frame Sync Signal: Toggling at each start of data transfer
#define AT91C_SSC_FSEDGE      ((unsigned int) 0x1 << 24) // (SSC) Frame Sync Edge Detection
// -------- SSC_TCMR : (SSC Offset: 0x18) SSC Transmit Clock Mode Register -------- 
// -------- SSC_TFMR : (SSC Offset: 0x1c) SSC Transmit Frame Mode Register -------- 
#define AT91C_SSC_DATDEF      ((unsigned int) 0x1 <<  5) // (SSC) Data Default Value
#define AT91C_SSC_FSDEN       ((unsigned int) 0x1 << 23) // (SSC) Frame Sync Data Enable
// -------- SSC_SR : (SSC Offset: 0x40) SSC Status Register -------- 
#define AT91C_SSC_TXRDY       ((unsigned int) 0x1 <<  0) // (SSC) Transmit Ready
#define AT91C_SSC_TXEMPTY     ((unsigned int) 0x1 <<  1) // (SSC) Transmit Empty
#define AT91C_SSC_ENDTX       ((unsigned int) 0x1 <<  2) // (SSC) End Of Transmission
#define AT91C_SSC_TXBUFE      ((unsigned int) 0x1 <<  3) // (SSC) Transmit Buffer Empty
#define AT91C_SSC_RXRDY       ((unsigned int) 0x1 <<  4) // (SSC) Receive Ready
#define AT91C_SSC_OVRUN       ((unsigned int) 0x1 <<  5) // (SSC) Receive Overrun
#define AT91C_SSC_ENDRX       ((unsigned int) 0x1 <<  6) // (SSC) End of Reception
#define AT91C_SSC_RXBUFF      ((unsigned int) 0x1 <<  7) // (SSC) Receive Buffer Full
#define AT91C_SSC_TXSYN       ((unsigned int) 0x1 << 10) // (SSC) Transmit Sync
#define AT91C_SSC_RXSYN       ((unsigned int) 0x1 << 11) // (SSC) Receive Sync
#define AT91C_SSC_TXENA       ((unsigned int) 0x1 << 16) // (SSC) Transmit Enable
#define AT91C_SSC_RXENA       ((unsigned int) 0x1 << 17) // (SSC) Receive Enable
// -------- SSC_IER : (SSC Offset: 0x44) SSC Interrupt Enable Register -------- 
// -------- SSC_IDR : (SSC Offset: 0x48) SSC Interrupt Disable Register -------- 
// -------- SSC_IMR : (SSC Offset: 0x4c) SSC Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Two-wire Interface
// *****************************************************************************
typedef struct _AT91S_TWI {
	AT91_REG	 TWI_CR; 	// Control Register
	AT91_REG	 TWI_MMR; 	// Master Mode Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 TWI_IADR; 	// Internal Address Register
	AT91_REG	 TWI_CWGR; 	// Clock Waveform Generator Register
	AT91_REG	 Reserved1[3]; 	// 
	AT91_REG	 TWI_SR; 	// Status Register
	AT91_REG	 TWI_IER; 	// Interrupt Enable Register
	AT91_REG	 TWI_IDR; 	// Interrupt Disable Register
	AT91_REG	 TWI_IMR; 	// Interrupt Mask Register
	AT91_REG	 TWI_RHR; 	// Receive Holding Register
	AT91_REG	 TWI_THR; 	// Transmit Holding Register
} AT91S_TWI, *AT91PS_TWI;

// -------- TWI_CR : (TWI Offset: 0x0) TWI Control Register -------- 
#define AT91C_TWI_START       ((unsigned int) 0x1 <<  0) // (TWI) Send a START Condition
#define AT91C_TWI_STOP        ((unsigned int) 0x1 <<  1) // (TWI) Send a STOP Condition
#define AT91C_TWI_MSEN        ((unsigned int) 0x1 <<  2) // (TWI) TWI Master Transfer Enabled
#define AT91C_TWI_MSDIS       ((unsigned int) 0x1 <<  3) // (TWI) TWI Master Transfer Disabled
#define AT91C_TWI_SWRST       ((unsigned int) 0x1 <<  7) // (TWI) Software Reset
// -------- TWI_MMR : (TWI Offset: 0x4) TWI Master Mode Register -------- 
#define AT91C_TWI_IADRSZ      ((unsigned int) 0x3 <<  8) // (TWI) Internal Device Address Size
#define 	AT91C_TWI_IADRSZ_NO                   ((unsigned int) 0x0 <<  8) // (TWI) No internal device address
#define 	AT91C_TWI_IADRSZ_1_BYTE               ((unsigned int) 0x1 <<  8) // (TWI) One-byte internal device address
#define 	AT91C_TWI_IADRSZ_2_BYTE               ((unsigned int) 0x2 <<  8) // (TWI) Two-byte internal device address
#define 	AT91C_TWI_IADRSZ_3_BYTE               ((unsigned int) 0x3 <<  8) // (TWI) Three-byte internal device address
#define AT91C_TWI_MREAD       ((unsigned int) 0x1 << 12) // (TWI) Master Read Direction
#define AT91C_TWI_DADR        ((unsigned int) 0x7F << 16) // (TWI) Device Address
// -------- TWI_CWGR : (TWI Offset: 0x10) TWI Clock Waveform Generator Register -------- 
#define AT91C_TWI_CLDIV       ((unsigned int) 0xFF <<  0) // (TWI) Clock Low Divider
#define AT91C_TWI_CHDIV       ((unsigned int) 0xFF <<  8) // (TWI) Clock High Divider
#define AT91C_TWI_CKDIV       ((unsigned int) 0x7 << 16) // (TWI) Clock Divider
// -------- TWI_SR : (TWI Offset: 0x20) TWI Status Register -------- 
#define AT91C_TWI_TXCOMP      ((unsigned int) 0x1 <<  0) // (TWI) Transmission Completed
#define AT91C_TWI_RXRDY       ((unsigned int) 0x1 <<  1) // (TWI) Receive holding register ReaDY
#define AT91C_TWI_TXRDY       ((unsigned int) 0x1 <<  2) // (TWI) Transmit holding register ReaDY
#define AT91C_TWI_OVRE        ((unsigned int) 0x1 <<  6) // (TWI) Overrun Error
#define AT91C_TWI_UNRE        ((unsigned int) 0x1 <<  7) // (TWI) Underrun Error
#define AT91C_TWI_NACK        ((unsigned int) 0x1 <<  8) // (TWI) Not Acknowledged
// -------- TWI_IER : (TWI Offset: 0x24) TWI Interrupt Enable Register -------- 
// -------- TWI_IDR : (TWI Offset: 0x28) TWI Interrupt Disable Register -------- 
// -------- TWI_IMR : (TWI Offset: 0x2c) TWI Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR PWMC Channel Interface
// *****************************************************************************
typedef struct _AT91S_PWMC_CH {
	AT91_REG	 PWMC_CMR; 	// Channel Mode Register
	AT91_REG	 PWMC_CDTYR; 	// Channel Duty Cycle Register
	AT91_REG	 PWMC_CPRDR; 	// Channel Period Register
	AT91_REG	 PWMC_CCNTR; 	// Channel Counter Register
	AT91_REG	 PWMC_CUPDR; 	// Channel Update Register
	AT91_REG	 PWMC_Reserved[3]; 	// Reserved
} AT91S_PWMC_CH, *AT91PS_PWMC_CH;

// -------- PWMC_CMR : (PWMC_CH Offset: 0x0) PWMC Channel Mode Register -------- 
#define AT91C_PWMC_CPRE       ((unsigned int) 0xF <<  0) // (PWMC_CH) Channel Pre-scaler : PWMC_CLKx
#define 	AT91C_PWMC_CPRE_MCK                  ((unsigned int) 0x0) // (PWMC_CH) 
#define 	AT91C_PWMC_CPRE_MCKA                 ((unsigned int) 0xB) // (PWMC_CH) 
#define 	AT91C_PWMC_CPRE_MCKB                 ((unsigned int) 0xC) // (PWMC_CH) 
#define AT91C_PWMC_CALG       ((unsigned int) 0x1 <<  8) // (PWMC_CH) Channel Alignment
#define AT91C_PWMC_CPOL       ((unsigned int) 0x1 <<  9) // (PWMC_CH) Channel Polarity
#define AT91C_PWMC_CPD        ((unsigned int) 0x1 << 10) // (PWMC_CH) Channel Update Period
// -------- PWMC_CDTYR : (PWMC_CH Offset: 0x4) PWMC Channel Duty Cycle Register -------- 
#define AT91C_PWMC_CDTY       ((unsigned int) 0x0 <<  0) // (PWMC_CH) Channel Duty Cycle
// -------- PWMC_CPRDR : (PWMC_CH Offset: 0x8) PWMC Channel Period Register -------- 
#define AT91C_PWMC_CPRD       ((unsigned int) 0x0 <<  0) // (PWMC_CH) Channel Period
// -------- PWMC_CCNTR : (PWMC_CH Offset: 0xc) PWMC Channel Counter Register -------- 
#define AT91C_PWMC_CCNT       ((unsigned int) 0x0 <<  0) // (PWMC_CH) Channel Counter
// -------- PWMC_CUPDR : (PWMC_CH Offset: 0x10) PWMC Channel Update Register -------- 
#define AT91C_PWMC_CUPD       ((unsigned int) 0x0 <<  0) // (PWMC_CH) Channel Update

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Pulse Width Modulation Controller Interface
// *****************************************************************************
typedef struct _AT91S_PWMC {
	AT91_REG	 PWMC_MR; 	// PWMC Mode Register
	AT91_REG	 PWMC_ENA; 	// PWMC Enable Register
	AT91_REG	 PWMC_DIS; 	// PWMC Disable Register
	AT91_REG	 PWMC_SR; 	// PWMC Status Register
	AT91_REG	 PWMC_IER; 	// PWMC Interrupt Enable Register
	AT91_REG	 PWMC_IDR; 	// PWMC Interrupt Disable Register
	AT91_REG	 PWMC_IMR; 	// PWMC Interrupt Mask Register
	AT91_REG	 PWMC_ISR; 	// PWMC Interrupt Status Register
	AT91_REG	 Reserved0[55]; 	// 
	AT91_REG	 PWMC_VR; 	// PWMC Version Register
	AT91_REG	 Reserved1[64]; 	// 
	AT91S_PWMC_CH	 PWMC_CH[4]; 	// PWMC Channel
} AT91S_PWMC, *AT91PS_PWMC;

// -------- PWMC_MR : (PWMC Offset: 0x0) PWMC Mode Register -------- 
#define AT91C_PWMC_DIVA       ((unsigned int) 0xFF <<  0) // (PWMC) CLKA divide factor.
#define AT91C_PWMC_PREA       ((unsigned int) 0xF <<  8) // (PWMC) Divider Input Clock Prescaler A
#define 	AT91C_PWMC_PREA_MCK                  ((unsigned int) 0x0 <<  8) // (PWMC) 
#define AT91C_PWMC_DIVB       ((unsigned int) 0xFF << 16) // (PWMC) CLKB divide factor.
#define AT91C_PWMC_PREB       ((unsigned int) 0xF << 24) // (PWMC) Divider Input Clock Prescaler B
#define 	AT91C_PWMC_PREB_MCK                  ((unsigned int) 0x0 << 24) // (PWMC) 
// -------- PWMC_ENA : (PWMC Offset: 0x4) PWMC Enable Register -------- 
#define AT91C_PWMC_CHID0      ((unsigned int) 0x1 <<  0) // (PWMC) Channel ID 0
#define AT91C_PWMC_CHID1      ((unsigned int) 0x1 <<  1) // (PWMC) Channel ID 1
#define AT91C_PWMC_CHID2      ((unsigned int) 0x1 <<  2) // (PWMC) Channel ID 2
#define AT91C_PWMC_CHID3      ((unsigned int) 0x1 <<  3) // (PWMC) Channel ID 3
// -------- PWMC_DIS : (PWMC Offset: 0x8) PWMC Disable Register -------- 
// -------- PWMC_SR : (PWMC Offset: 0xc) PWMC Status Register -------- 
// -------- PWMC_IER : (PWMC Offset: 0x10) PWMC Interrupt Enable Register -------- 
// -------- PWMC_IDR : (PWMC Offset: 0x14) PWMC Interrupt Disable Register -------- 
// -------- PWMC_IMR : (PWMC Offset: 0x18) PWMC Interrupt Mask Register -------- 
// -------- PWMC_ISR : (PWMC Offset: 0x1c) PWMC Interrupt Status Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR USB Device Interface
// *****************************************************************************
typedef struct _AT91S_UDP {
	AT91_REG	 UDP_NUM; 	// Frame Number Register
	AT91_REG	 UDP_GLBSTATE; 	// Global State Register
	AT91_REG	 UDP_FADDR; 	// Function Address Register
	AT91_REG	 Reserved0[1]; 	// 
	AT91_REG	 UDP_IER; 	// Interrupt Enable Register
	AT91_REG	 UDP_IDR; 	// Interrupt Disable Register
	AT91_REG	 UDP_IMR; 	// Interrupt Mask Register
	AT91_REG	 UDP_ISR; 	// Interrupt Status Register
	AT91_REG	 UDP_ICR; 	// Interrupt Clear Register
	AT91_REG	 Reserved1[1]; 	// 
	AT91_REG	 UDP_RSTEP; 	// Reset Endpoint Register
	AT91_REG	 Reserved2[1]; 	// 
	AT91_REG	 UDP_CSR[6]; 	// Endpoint Control and Status Register
	AT91_REG	 Reserved3[2]; 	// 
	AT91_REG	 UDP_FDR[6]; 	// Endpoint FIFO Data Register
	AT91_REG	 Reserved4[3]; 	// 
	AT91_REG	 UDP_TXVC; 	// Transceiver Control Register
} AT91S_UDP, *AT91PS_UDP;

// -------- UDP_FRM_NUM : (UDP Offset: 0x0) USB Frame Number Register -------- 
#define AT91C_UDP_FRM_NUM     ((unsigned int) 0x7FF <<  0) // (UDP) Frame Number as Defined in the Packet Field Formats
#define AT91C_UDP_FRM_ERR     ((unsigned int) 0x1 << 16) // (UDP) Frame Error
#define AT91C_UDP_FRM_OK      ((unsigned int) 0x1 << 17) // (UDP) Frame OK
// -------- UDP_GLB_STATE : (UDP Offset: 0x4) USB Global State Register -------- 
#define AT91C_UDP_FADDEN      ((unsigned int) 0x1 <<  0) // (UDP) Function Address Enable
#define AT91C_UDP_CONFG       ((unsigned int) 0x1 <<  1) // (UDP) Configured
#define AT91C_UDP_ESR         ((unsigned int) 0x1 <<  2) // (UDP) Enable Send Resume
#define AT91C_UDP_RSMINPR     ((unsigned int) 0x1 <<  3) // (UDP) A Resume Has Been Sent to the Host
#define AT91C_UDP_RMWUPE      ((unsigned int) 0x1 <<  4) // (UDP) Remote Wake Up Enable
// -------- UDP_FADDR : (UDP Offset: 0x8) USB Function Address Register -------- 
#define AT91C_UDP_FADD        ((unsigned int) 0xFF <<  0) // (UDP) Function Address Value
#define AT91C_UDP_FEN         ((unsigned int) 0x1 <<  8) // (UDP) Function Enable
// -------- UDP_IER : (UDP Offset: 0x10) USB Interrupt Enable Register -------- 
#define AT91C_UDP_EPINT0      ((unsigned int) 0x1 <<  0) // (UDP) Endpoint 0 Interrupt
#define AT91C_UDP_EPINT1      ((unsigned int) 0x1 <<  1) // (UDP) Endpoint 0 Interrupt
#define AT91C_UDP_EPINT2      ((unsigned int) 0x1 <<  2) // (UDP) Endpoint 2 Interrupt
#define AT91C_UDP_EPINT3      ((unsigned int) 0x1 <<  3) // (UDP) Endpoint 3 Interrupt
#define AT91C_UDP_EPINT4      ((unsigned int) 0x1 <<  4) // (UDP) Endpoint 4 Interrupt
#define AT91C_UDP_EPINT5      ((unsigned int) 0x1 <<  5) // (UDP) Endpoint 5 Interrupt
#define AT91C_UDP_RXSUSP      ((unsigned int) 0x1 <<  8) // (UDP) USB Suspend Interrupt
#define AT91C_UDP_RXRSM       ((unsigned int) 0x1 <<  9) // (UDP) USB Resume Interrupt
#define AT91C_UDP_EXTRSM      ((unsigned int) 0x1 << 10) // (UDP) USB External Resume Interrupt
#define AT91C_UDP_SOFINT      ((unsigned int) 0x1 << 11) // (UDP) USB Start Of frame Interrupt
#define AT91C_UDP_WAKEUP      ((unsigned int) 0x1 << 13) // (UDP) USB Resume Interrupt
// -------- UDP_IDR : (UDP Offset: 0x14) USB Interrupt Disable Register -------- 
// -------- UDP_IMR : (UDP Offset: 0x18) USB Interrupt Mask Register -------- 
// -------- UDP_ISR : (UDP Offset: 0x1c) USB Interrupt Status Register -------- 
#define AT91C_UDP_ENDBUSRES   ((unsigned int) 0x1 << 12) // (UDP) USB End Of Bus Reset Interrupt
// -------- UDP_ICR : (UDP Offset: 0x20) USB Interrupt Clear Register -------- 
// -------- UDP_RST_EP : (UDP Offset: 0x28) USB Reset Endpoint Register -------- 
#define AT91C_UDP_EP0         ((unsigned int) 0x1 <<  0) // (UDP) Reset Endpoint 0
#define AT91C_UDP_EP1         ((unsigned int) 0x1 <<  1) // (UDP) Reset Endpoint 1
#define AT91C_UDP_EP2         ((unsigned int) 0x1 <<  2) // (UDP) Reset Endpoint 2
#define AT91C_UDP_EP3         ((unsigned int) 0x1 <<  3) // (UDP) Reset Endpoint 3
#define AT91C_UDP_EP4         ((unsigned int) 0x1 <<  4) // (UDP) Reset Endpoint 4
#define AT91C_UDP_EP5         ((unsigned int) 0x1 <<  5) // (UDP) Reset Endpoint 5
// -------- UDP_CSR : (UDP Offset: 0x30) USB Endpoint Control and Status Register -------- 
#define AT91C_UDP_TXCOMP      ((unsigned int) 0x1 <<  0) // (UDP) Generates an IN packet with data previously written in the DPR
#define AT91C_UDP_RX_DATA_BK0 ((unsigned int) 0x1 <<  1) // (UDP) Receive Data Bank 0
#define AT91C_UDP_RXSETUP     ((unsigned int) 0x1 <<  2) // (UDP) Sends STALL to the Host (Control endpoints)
#define AT91C_UDP_ISOERROR    ((unsigned int) 0x1 <<  3) // (UDP) Isochronous error (Isochronous endpoints)
#define AT91C_UDP_TXPKTRDY    ((unsigned int) 0x1 <<  4) // (UDP) Transmit Packet Ready
#define AT91C_UDP_FORCESTALL  ((unsigned int) 0x1 <<  5) // (UDP) Force Stall (used by Control, Bulk and Isochronous endpoints).
#define AT91C_UDP_RX_DATA_BK1 ((unsigned int) 0x1 <<  6) // (UDP) Receive Data Bank 1 (only used by endpoints with ping-pong attributes).
#define AT91C_UDP_DIR         ((unsigned int) 0x1 <<  7) // (UDP) Transfer Direction
#define AT91C_UDP_EPTYPE      ((unsigned int) 0x7 <<  8) // (UDP) Endpoint type
#define 	AT91C_UDP_EPTYPE_CTRL                 ((unsigned int) 0x0 <<  8) // (UDP) Control
#define 	AT91C_UDP_EPTYPE_ISO_OUT              ((unsigned int) 0x1 <<  8) // (UDP) Isochronous OUT
#define 	AT91C_UDP_EPTYPE_BULK_OUT             ((unsigned int) 0x2 <<  8) // (UDP) Bulk OUT
#define 	AT91C_UDP_EPTYPE_INT_OUT              ((unsigned int) 0x3 <<  8) // (UDP) Interrupt OUT
#define 	AT91C_UDP_EPTYPE_ISO_IN               ((unsigned int) 0x5 <<  8) // (UDP) Isochronous IN
#define 	AT91C_UDP_EPTYPE_BULK_IN              ((unsigned int) 0x6 <<  8) // (UDP) Bulk IN
#define 	AT91C_UDP_EPTYPE_INT_IN               ((unsigned int) 0x7 <<  8) // (UDP) Interrupt IN
#define AT91C_UDP_DTGLE       ((unsigned int) 0x1 << 11) // (UDP) Data Toggle
#define AT91C_UDP_EPEDS       ((unsigned int) 0x1 << 15) // (UDP) Endpoint Enable Disable
#define AT91C_UDP_RXBYTECNT   ((unsigned int) 0x7FF << 16) // (UDP) Number Of Bytes Available in the FIFO
// -------- UDP_TXVC : (UDP Offset: 0x74) Transceiver Control Register -------- 
#define AT91C_UDP_TXVDIS      ((unsigned int) 0x1 <<  8) // (UDP) 
#define AT91C_UDP_PUON        ((unsigned int) 0x1 <<  9) // (UDP) Pull-up ON

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Channel Interface
// *****************************************************************************
typedef struct _AT91S_TC {
	AT91_REG	 TC_CCR; 	// Channel Control Register
	AT91_REG	 TC_CMR; 	// Channel Mode Register (Capture Mode / Waveform Mode)
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 TC_CV; 	// Counter Value
	AT91_REG	 TC_RA; 	// Register A
	AT91_REG	 TC_RB; 	// Register B
	AT91_REG	 TC_RC; 	// Register C
	AT91_REG	 TC_SR; 	// Status Register
	AT91_REG	 TC_IER; 	// Interrupt Enable Register
	AT91_REG	 TC_IDR; 	// Interrupt Disable Register
	AT91_REG	 TC_IMR; 	// Interrupt Mask Register
} AT91S_TC, *AT91PS_TC;

// -------- TC_CCR : (TC Offset: 0x0) TC Channel Control Register -------- 
#define AT91C_TC_CLKEN        ((unsigned int) 0x1 <<  0) // (TC) Counter Clock Enable Command
#define AT91C_TC_CLKDIS       ((unsigned int) 0x1 <<  1) // (TC) Counter Clock Disable Command
#define AT91C_TC_SWTRG        ((unsigned int) 0x1 <<  2) // (TC) Software Trigger Command
// -------- TC_CMR : (TC Offset: 0x4) TC Channel Mode Register: Capture Mode / Waveform Mode -------- 
#define AT91C_TC_CLKS         ((unsigned int) 0x7 <<  0) // (TC) Clock Selection
#define 	AT91C_TC_CLKS_TIMER_DIV1_CLOCK     ((unsigned int) 0x0) // (TC) Clock selected: TIMER_DIV1_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV2_CLOCK     ((unsigned int) 0x1) // (TC) Clock selected: TIMER_DIV2_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV3_CLOCK     ((unsigned int) 0x2) // (TC) Clock selected: TIMER_DIV3_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV4_CLOCK     ((unsigned int) 0x3) // (TC) Clock selected: TIMER_DIV4_CLOCK
#define 	AT91C_TC_CLKS_TIMER_DIV5_CLOCK     ((unsigned int) 0x4) // (TC) Clock selected: TIMER_DIV5_CLOCK
#define 	AT91C_TC_CLKS_XC0                  ((unsigned int) 0x5) // (TC) Clock selected: XC0
#define 	AT91C_TC_CLKS_XC1                  ((unsigned int) 0x6) // (TC) Clock selected: XC1
#define 	AT91C_TC_CLKS_XC2                  ((unsigned int) 0x7) // (TC) Clock selected: XC2
#define AT91C_TC_CLKI         ((unsigned int) 0x1 <<  3) // (TC) Clock Invert
#define AT91C_TC_BURST        ((unsigned int) 0x3 <<  4) // (TC) Burst Signal Selection
#define 	AT91C_TC_BURST_NONE                 ((unsigned int) 0x0 <<  4) // (TC) The clock is not gated by an external signal
#define 	AT91C_TC_BURST_XC0                  ((unsigned int) 0x1 <<  4) // (TC) XC0 is ANDed with the selected clock
#define 	AT91C_TC_BURST_XC1                  ((unsigned int) 0x2 <<  4) // (TC) XC1 is ANDed with the selected clock
#define 	AT91C_TC_BURST_XC2                  ((unsigned int) 0x3 <<  4) // (TC) XC2 is ANDed with the selected clock
#define AT91C_TC_CPCSTOP      ((unsigned int) 0x1 <<  6) // (TC) Counter Clock Stopped with RC Compare
#define AT91C_TC_LDBSTOP      ((unsigned int) 0x1 <<  6) // (TC) Counter Clock Stopped with RB Loading
#define AT91C_TC_CPCDIS       ((unsigned int) 0x1 <<  7) // (TC) Counter Clock Disable with RC Compare
#define AT91C_TC_LDBDIS       ((unsigned int) 0x1 <<  7) // (TC) Counter Clock Disabled with RB Loading
#define AT91C_TC_ETRGEDG      ((unsigned int) 0x3 <<  8) // (TC) External Trigger Edge Selection
#define 	AT91C_TC_ETRGEDG_NONE                 ((unsigned int) 0x0 <<  8) // (TC) Edge: None
#define 	AT91C_TC_ETRGEDG_RISING               ((unsigned int) 0x1 <<  8) // (TC) Edge: rising edge
#define 	AT91C_TC_ETRGEDG_FALLING              ((unsigned int) 0x2 <<  8) // (TC) Edge: falling edge
#define 	AT91C_TC_ETRGEDG_BOTH                 ((unsigned int) 0x3 <<  8) // (TC) Edge: each edge
#define AT91C_TC_EEVTEDG      ((unsigned int) 0x3 <<  8) // (TC) External Event Edge Selection
#define 	AT91C_TC_EEVTEDG_NONE                 ((unsigned int) 0x0 <<  8) // (TC) Edge: None
#define 	AT91C_TC_EEVTEDG_RISING               ((unsigned int) 0x1 <<  8) // (TC) Edge: rising edge
#define 	AT91C_TC_EEVTEDG_FALLING              ((unsigned int) 0x2 <<  8) // (TC) Edge: falling edge
#define 	AT91C_TC_EEVTEDG_BOTH                 ((unsigned int) 0x3 <<  8) // (TC) Edge: each edge
#define AT91C_TC_EEVT         ((unsigned int) 0x3 << 10) // (TC) External Event  Selection
#define 	AT91C_TC_EEVT_TIOB                 ((unsigned int) 0x0 << 10) // (TC) Signal selected as external event: TIOB TIOB direction: input
#define 	AT91C_TC_EEVT_XC0                  ((unsigned int) 0x1 << 10) // (TC) Signal selected as external event: XC0 TIOB direction: output
#define 	AT91C_TC_EEVT_XC1                  ((unsigned int) 0x2 << 10) // (TC) Signal selected as external event: XC1 TIOB direction: output
#define 	AT91C_TC_EEVT_XC2                  ((unsigned int) 0x3 << 10) // (TC) Signal selected as external event: XC2 TIOB direction: output
#define AT91C_TC_ABETRG       ((unsigned int) 0x1 << 10) // (TC) TIOA or TIOB External Trigger Selection
#define AT91C_TC_ENETRG       ((unsigned int) 0x1 << 12) // (TC) External Event Trigger enable
#define AT91C_TC_WAVESEL      ((unsigned int) 0x3 << 13) // (TC) Waveform  Selection
#define 	AT91C_TC_WAVESEL_UP                   ((unsigned int) 0x0 << 13) // (TC) UP mode without atomatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN               ((unsigned int) 0x1 << 13) // (TC) UPDOWN mode without automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UP_AUTO              ((unsigned int) 0x2 << 13) // (TC) UP mode with automatic trigger on RC Compare
#define 	AT91C_TC_WAVESEL_UPDOWN_AUTO          ((unsigned int) 0x3 << 13) // (TC) UPDOWN mode with automatic trigger on RC Compare
#define AT91C_TC_CPCTRG       ((unsigned int) 0x1 << 14) // (TC) RC Compare Trigger Enable
#define AT91C_TC_WAVE         ((unsigned int) 0x1 << 15) // (TC) 
#define AT91C_TC_ACPA         ((unsigned int) 0x3 << 16) // (TC) RA Compare Effect on TIOA
#define 	AT91C_TC_ACPA_NONE                 ((unsigned int) 0x0 << 16) // (TC) Effect: none
#define 	AT91C_TC_ACPA_SET                  ((unsigned int) 0x1 << 16) // (TC) Effect: set
#define 	AT91C_TC_ACPA_CLEAR                ((unsigned int) 0x2 << 16) // (TC) Effect: clear
#define 	AT91C_TC_ACPA_TOGGLE               ((unsigned int) 0x3 << 16) // (TC) Effect: toggle
#define AT91C_TC_LDRA         ((unsigned int) 0x3 << 16) // (TC) RA Loading Selection
#define 	AT91C_TC_LDRA_NONE                 ((unsigned int) 0x0 << 16) // (TC) Edge: None
#define 	AT91C_TC_LDRA_RISING               ((unsigned int) 0x1 << 16) // (TC) Edge: rising edge of TIOA
#define 	AT91C_TC_LDRA_FALLING              ((unsigned int) 0x2 << 16) // (TC) Edge: falling edge of TIOA
#define 	AT91C_TC_LDRA_BOTH                 ((unsigned int) 0x3 << 16) // (TC) Edge: each edge of TIOA
#define AT91C_TC_ACPC         ((unsigned int) 0x3 << 18) // (TC) RC Compare Effect on TIOA
#define 	AT91C_TC_ACPC_NONE                 ((unsigned int) 0x0 << 18) // (TC) Effect: none
#define 	AT91C_TC_ACPC_SET                  ((unsigned int) 0x1 << 18) // (TC) Effect: set
#define 	AT91C_TC_ACPC_CLEAR                ((unsigned int) 0x2 << 18) // (TC) Effect: clear
#define 	AT91C_TC_ACPC_TOGGLE               ((unsigned int) 0x3 << 18) // (TC) Effect: toggle
#define AT91C_TC_LDRB         ((unsigned int) 0x3 << 18) // (TC) RB Loading Selection
#define 	AT91C_TC_LDRB_NONE                 ((unsigned int) 0x0 << 18) // (TC) Edge: None
#define 	AT91C_TC_LDRB_RISING               ((unsigned int) 0x1 << 18) // (TC) Edge: rising edge of TIOA
#define 	AT91C_TC_LDRB_FALLING              ((unsigned int) 0x2 << 18) // (TC) Edge: falling edge of TIOA
#define 	AT91C_TC_LDRB_BOTH                 ((unsigned int) 0x3 << 18) // (TC) Edge: each edge of TIOA
#define AT91C_TC_AEEVT        ((unsigned int) 0x3 << 20) // (TC) External Event Effect on TIOA
#define 	AT91C_TC_AEEVT_NONE                 ((unsigned int) 0x0 << 20) // (TC) Effect: none
#define 	AT91C_TC_AEEVT_SET                  ((unsigned int) 0x1 << 20) // (TC) Effect: set
#define 	AT91C_TC_AEEVT_CLEAR                ((unsigned int) 0x2 << 20) // (TC) Effect: clear
#define 	AT91C_TC_AEEVT_TOGGLE               ((unsigned int) 0x3 << 20) // (TC) Effect: toggle
#define AT91C_TC_ASWTRG       ((unsigned int) 0x3 << 22) // (TC) Software Trigger Effect on TIOA
#define 	AT91C_TC_ASWTRG_NONE                 ((unsigned int) 0x0 << 22) // (TC) Effect: none
#define 	AT91C_TC_ASWTRG_SET                  ((unsigned int) 0x1 << 22) // (TC) Effect: set
#define 	AT91C_TC_ASWTRG_CLEAR                ((unsigned int) 0x2 << 22) // (TC) Effect: clear
#define 	AT91C_TC_ASWTRG_TOGGLE               ((unsigned int) 0x3 << 22) // (TC) Effect: toggle
#define AT91C_TC_BCPB         ((unsigned int) 0x3 << 24) // (TC) RB Compare Effect on TIOB
#define 	AT91C_TC_BCPB_NONE                 ((unsigned int) 0x0 << 24) // (TC) Effect: none
#define 	AT91C_TC_BCPB_SET                  ((unsigned int) 0x1 << 24) // (TC) Effect: set
#define 	AT91C_TC_BCPB_CLEAR                ((unsigned int) 0x2 << 24) // (TC) Effect: clear
#define 	AT91C_TC_BCPB_TOGGLE               ((unsigned int) 0x3 << 24) // (TC) Effect: toggle
#define AT91C_TC_BCPC         ((unsigned int) 0x3 << 26) // (TC) RC Compare Effect on TIOB
#define 	AT91C_TC_BCPC_NONE                 ((unsigned int) 0x0 << 26) // (TC) Effect: none
#define 	AT91C_TC_BCPC_SET                  ((unsigned int) 0x1 << 26) // (TC) Effect: set
#define 	AT91C_TC_BCPC_CLEAR                ((unsigned int) 0x2 << 26) // (TC) Effect: clear
#define 	AT91C_TC_BCPC_TOGGLE               ((unsigned int) 0x3 << 26) // (TC) Effect: toggle
#define AT91C_TC_BEEVT        ((unsigned int) 0x3 << 28) // (TC) External Event Effect on TIOB
#define 	AT91C_TC_BEEVT_NONE                 ((unsigned int) 0x0 << 28) // (TC) Effect: none
#define 	AT91C_TC_BEEVT_SET                  ((unsigned int) 0x1 << 28) // (TC) Effect: set
#define 	AT91C_TC_BEEVT_CLEAR                ((unsigned int) 0x2 << 28) // (TC) Effect: clear
#define 	AT91C_TC_BEEVT_TOGGLE               ((unsigned int) 0x3 << 28) // (TC) Effect: toggle
#define AT91C_TC_BSWTRG       ((unsigned int) 0x3 << 30) // (TC) Software Trigger Effect on TIOB
#define 	AT91C_TC_BSWTRG_NONE                 ((unsigned int) 0x0 << 30) // (TC) Effect: none
#define 	AT91C_TC_BSWTRG_SET                  ((unsigned int) 0x1 << 30) // (TC) Effect: set
#define 	AT91C_TC_BSWTRG_CLEAR                ((unsigned int) 0x2 << 30) // (TC) Effect: clear
#define 	AT91C_TC_BSWTRG_TOGGLE               ((unsigned int) 0x3 << 30) // (TC) Effect: toggle
// -------- TC_SR : (TC Offset: 0x20) TC Channel Status Register -------- 
#define AT91C_TC_COVFS        ((unsigned int) 0x1 <<  0) // (TC) Counter Overflow
#define AT91C_TC_LOVRS        ((unsigned int) 0x1 <<  1) // (TC) Load Overrun
#define AT91C_TC_CPAS         ((unsigned int) 0x1 <<  2) // (TC) RA Compare
#define AT91C_TC_CPBS         ((unsigned int) 0x1 <<  3) // (TC) RB Compare
#define AT91C_TC_CPCS         ((unsigned int) 0x1 <<  4) // (TC) RC Compare
#define AT91C_TC_LDRAS        ((unsigned int) 0x1 <<  5) // (TC) RA Loading
#define AT91C_TC_LDRBS        ((unsigned int) 0x1 <<  6) // (TC) RB Loading
#define AT91C_TC_ETRGS        ((unsigned int) 0x1 <<  7) // (TC) External Trigger
#define AT91C_TC_CLKSTA       ((unsigned int) 0x1 << 16) // (TC) Clock Enabling
#define AT91C_TC_MTIOA        ((unsigned int) 0x1 << 17) // (TC) TIOA Mirror
#define AT91C_TC_MTIOB        ((unsigned int) 0x1 << 18) // (TC) TIOA Mirror
// -------- TC_IER : (TC Offset: 0x24) TC Channel Interrupt Enable Register -------- 
// -------- TC_IDR : (TC Offset: 0x28) TC Channel Interrupt Disable Register -------- 
// -------- TC_IMR : (TC Offset: 0x2c) TC Channel Interrupt Mask Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Timer Counter Interface
// *****************************************************************************
typedef struct _AT91S_TCB {
	AT91S_TC	 TCB_TC0; 	// TC Channel 0
	AT91_REG	 Reserved0[4]; 	// 
	AT91S_TC	 TCB_TC1; 	// TC Channel 1
	AT91_REG	 Reserved1[4]; 	// 
	AT91S_TC	 TCB_TC2; 	// TC Channel 2
	AT91_REG	 Reserved2[4]; 	// 
	AT91_REG	 TCB_BCR; 	// TC Block Control Register
	AT91_REG	 TCB_BMR; 	// TC Block Mode Register
} AT91S_TCB, *AT91PS_TCB;

// -------- TCB_BCR : (TCB Offset: 0xc0) TC Block Control Register -------- 
#define AT91C_TCB_SYNC        ((unsigned int) 0x1 <<  0) // (TCB) Synchro Command
// -------- TCB_BMR : (TCB Offset: 0xc4) TC Block Mode Register -------- 
#define AT91C_TCB_TC0XC0S     ((unsigned int) 0x3 <<  0) // (TCB) External Clock Signal 0 Selection
#define 	AT91C_TCB_TC0XC0S_TCLK0                ((unsigned int) 0x0) // (TCB) TCLK0 connected to XC0
#define 	AT91C_TCB_TC0XC0S_NONE                 ((unsigned int) 0x1) // (TCB) None signal connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA1                ((unsigned int) 0x2) // (TCB) TIOA1 connected to XC0
#define 	AT91C_TCB_TC0XC0S_TIOA2                ((unsigned int) 0x3) // (TCB) TIOA2 connected to XC0
#define AT91C_TCB_TC1XC1S     ((unsigned int) 0x3 <<  2) // (TCB) External Clock Signal 1 Selection
#define 	AT91C_TCB_TC1XC1S_TCLK1                ((unsigned int) 0x0 <<  2) // (TCB) TCLK1 connected to XC1
#define 	AT91C_TCB_TC1XC1S_NONE                 ((unsigned int) 0x1 <<  2) // (TCB) None signal connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA0                ((unsigned int) 0x2 <<  2) // (TCB) TIOA0 connected to XC1
#define 	AT91C_TCB_TC1XC1S_TIOA2                ((unsigned int) 0x3 <<  2) // (TCB) TIOA2 connected to XC1
#define AT91C_TCB_TC2XC2S     ((unsigned int) 0x3 <<  4) // (TCB) External Clock Signal 2 Selection
#define 	AT91C_TCB_TC2XC2S_TCLK2                ((unsigned int) 0x0 <<  4) // (TCB) TCLK2 connected to XC2
#define 	AT91C_TCB_TC2XC2S_NONE                 ((unsigned int) 0x1 <<  4) // (TCB) None signal connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA0                ((unsigned int) 0x2 <<  4) // (TCB) TIOA0 connected to XC2
#define 	AT91C_TCB_TC2XC2S_TIOA1                ((unsigned int) 0x3 <<  4) // (TCB) TIOA2 connected to XC2

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Control Area Network MailBox Interface
// *****************************************************************************
typedef struct _AT91S_CAN_MB {
	AT91_REG	 CAN_MB_MMR; 	// MailBox Mode Register
	AT91_REG	 CAN_MB_MAM; 	// MailBox Acceptance Mask Register
	AT91_REG	 CAN_MB_MID; 	// MailBox ID Register
	AT91_REG	 CAN_MB_MFID; 	// MailBox Family ID Register
	AT91_REG	 CAN_MB_MSR; 	// MailBox Status Register
	AT91_REG	 CAN_MB_MDL; 	// MailBox Data Low Register
	AT91_REG	 CAN_MB_MDH; 	// MailBox Data High Register
	AT91_REG	 CAN_MB_MCR; 	// MailBox Control Register
} AT91S_CAN_MB, *AT91PS_CAN_MB;

// -------- CAN_MMR : (CAN_MB Offset: 0x0) CAN Message Mode Register -------- 
#define AT91C_CAN_MTIMEMARK   ((unsigned int) 0xFFFF <<  0) // (CAN_MB) Mailbox Timemark
#define AT91C_CAN_PRIOR       ((unsigned int) 0xF << 16) // (CAN_MB) Mailbox Priority
#define AT91C_CAN_MOT         ((unsigned int) 0x7 << 24) // (CAN_MB) Mailbox Object Type
#define 	AT91C_CAN_MOT_DIS                  ((unsigned int) 0x0 << 24) // (CAN_MB) 
#define 	AT91C_CAN_MOT_RX                   ((unsigned int) 0x1 << 24) // (CAN_MB) 
#define 	AT91C_CAN_MOT_RXOVERWRITE          ((unsigned int) 0x2 << 24) // (CAN_MB) 
#define 	AT91C_CAN_MOT_TX                   ((unsigned int) 0x3 << 24) // (CAN_MB) 
#define 	AT91C_CAN_MOT_CONSUMER             ((unsigned int) 0x4 << 24) // (CAN_MB) 
#define 	AT91C_CAN_MOT_PRODUCER             ((unsigned int) 0x5 << 24) // (CAN_MB) 
// -------- CAN_MAM : (CAN_MB Offset: 0x4) CAN Message Acceptance Mask Register -------- 
#define AT91C_CAN_MIDvB       ((unsigned int) 0x3FFFF <<  0) // (CAN_MB) Complementary bits for identifier in extended mode
#define AT91C_CAN_MIDvA       ((unsigned int) 0x7FF << 18) // (CAN_MB) Identifier for standard frame mode
#define AT91C_CAN_MIDE        ((unsigned int) 0x1 << 29) // (CAN_MB) Identifier Version
// -------- CAN_MID : (CAN_MB Offset: 0x8) CAN Message ID Register -------- 
// -------- CAN_MFID : (CAN_MB Offset: 0xc) CAN Message Family ID Register -------- 
// -------- CAN_MSR : (CAN_MB Offset: 0x10) CAN Message Status Register -------- 
#define AT91C_CAN_MTIMESTAMP  ((unsigned int) 0xFFFF <<  0) // (CAN_MB) Timer Value
#define AT91C_CAN_MDLC        ((unsigned int) 0xF << 16) // (CAN_MB) Mailbox Data Length Code
#define AT91C_CAN_MRTR        ((unsigned int) 0x1 << 20) // (CAN_MB) Mailbox Remote Transmission Request
#define AT91C_CAN_MABT        ((unsigned int) 0x1 << 22) // (CAN_MB) Mailbox Message Abort
#define AT91C_CAN_MRDY        ((unsigned int) 0x1 << 23) // (CAN_MB) Mailbox Ready
#define AT91C_CAN_MMI         ((unsigned int) 0x1 << 24) // (CAN_MB) Mailbox Message Ignored
// -------- CAN_MDL : (CAN_MB Offset: 0x14) CAN Message Data Low Register -------- 
// -------- CAN_MDH : (CAN_MB Offset: 0x18) CAN Message Data High Register -------- 
// -------- CAN_MCR : (CAN_MB Offset: 0x1c) CAN Message Control Register -------- 
#define AT91C_CAN_MACR        ((unsigned int) 0x1 << 22) // (CAN_MB) Abort Request for Mailbox
#define AT91C_CAN_MTCR        ((unsigned int) 0x1 << 23) // (CAN_MB) Mailbox Transfer Command

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Control Area Network Interface
// *****************************************************************************
typedef struct _AT91S_CAN {
	AT91_REG	 CAN_MR; 	// Mode Register
	AT91_REG	 CAN_IER; 	// Interrupt Enable Register
	AT91_REG	 CAN_IDR; 	// Interrupt Disable Register
	AT91_REG	 CAN_IMR; 	// Interrupt Mask Register
	AT91_REG	 CAN_SR; 	// Status Register
	AT91_REG	 CAN_BR; 	// Baudrate Register
	AT91_REG	 CAN_TIM; 	// Timer Register
	AT91_REG	 CAN_TIMESTP; 	// Time Stamp Register
	AT91_REG	 CAN_ECR; 	// Error Counter Register
	AT91_REG	 CAN_TCR; 	// Transfer Command Register
	AT91_REG	 CAN_ACR; 	// Abort Command Register
	AT91_REG	 Reserved0[52]; 	// 
	AT91_REG	 CAN_VR; 	// Version Register
	AT91_REG	 Reserved1[64]; 	// 
	AT91S_CAN_MB	 CAN_MB0; 	// CAN Mailbox 0
	AT91S_CAN_MB	 CAN_MB1; 	// CAN Mailbox 1
	AT91S_CAN_MB	 CAN_MB2; 	// CAN Mailbox 2
	AT91S_CAN_MB	 CAN_MB3; 	// CAN Mailbox 3
	AT91S_CAN_MB	 CAN_MB4; 	// CAN Mailbox 4
	AT91S_CAN_MB	 CAN_MB5; 	// CAN Mailbox 5
	AT91S_CAN_MB	 CAN_MB6; 	// CAN Mailbox 6
	AT91S_CAN_MB	 CAN_MB7; 	// CAN Mailbox 7
	AT91S_CAN_MB	 CAN_MB8; 	// CAN Mailbox 8
	AT91S_CAN_MB	 CAN_MB9; 	// CAN Mailbox 9
	AT91S_CAN_MB	 CAN_MB10; 	// CAN Mailbox 10
	AT91S_CAN_MB	 CAN_MB11; 	// CAN Mailbox 11
	AT91S_CAN_MB	 CAN_MB12; 	// CAN Mailbox 12
	AT91S_CAN_MB	 CAN_MB13; 	// CAN Mailbox 13
	AT91S_CAN_MB	 CAN_MB14; 	// CAN Mailbox 14
	AT91S_CAN_MB	 CAN_MB15; 	// CAN Mailbox 15
} AT91S_CAN, *AT91PS_CAN;

// -------- CAN_MR : (CAN Offset: 0x0) CAN Mode Register -------- 
#define AT91C_CAN_CANEN       ((unsigned int) 0x1 <<  0) // (CAN) CAN Controller Enable
#define AT91C_CAN_LPM         ((unsigned int) 0x1 <<  1) // (CAN) Disable/Enable Low Power Mode
#define AT91C_CAN_ABM         ((unsigned int) 0x1 <<  2) // (CAN) Disable/Enable Autobaud/Listen Mode
#define AT91C_CAN_OVL         ((unsigned int) 0x1 <<  3) // (CAN) Disable/Enable Overload Frame
#define AT91C_CAN_TEOF        ((unsigned int) 0x1 <<  4) // (CAN) Time Stamp messages at each end of Frame
#define AT91C_CAN_TTM         ((unsigned int) 0x1 <<  5) // (CAN) Disable/Enable Time Trigger Mode
#define AT91C_CAN_TIMFRZ      ((unsigned int) 0x1 <<  6) // (CAN) Enable Timer Freeze
#define AT91C_CAN_DRPT        ((unsigned int) 0x1 <<  7) // (CAN) Disable Repeat
// -------- CAN_IER : (CAN Offset: 0x4) CAN Interrupt Enable Register -------- 
#define AT91C_CAN_MB0         ((unsigned int) 0x1 <<  0) // (CAN) Mailbox 0 Flag
#define AT91C_CAN_MB1         ((unsigned int) 0x1 <<  1) // (CAN) Mailbox 1 Flag
#define AT91C_CAN_MB2         ((unsigned int) 0x1 <<  2) // (CAN) Mailbox 2 Flag
#define AT91C_CAN_MB3         ((unsigned int) 0x1 <<  3) // (CAN) Mailbox 3 Flag
#define AT91C_CAN_MB4         ((unsigned int) 0x1 <<  4) // (CAN) Mailbox 4 Flag
#define AT91C_CAN_MB5         ((unsigned int) 0x1 <<  5) // (CAN) Mailbox 5 Flag
#define AT91C_CAN_MB6         ((unsigned int) 0x1 <<  6) // (CAN) Mailbox 6 Flag
#define AT91C_CAN_MB7         ((unsigned int) 0x1 <<  7) // (CAN) Mailbox 7 Flag
#define AT91C_CAN_MB8         ((unsigned int) 0x1 <<  8) // (CAN) Mailbox 8 Flag
#define AT91C_CAN_MB9         ((unsigned int) 0x1 <<  9) // (CAN) Mailbox 9 Flag
#define AT91C_CAN_MB10        ((unsigned int) 0x1 << 10) // (CAN) Mailbox 10 Flag
#define AT91C_CAN_MB11        ((unsigned int) 0x1 << 11) // (CAN) Mailbox 11 Flag
#define AT91C_CAN_MB12        ((unsigned int) 0x1 << 12) // (CAN) Mailbox 12 Flag
#define AT91C_CAN_MB13        ((unsigned int) 0x1 << 13) // (CAN) Mailbox 13 Flag
#define AT91C_CAN_MB14        ((unsigned int) 0x1 << 14) // (CAN) Mailbox 14 Flag
#define AT91C_CAN_MB15        ((unsigned int) 0x1 << 15) // (CAN) Mailbox 15 Flag
#define AT91C_CAN_ERRA        ((unsigned int) 0x1 << 16) // (CAN) Error Active Mode Flag
#define AT91C_CAN_WARN        ((unsigned int) 0x1 << 17) // (CAN) Warning Limit Flag
#define AT91C_CAN_ERRP        ((unsigned int) 0x1 << 18) // (CAN) Error Passive Mode Flag
#define AT91C_CAN_BOFF        ((unsigned int) 0x1 << 19) // (CAN) Bus Off Mode Flag
#define AT91C_CAN_SLEEP       ((unsigned int) 0x1 << 20) // (CAN) Sleep Flag
#define AT91C_CAN_WAKEUP      ((unsigned int) 0x1 << 21) // (CAN) Wakeup Flag
#define AT91C_CAN_TOVF        ((unsigned int) 0x1 << 22) // (CAN) Timer Overflow Flag
#define AT91C_CAN_TSTP        ((unsigned int) 0x1 << 23) // (CAN) Timestamp Flag
#define AT91C_CAN_CERR        ((unsigned int) 0x1 << 24) // (CAN) CRC Error
#define AT91C_CAN_SERR        ((unsigned int) 0x1 << 25) // (CAN) Stuffing Error
#define AT91C_CAN_AERR        ((unsigned int) 0x1 << 26) // (CAN) Acknowledgment Error
#define AT91C_CAN_FERR        ((unsigned int) 0x1 << 27) // (CAN) Form Error
#define AT91C_CAN_BERR        ((unsigned int) 0x1 << 28) // (CAN) Bit Error
// -------- CAN_IDR : (CAN Offset: 0x8) CAN Interrupt Disable Register -------- 
// -------- CAN_IMR : (CAN Offset: 0xc) CAN Interrupt Mask Register -------- 
// -------- CAN_SR : (CAN Offset: 0x10) CAN Status Register -------- 
#define AT91C_CAN_RBSY        ((unsigned int) 0x1 << 29) // (CAN) Receiver Busy
#define AT91C_CAN_TBSY        ((unsigned int) 0x1 << 30) // (CAN) Transmitter Busy
#define AT91C_CAN_OVLY        ((unsigned int) 0x1 << 31) // (CAN) Overload Busy
// -------- CAN_BR : (CAN Offset: 0x14) CAN Baudrate Register -------- 
#define AT91C_CAN_PHASE2      ((unsigned int) 0x7 <<  0) // (CAN) Phase 2 segment
#define AT91C_CAN_PHASE1      ((unsigned int) 0x7 <<  4) // (CAN) Phase 1 segment
#define AT91C_CAN_PROPAG      ((unsigned int) 0x7 <<  8) // (CAN) Programmation time segment
#define AT91C_CAN_SYNC        ((unsigned int) 0x3 << 12) // (CAN) Re-synchronization jump width segment
#define AT91C_CAN_BRP         ((unsigned int) 0x7F << 16) // (CAN) Baudrate Prescaler
#define AT91C_CAN_SMP         ((unsigned int) 0x1 << 24) // (CAN) Sampling mode
// -------- CAN_TIM : (CAN Offset: 0x18) CAN Timer Register -------- 
#define AT91C_CAN_TIMER       ((unsigned int) 0xFFFF <<  0) // (CAN) Timer field
// -------- CAN_TIMESTP : (CAN Offset: 0x1c) CAN Timestamp Register -------- 
// -------- CAN_ECR : (CAN Offset: 0x20) CAN Error Counter Register -------- 
#define AT91C_CAN_REC         ((unsigned int) 0xFF <<  0) // (CAN) Receive Error Counter
#define AT91C_CAN_TEC         ((unsigned int) 0xFF << 16) // (CAN) Transmit Error Counter
// -------- CAN_TCR : (CAN Offset: 0x24) CAN Transfer Command Register -------- 
#define AT91C_CAN_TIMRST      ((unsigned int) 0x1 << 31) // (CAN) Timer Reset Field
// -------- CAN_ACR : (CAN Offset: 0x28) CAN Abort Command Register -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Ethernet MAC 10/100
// *****************************************************************************
typedef struct _AT91S_EMAC {
	AT91_REG	 EMAC_NCR; 	// Network Control Register
	AT91_REG	 EMAC_NCFGR; 	// Network Configuration Register
	AT91_REG	 EMAC_NSR; 	// Network Status Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 EMAC_TSR; 	// Transmit Status Register
	AT91_REG	 EMAC_RBQP; 	// Receive Buffer Queue Pointer
	AT91_REG	 EMAC_TBQP; 	// Transmit Buffer Queue Pointer
	AT91_REG	 EMAC_RSR; 	// Receive Status Register
	AT91_REG	 EMAC_ISR; 	// Interrupt Status Register
	AT91_REG	 EMAC_IER; 	// Interrupt Enable Register
	AT91_REG	 EMAC_IDR; 	// Interrupt Disable Register
	AT91_REG	 EMAC_IMR; 	// Interrupt Mask Register
	AT91_REG	 EMAC_MAN; 	// PHY Maintenance Register
	AT91_REG	 EMAC_PTR; 	// Pause Time Register
	AT91_REG	 EMAC_PFR; 	// Pause Frames received Register
	AT91_REG	 EMAC_FTO; 	// Frames Transmitted OK Register
	AT91_REG	 EMAC_SCF; 	// Single Collision Frame Register
	AT91_REG	 EMAC_MCF; 	// Multiple Collision Frame Register
	AT91_REG	 EMAC_FRO; 	// Frames Received OK Register
	AT91_REG	 EMAC_FCSE; 	// Frame Check Sequence Error Register
	AT91_REG	 EMAC_ALE; 	// Alignment Error Register
	AT91_REG	 EMAC_DTF; 	// Deferred Transmission Frame Register
	AT91_REG	 EMAC_LCOL; 	// Late Collision Register
	AT91_REG	 EMAC_ECOL; 	// Excessive Collision Register
	AT91_REG	 EMAC_TUND; 	// Transmit Underrun Error Register
	AT91_REG	 EMAC_CSE; 	// Carrier Sense Error Register
	AT91_REG	 EMAC_RRE; 	// Receive Ressource Error Register
	AT91_REG	 EMAC_ROV; 	// Receive Overrun Errors Register
	AT91_REG	 EMAC_RSE; 	// Receive Symbol Errors Register
	AT91_REG	 EMAC_ELE; 	// Excessive Length Errors Register
	AT91_REG	 EMAC_RJA; 	// Receive Jabbers Register
	AT91_REG	 EMAC_USF; 	// Undersize Frames Register
	AT91_REG	 EMAC_STE; 	// SQE Test Error Register
	AT91_REG	 EMAC_RLE; 	// Receive Length Field Mismatch Register
	AT91_REG	 EMAC_TPF; 	// Transmitted Pause Frames Register
	AT91_REG	 EMAC_HRB; 	// Hash Address Bottom[31:0]
	AT91_REG	 EMAC_HRT; 	// Hash Address Top[63:32]
	AT91_REG	 EMAC_SA1L; 	// Specific Address 1 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA1H; 	// Specific Address 1 Top, Last 2 bytes
	AT91_REG	 EMAC_SA2L; 	// Specific Address 2 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA2H; 	// Specific Address 2 Top, Last 2 bytes
	AT91_REG	 EMAC_SA3L; 	// Specific Address 3 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA3H; 	// Specific Address 3 Top, Last 2 bytes
	AT91_REG	 EMAC_SA4L; 	// Specific Address 4 Bottom, First 4 bytes
	AT91_REG	 EMAC_SA4H; 	// Specific Address 4 Top, Last 2 bytes
	AT91_REG	 EMAC_TID; 	// Type ID Checking Register
	AT91_REG	 EMAC_TPQ; 	// Transmit Pause Quantum Register
	AT91_REG	 EMAC_USRIO; 	// USER Input/Output Register
	AT91_REG	 EMAC_WOL; 	// Wake On LAN Register
	AT91_REG	 Reserved1[13]; 	// 
	AT91_REG	 EMAC_REV; 	// Revision Register
} AT91S_EMAC, *AT91PS_EMAC;

// -------- EMAC_NCR : (EMAC Offset: 0x0)  -------- 
#define AT91C_EMAC_LB         ((unsigned int) 0x1 <<  0) // (EMAC) Loopback. Optional. When set, loopback signal is at high level.
#define AT91C_EMAC_LLB        ((unsigned int) 0x1 <<  1) // (EMAC) Loopback local. 
#define AT91C_EMAC_RE         ((unsigned int) 0x1 <<  2) // (EMAC) Receive enable. 
#define AT91C_EMAC_TE         ((unsigned int) 0x1 <<  3) // (EMAC) Transmit enable. 
#define AT91C_EMAC_MPE        ((unsigned int) 0x1 <<  4) // (EMAC) Management port enable. 
#define AT91C_EMAC_CLRSTAT    ((unsigned int) 0x1 <<  5) // (EMAC) Clear statistics registers. 
#define AT91C_EMAC_INCSTAT    ((unsigned int) 0x1 <<  6) // (EMAC) Increment statistics registers. 
#define AT91C_EMAC_WESTAT     ((unsigned int) 0x1 <<  7) // (EMAC) Write enable for statistics registers. 
#define AT91C_EMAC_BP         ((unsigned int) 0x1 <<  8) // (EMAC) Back pressure. 
#define AT91C_EMAC_TSTART     ((unsigned int) 0x1 <<  9) // (EMAC) Start Transmission. 
#define AT91C_EMAC_THALT      ((unsigned int) 0x1 << 10) // (EMAC) Transmission Halt. 
#define AT91C_EMAC_TPFR       ((unsigned int) 0x1 << 11) // (EMAC) Transmit pause frame 
#define AT91C_EMAC_TZQ        ((unsigned int) 0x1 << 12) // (EMAC) Transmit zero quantum pause frame
// -------- EMAC_NCFGR : (EMAC Offset: 0x4) Network Configuration Register -------- 
#define AT91C_EMAC_SPD        ((unsigned int) 0x1 <<  0) // (EMAC) Speed. 
#define AT91C_EMAC_FD         ((unsigned int) 0x1 <<  1) // (EMAC) Full duplex. 
#define AT91C_EMAC_JFRAME     ((unsigned int) 0x1 <<  3) // (EMAC) Jumbo Frames. 
#define AT91C_EMAC_CAF        ((unsigned int) 0x1 <<  4) // (EMAC) Copy all frames. 
#define AT91C_EMAC_NBC        ((unsigned int) 0x1 <<  5) // (EMAC) No broadcast. 
#define AT91C_EMAC_MTI        ((unsigned int) 0x1 <<  6) // (EMAC) Multicast hash event enable
#define AT91C_EMAC_UNI        ((unsigned int) 0x1 <<  7) // (EMAC) Unicast hash enable. 
#define AT91C_EMAC_BIG        ((unsigned int) 0x1 <<  8) // (EMAC) Receive 1522 bytes. 
#define AT91C_EMAC_EAE        ((unsigned int) 0x1 <<  9) // (EMAC) External address match enable. 
#define AT91C_EMAC_CLK        ((unsigned int) 0x3 << 10) // (EMAC) 
#define 	AT91C_EMAC_CLK_HCLK_8               ((unsigned int) 0x0 << 10) // (EMAC) HCLK divided by 8
#define 	AT91C_EMAC_CLK_HCLK_16              ((unsigned int) 0x1 << 10) // (EMAC) HCLK divided by 16
#define 	AT91C_EMAC_CLK_HCLK_32              ((unsigned int) 0x2 << 10) // (EMAC) HCLK divided by 32
#define 	AT91C_EMAC_CLK_HCLK_64              ((unsigned int) 0x3 << 10) // (EMAC) HCLK divided by 64
#define AT91C_EMAC_RTY        ((unsigned int) 0x1 << 12) // (EMAC) 
#define AT91C_EMAC_PAE        ((unsigned int) 0x1 << 13) // (EMAC) 
#define AT91C_EMAC_RBOF       ((unsigned int) 0x3 << 14) // (EMAC) 
#define 	AT91C_EMAC_RBOF_OFFSET_0             ((unsigned int) 0x0 << 14) // (EMAC) no offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_1             ((unsigned int) 0x1 << 14) // (EMAC) one byte offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_2             ((unsigned int) 0x2 << 14) // (EMAC) two bytes offset from start of receive buffer
#define 	AT91C_EMAC_RBOF_OFFSET_3             ((unsigned int) 0x3 << 14) // (EMAC) three bytes offset from start of receive buffer
#define AT91C_EMAC_RLCE       ((unsigned int) 0x1 << 16) // (EMAC) Receive Length field Checking Enable
#define AT91C_EMAC_DRFCS      ((unsigned int) 0x1 << 17) // (EMAC) Discard Receive FCS
#define AT91C_EMAC_EFRHD      ((unsigned int) 0x1 << 18) // (EMAC) 
#define AT91C_EMAC_IRXFCS     ((unsigned int) 0x1 << 19) // (EMAC) Ignore RX FCS
// -------- EMAC_NSR : (EMAC Offset: 0x8) Network Status Register -------- 
#define AT91C_EMAC_LINKR      ((unsigned int) 0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_MDIO       ((unsigned int) 0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_IDLE       ((unsigned int) 0x1 <<  2) // (EMAC) 
// -------- EMAC_TSR : (EMAC Offset: 0x14) Transmit Status Register -------- 
#define AT91C_EMAC_UBR        ((unsigned int) 0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_COL        ((unsigned int) 0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_RLES       ((unsigned int) 0x1 <<  2) // (EMAC) 
#define AT91C_EMAC_TGO        ((unsigned int) 0x1 <<  3) // (EMAC) Transmit Go
#define AT91C_EMAC_BEX        ((unsigned int) 0x1 <<  4) // (EMAC) Buffers exhausted mid frame
#define AT91C_EMAC_COMP       ((unsigned int) 0x1 <<  5) // (EMAC) 
#define AT91C_EMAC_UND        ((unsigned int) 0x1 <<  6) // (EMAC) 
// -------- EMAC_RSR : (EMAC Offset: 0x20) Receive Status Register -------- 
#define AT91C_EMAC_BNA        ((unsigned int) 0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_REC        ((unsigned int) 0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_OVR        ((unsigned int) 0x1 <<  2) // (EMAC) 
// -------- EMAC_ISR : (EMAC Offset: 0x24) Interrupt Status Register -------- 
#define AT91C_EMAC_MFD        ((unsigned int) 0x1 <<  0) // (EMAC) 
#define AT91C_EMAC_RCOMP      ((unsigned int) 0x1 <<  1) // (EMAC) 
#define AT91C_EMAC_RXUBR      ((unsigned int) 0x1 <<  2) // (EMAC) 
#define AT91C_EMAC_TXUBR      ((unsigned int) 0x1 <<  3) // (EMAC) 
#define AT91C_EMAC_TUNDR      ((unsigned int) 0x1 <<  4) // (EMAC) 
#define AT91C_EMAC_RLEX       ((unsigned int) 0x1 <<  5) // (EMAC) 
#define AT91C_EMAC_TXERR      ((unsigned int) 0x1 <<  6) // (EMAC) 
#define AT91C_EMAC_TCOMP      ((unsigned int) 0x1 <<  7) // (EMAC) 
#define AT91C_EMAC_LINK       ((unsigned int) 0x1 <<  9) // (EMAC) 
#define AT91C_EMAC_ROVR       ((unsigned int) 0x1 << 10) // (EMAC) 
#define AT91C_EMAC_HRESP      ((unsigned int) 0x1 << 11) // (EMAC) 
#define AT91C_EMAC_PFRE       ((unsigned int) 0x1 << 12) // (EMAC) 
#define AT91C_EMAC_PTZ        ((unsigned int) 0x1 << 13) // (EMAC) 
// -------- EMAC_IER : (EMAC Offset: 0x28) Interrupt Enable Register -------- 
// -------- EMAC_IDR : (EMAC Offset: 0x2c) Interrupt Disable Register -------- 
// -------- EMAC_IMR : (EMAC Offset: 0x30) Interrupt Mask Register -------- 
// -------- EMAC_MAN : (EMAC Offset: 0x34) PHY Maintenance Register -------- 
#define AT91C_EMAC_DATA       ((unsigned int) 0xFFFF <<  0) // (EMAC) 
#define AT91C_EMAC_CODE       ((unsigned int) 0x3 << 16) // (EMAC) 
#define AT91C_EMAC_REGA       ((unsigned int) 0x1F << 18) // (EMAC) 
#define AT91C_EMAC_PHYA       ((unsigned int) 0x1F << 23) // (EMAC) 
#define AT91C_EMAC_RW         ((unsigned int) 0x3 << 28) // (EMAC) 
#define AT91C_EMAC_SOF        ((unsigned int) 0x3 << 30) // (EMAC) 
// -------- EMAC_USRIO : (EMAC Offset: 0xc0) USER Input Output Register -------- 
#define AT91C_EMAC_RMII       ((unsigned int) 0x1 <<  0) // (EMAC) Reduce MII
// -------- EMAC_WOL : (EMAC Offset: 0xc4) Wake On LAN Register -------- 
#define AT91C_EMAC_IP         ((unsigned int) 0xFFFF <<  0) // (EMAC) ARP request IP address
#define AT91C_EMAC_MAG        ((unsigned int) 0x1 << 16) // (EMAC) Magic packet event enable
#define AT91C_EMAC_ARP        ((unsigned int) 0x1 << 17) // (EMAC) ARP request event enable
#define AT91C_EMAC_SA1        ((unsigned int) 0x1 << 18) // (EMAC) Specific address register 1 event enable
// -------- EMAC_REV : (EMAC Offset: 0xfc) Revision Register -------- 
#define AT91C_EMAC_REVREF     ((unsigned int) 0xFFFF <<  0) // (EMAC) 
#define AT91C_EMAC_PARTREF    ((unsigned int) 0xFFFF << 16) // (EMAC) 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Analog to Digital Convertor
// *****************************************************************************
typedef struct _AT91S_ADC {
	AT91_REG	 ADC_CR; 	// ADC Control Register
	AT91_REG	 ADC_MR; 	// ADC Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 ADC_CHER; 	// ADC Channel Enable Register
	AT91_REG	 ADC_CHDR; 	// ADC Channel Disable Register
	AT91_REG	 ADC_CHSR; 	// ADC Channel Status Register
	AT91_REG	 ADC_SR; 	// ADC Status Register
	AT91_REG	 ADC_LCDR; 	// ADC Last Converted Data Register
	AT91_REG	 ADC_IER; 	// ADC Interrupt Enable Register
	AT91_REG	 ADC_IDR; 	// ADC Interrupt Disable Register
	AT91_REG	 ADC_IMR; 	// ADC Interrupt Mask Register
	AT91_REG	 ADC_CDR0; 	// ADC Channel Data Register 0
	AT91_REG	 ADC_CDR1; 	// ADC Channel Data Register 1
	AT91_REG	 ADC_CDR2; 	// ADC Channel Data Register 2
	AT91_REG	 ADC_CDR3; 	// ADC Channel Data Register 3
	AT91_REG	 ADC_CDR4; 	// ADC Channel Data Register 4
	AT91_REG	 ADC_CDR5; 	// ADC Channel Data Register 5
	AT91_REG	 ADC_CDR6; 	// ADC Channel Data Register 6
	AT91_REG	 ADC_CDR7; 	// ADC Channel Data Register 7
	AT91_REG	 Reserved1[44]; 	// 
	AT91_REG	 ADC_RPR; 	// Receive Pointer Register
	AT91_REG	 ADC_RCR; 	// Receive Counter Register
	AT91_REG	 ADC_TPR; 	// Transmit Pointer Register
	AT91_REG	 ADC_TCR; 	// Transmit Counter Register
	AT91_REG	 ADC_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 ADC_RNCR; 	// Receive Next Counter Register
	AT91_REG	 ADC_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 ADC_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 ADC_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 ADC_PTSR; 	// PDC Transfer Status Register
} AT91S_ADC, *AT91PS_ADC;

// -------- ADC_CR : (ADC Offset: 0x0) ADC Control Register -------- 
#define AT91C_ADC_SWRST       ((unsigned int) 0x1 <<  0) // (ADC) Software Reset
#define AT91C_ADC_START       ((unsigned int) 0x1 <<  1) // (ADC) Start Conversion
// -------- ADC_MR : (ADC Offset: 0x4) ADC Mode Register -------- 
#define AT91C_ADC_TRGEN       ((unsigned int) 0x1 <<  0) // (ADC) Trigger Enable
#define 	AT91C_ADC_TRGEN_DIS                  ((unsigned int) 0x0) // (ADC) Hradware triggers are disabled. Starting a conversion is only possible by software
#define 	AT91C_ADC_TRGEN_EN                   ((unsigned int) 0x1) // (ADC) Hardware trigger selected by TRGSEL field is enabled.
#define AT91C_ADC_TRGSEL      ((unsigned int) 0x7 <<  1) // (ADC) Trigger Selection
#define 	AT91C_ADC_TRGSEL_TIOA0                ((unsigned int) 0x0 <<  1) // (ADC) Selected TRGSEL = TIAO0
#define 	AT91C_ADC_TRGSEL_TIOA1                ((unsigned int) 0x1 <<  1) // (ADC) Selected TRGSEL = TIAO1
#define 	AT91C_ADC_TRGSEL_TIOA2                ((unsigned int) 0x2 <<  1) // (ADC) Selected TRGSEL = TIAO2
#define 	AT91C_ADC_TRGSEL_TIOA3                ((unsigned int) 0x3 <<  1) // (ADC) Selected TRGSEL = TIAO3
#define 	AT91C_ADC_TRGSEL_TIOA4                ((unsigned int) 0x4 <<  1) // (ADC) Selected TRGSEL = TIAO4
#define 	AT91C_ADC_TRGSEL_TIOA5                ((unsigned int) 0x5 <<  1) // (ADC) Selected TRGSEL = TIAO5
#define 	AT91C_ADC_TRGSEL_EXT                  ((unsigned int) 0x6 <<  1) // (ADC) Selected TRGSEL = External Trigger
#define AT91C_ADC_LOWRES      ((unsigned int) 0x1 <<  4) // (ADC) Resolution.
#define 	AT91C_ADC_LOWRES_10_BIT               ((unsigned int) 0x0 <<  4) // (ADC) 10-bit resolution
#define 	AT91C_ADC_LOWRES_8_BIT                ((unsigned int) 0x1 <<  4) // (ADC) 8-bit resolution
#define AT91C_ADC_SLEEP       ((unsigned int) 0x1 <<  5) // (ADC) Sleep Mode
#define 	AT91C_ADC_SLEEP_NORMAL_MODE          ((unsigned int) 0x0 <<  5) // (ADC) Normal Mode
#define 	AT91C_ADC_SLEEP_MODE                 ((unsigned int) 0x1 <<  5) // (ADC) Sleep Mode
#define AT91C_ADC_PRESCAL     ((unsigned int) 0x3F <<  8) // (ADC) Prescaler rate selection
#define AT91C_ADC_STARTUP     ((unsigned int) 0x1F << 16) // (ADC) Startup Time
#define AT91C_ADC_SHTIM       ((unsigned int) 0xF << 24) // (ADC) Sample & Hold Time
// -------- 	ADC_CHER : (ADC Offset: 0x10) ADC Channel Enable Register -------- 
#define AT91C_ADC_CH0         ((unsigned int) 0x1 <<  0) // (ADC) Channel 0
#define AT91C_ADC_CH1         ((unsigned int) 0x1 <<  1) // (ADC) Channel 1
#define AT91C_ADC_CH2         ((unsigned int) 0x1 <<  2) // (ADC) Channel 2
#define AT91C_ADC_CH3         ((unsigned int) 0x1 <<  3) // (ADC) Channel 3
#define AT91C_ADC_CH4         ((unsigned int) 0x1 <<  4) // (ADC) Channel 4
#define AT91C_ADC_CH5         ((unsigned int) 0x1 <<  5) // (ADC) Channel 5
#define AT91C_ADC_CH6         ((unsigned int) 0x1 <<  6) // (ADC) Channel 6
#define AT91C_ADC_CH7         ((unsigned int) 0x1 <<  7) // (ADC) Channel 7
// -------- 	ADC_CHDR : (ADC Offset: 0x14) ADC Channel Disable Register -------- 
// -------- 	ADC_CHSR : (ADC Offset: 0x18) ADC Channel Status Register -------- 
// -------- ADC_SR : (ADC Offset: 0x1c) ADC Status Register -------- 
#define AT91C_ADC_EOC0        ((unsigned int) 0x1 <<  0) // (ADC) End of Conversion
#define AT91C_ADC_EOC1        ((unsigned int) 0x1 <<  1) // (ADC) End of Conversion
#define AT91C_ADC_EOC2        ((unsigned int) 0x1 <<  2) // (ADC) End of Conversion
#define AT91C_ADC_EOC3        ((unsigned int) 0x1 <<  3) // (ADC) End of Conversion
#define AT91C_ADC_EOC4        ((unsigned int) 0x1 <<  4) // (ADC) End of Conversion
#define AT91C_ADC_EOC5        ((unsigned int) 0x1 <<  5) // (ADC) End of Conversion
#define AT91C_ADC_EOC6        ((unsigned int) 0x1 <<  6) // (ADC) End of Conversion
#define AT91C_ADC_EOC7        ((unsigned int) 0x1 <<  7) // (ADC) End of Conversion
#define AT91C_ADC_OVRE0       ((unsigned int) 0x1 <<  8) // (ADC) Overrun Error
#define AT91C_ADC_OVRE1       ((unsigned int) 0x1 <<  9) // (ADC) Overrun Error
#define AT91C_ADC_OVRE2       ((unsigned int) 0x1 << 10) // (ADC) Overrun Error
#define AT91C_ADC_OVRE3       ((unsigned int) 0x1 << 11) // (ADC) Overrun Error
#define AT91C_ADC_OVRE4       ((unsigned int) 0x1 << 12) // (ADC) Overrun Error
#define AT91C_ADC_OVRE5       ((unsigned int) 0x1 << 13) // (ADC) Overrun Error
#define AT91C_ADC_OVRE6       ((unsigned int) 0x1 << 14) // (ADC) Overrun Error
#define AT91C_ADC_OVRE7       ((unsigned int) 0x1 << 15) // (ADC) Overrun Error
#define AT91C_ADC_DRDY        ((unsigned int) 0x1 << 16) // (ADC) Data Ready
#define AT91C_ADC_GOVRE       ((unsigned int) 0x1 << 17) // (ADC) General Overrun
#define AT91C_ADC_ENDRX       ((unsigned int) 0x1 << 18) // (ADC) End of Receiver Transfer
#define AT91C_ADC_RXBUFF      ((unsigned int) 0x1 << 19) // (ADC) RXBUFF Interrupt
// -------- ADC_LCDR : (ADC Offset: 0x20) ADC Last Converted Data Register -------- 
#define AT91C_ADC_LDATA       ((unsigned int) 0x3FF <<  0) // (ADC) Last Data Converted
// -------- ADC_IER : (ADC Offset: 0x24) ADC Interrupt Enable Register -------- 
// -------- ADC_IDR : (ADC Offset: 0x28) ADC Interrupt Disable Register -------- 
// -------- ADC_IMR : (ADC Offset: 0x2c) ADC Interrupt Mask Register -------- 
// -------- ADC_CDR0 : (ADC Offset: 0x30) ADC Channel Data Register 0 -------- 
#define AT91C_ADC_DATA        ((unsigned int) 0x3FF <<  0) // (ADC) Converted Data
// -------- ADC_CDR1 : (ADC Offset: 0x34) ADC Channel Data Register 1 -------- 
// -------- ADC_CDR2 : (ADC Offset: 0x38) ADC Channel Data Register 2 -------- 
// -------- ADC_CDR3 : (ADC Offset: 0x3c) ADC Channel Data Register 3 -------- 
// -------- ADC_CDR4 : (ADC Offset: 0x40) ADC Channel Data Register 4 -------- 
// -------- ADC_CDR5 : (ADC Offset: 0x44) ADC Channel Data Register 5 -------- 
// -------- ADC_CDR6 : (ADC Offset: 0x48) ADC Channel Data Register 6 -------- 
// -------- ADC_CDR7 : (ADC Offset: 0x4c) ADC Channel Data Register 7 -------- 

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Advanced  Encryption Standard
// *****************************************************************************
typedef struct _AT91S_AES {
	AT91_REG	 AES_CR; 	// Control Register
	AT91_REG	 AES_MR; 	// Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 AES_IER; 	// Interrupt Enable Register
	AT91_REG	 AES_IDR; 	// Interrupt Disable Register
	AT91_REG	 AES_IMR; 	// Interrupt Mask Register
	AT91_REG	 AES_ISR; 	// Interrupt Status Register
	AT91_REG	 AES_KEYWxR[4]; 	// Key Word x Register
	AT91_REG	 Reserved1[4]; 	// 
	AT91_REG	 AES_IDATAxR[4]; 	// Input Data x Register
	AT91_REG	 AES_ODATAxR[4]; 	// Output Data x Register
	AT91_REG	 AES_IVxR[4]; 	// Initialization Vector x Register
	AT91_REG	 Reserved2[35]; 	// 
	AT91_REG	 AES_VR; 	// AES Version Register
	AT91_REG	 AES_RPR; 	// Receive Pointer Register
	AT91_REG	 AES_RCR; 	// Receive Counter Register
	AT91_REG	 AES_TPR; 	// Transmit Pointer Register
	AT91_REG	 AES_TCR; 	// Transmit Counter Register
	AT91_REG	 AES_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 AES_RNCR; 	// Receive Next Counter Register
	AT91_REG	 AES_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 AES_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 AES_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 AES_PTSR; 	// PDC Transfer Status Register
} AT91S_AES, *AT91PS_AES;

// -------- AES_CR : (AES Offset: 0x0) Control Register -------- 
#define AT91C_AES_START       ((unsigned int) 0x1 <<  0) // (AES) Starts Processing
#define AT91C_AES_SWRST       ((unsigned int) 0x1 <<  8) // (AES) Software Reset
#define AT91C_AES_LOADSEED    ((unsigned int) 0x1 << 16) // (AES) Random Number Generator Seed Loading
// -------- AES_MR : (AES Offset: 0x4) Mode Register -------- 
#define AT91C_AES_CIPHER      ((unsigned int) 0x1 <<  0) // (AES) Processing Mode
#define AT91C_AES_PROCDLY     ((unsigned int) 0xF <<  4) // (AES) Processing Delay
#define AT91C_AES_SMOD        ((unsigned int) 0x3 <<  8) // (AES) Start Mode
#define 	AT91C_AES_SMOD_MANUAL               ((unsigned int) 0x0 <<  8) // (AES) Manual Mode: The START bit in register AES_CR must be set to begin encryption or decryption.
#define 	AT91C_AES_SMOD_AUTO                 ((unsigned int) 0x1 <<  8) // (AES) Auto Mode: no action in AES_CR is necessary (cf datasheet).
#define 	AT91C_AES_SMOD_PDC                  ((unsigned int) 0x2 <<  8) // (AES) PDC Mode (cf datasheet).
#define AT91C_AES_OPMOD       ((unsigned int) 0x7 << 12) // (AES) Operation Mode
#define 	AT91C_AES_OPMOD_ECB                  ((unsigned int) 0x0 << 12) // (AES) ECB Electronic CodeBook mode.
#define 	AT91C_AES_OPMOD_CBC                  ((unsigned int) 0x1 << 12) // (AES) CBC Cipher Block Chaining mode.
#define 	AT91C_AES_OPMOD_OFB                  ((unsigned int) 0x2 << 12) // (AES) OFB Output Feedback mode.
#define 	AT91C_AES_OPMOD_CFB                  ((unsigned int) 0x3 << 12) // (AES) CFB Cipher Feedback mode.
#define 	AT91C_AES_OPMOD_CTR                  ((unsigned int) 0x4 << 12) // (AES) CTR Counter mode.
#define AT91C_AES_LOD         ((unsigned int) 0x1 << 15) // (AES) Last Output Data Mode
#define AT91C_AES_CFBS        ((unsigned int) 0x7 << 16) // (AES) Cipher Feedback Data Size
#define 	AT91C_AES_CFBS_128_BIT              ((unsigned int) 0x0 << 16) // (AES) 128-bit.
#define 	AT91C_AES_CFBS_64_BIT               ((unsigned int) 0x1 << 16) // (AES) 64-bit.
#define 	AT91C_AES_CFBS_32_BIT               ((unsigned int) 0x2 << 16) // (AES) 32-bit.
#define 	AT91C_AES_CFBS_16_BIT               ((unsigned int) 0x3 << 16) // (AES) 16-bit.
#define 	AT91C_AES_CFBS_8_BIT                ((unsigned int) 0x4 << 16) // (AES) 8-bit.
#define AT91C_AES_CKEY        ((unsigned int) 0xF << 20) // (AES) Countermeasure Key
#define AT91C_AES_CTYPE       ((unsigned int) 0x1F << 24) // (AES) Countermeasure Type
#define 	AT91C_AES_CTYPE_TYPE1_EN             ((unsigned int) 0x1 << 24) // (AES) Countermeasure type 1 is enabled.
#define 	AT91C_AES_CTYPE_TYPE2_EN             ((unsigned int) 0x2 << 24) // (AES) Countermeasure type 2 is enabled.
#define 	AT91C_AES_CTYPE_TYPE3_EN             ((unsigned int) 0x4 << 24) // (AES) Countermeasure type 3 is enabled.
#define 	AT91C_AES_CTYPE_TYPE4_EN             ((unsigned int) 0x8 << 24) // (AES) Countermeasure type 4 is enabled.
#define 	AT91C_AES_CTYPE_TYPE5_EN             ((unsigned int) 0x10 << 24) // (AES) Countermeasure type 5 is enabled.
// -------- AES_IER : (AES Offset: 0x10) Interrupt Enable Register -------- 
#define AT91C_AES_DATRDY      ((unsigned int) 0x1 <<  0) // (AES) DATRDY
#define AT91C_AES_ENDRX       ((unsigned int) 0x1 <<  1) // (AES) PDC Read Buffer End
#define AT91C_AES_ENDTX       ((unsigned int) 0x1 <<  2) // (AES) PDC Write Buffer End
#define AT91C_AES_RXBUFF      ((unsigned int) 0x1 <<  3) // (AES) PDC Read Buffer Full
#define AT91C_AES_TXBUFE      ((unsigned int) 0x1 <<  4) // (AES) PDC Write Buffer Empty
#define AT91C_AES_URAD        ((unsigned int) 0x1 <<  8) // (AES) Unspecified Register Access Detection
// -------- AES_IDR : (AES Offset: 0x14) Interrupt Disable Register -------- 
// -------- AES_IMR : (AES Offset: 0x18) Interrupt Mask Register -------- 
// -------- AES_ISR : (AES Offset: 0x1c) Interrupt Status Register -------- 
#define AT91C_AES_URAT        ((unsigned int) 0x7 << 12) // (AES) Unspecified Register Access Type Status
#define 	AT91C_AES_URAT_IN_DAT_WRITE_DATPROC ((unsigned int) 0x0 << 12) // (AES) Input data register written during the data processing in PDC mode.
#define 	AT91C_AES_URAT_OUT_DAT_READ_DATPROC ((unsigned int) 0x1 << 12) // (AES) Output data register read during the data processing.
#define 	AT91C_AES_URAT_MODEREG_WRITE_DATPROC ((unsigned int) 0x2 << 12) // (AES) Mode register written during the data processing.
#define 	AT91C_AES_URAT_OUT_DAT_READ_SUBKEY  ((unsigned int) 0x3 << 12) // (AES) Output data register read during the sub-keys generation.
#define 	AT91C_AES_URAT_MODEREG_WRITE_SUBKEY ((unsigned int) 0x4 << 12) // (AES) Mode register written during the sub-keys generation.
#define 	AT91C_AES_URAT_WO_REG_READ          ((unsigned int) 0x5 << 12) // (AES) Write-only register read access.

// *****************************************************************************
//              SOFTWARE API DEFINITION  FOR Triple Data Encryption Standard
// *****************************************************************************
typedef struct _AT91S_TDES {
	AT91_REG	 TDES_CR; 	// Control Register
	AT91_REG	 TDES_MR; 	// Mode Register
	AT91_REG	 Reserved0[2]; 	// 
	AT91_REG	 TDES_IER; 	// Interrupt Enable Register
	AT91_REG	 TDES_IDR; 	// Interrupt Disable Register
	AT91_REG	 TDES_IMR; 	// Interrupt Mask Register
	AT91_REG	 TDES_ISR; 	// Interrupt Status Register
	AT91_REG	 TDES_KEY1WxR[2]; 	// Key 1 Word x Register
	AT91_REG	 TDES_KEY2WxR[2]; 	// Key 2 Word x Register
	AT91_REG	 TDES_KEY3WxR[2]; 	// Key 3 Word x Register
	AT91_REG	 Reserved1[2]; 	// 
	AT91_REG	 TDES_IDATAxR[2]; 	// Input Data x Register
	AT91_REG	 Reserved2[2]; 	// 
	AT91_REG	 TDES_ODATAxR[2]; 	// Output Data x Register
	AT91_REG	 Reserved3[2]; 	// 
	AT91_REG	 TDES_IVxR[2]; 	// Initialization Vector x Register
	AT91_REG	 Reserved4[37]; 	// 
	AT91_REG	 TDES_VR; 	// TDES Version Register
	AT91_REG	 TDES_RPR; 	// Receive Pointer Register
	AT91_REG	 TDES_RCR; 	// Receive Counter Register
	AT91_REG	 TDES_TPR; 	// Transmit Pointer Register
	AT91_REG	 TDES_TCR; 	// Transmit Counter Register
	AT91_REG	 TDES_RNPR; 	// Receive Next Pointer Register
	AT91_REG	 TDES_RNCR; 	// Receive Next Counter Register
	AT91_REG	 TDES_TNPR; 	// Transmit Next Pointer Register
	AT91_REG	 TDES_TNCR; 	// Transmit Next Counter Register
	AT91_REG	 TDES_PTCR; 	// PDC Transfer Control Register
	AT91_REG	 TDES_PTSR; 	// PDC Transfer Status Register
} AT91S_TDES, *AT91PS_TDES;

// -------- TDES_CR : (TDES Offset: 0x0) Control Register -------- 
#define AT91C_TDES_START      ((unsigned int) 0x1 <<  0) // (TDES) Starts Processing
#define AT91C_TDES_SWRST      ((unsigned int) 0x1 <<  8) // (TDES) Software Reset
// -------- TDES_MR : (TDES Offset: 0x4) Mode Register -------- 
#define AT91C_TDES_CIPHER     ((unsigned int) 0x1 <<  0) // (TDES) Processing Mode
#define AT91C_TDES_TDESMOD    ((unsigned int) 0x1 <<  1) // (TDES) Single or Triple DES Mode
#define AT91C_TDES_KEYMOD     ((unsigned int) 0x1 <<  4) // (TDES) Key Mode
#define AT91C_TDES_SMOD       ((unsigned int) 0x3 <<  8) // (TDES) Start Mode
#define 	AT91C_TDES_SMOD_MANUAL               ((unsigned int) 0x0 <<  8) // (TDES) Manual Mode: The START bit in register TDES_CR must be set to begin encryption or decryption.
#define 	AT91C_TDES_SMOD_AUTO                 ((unsigned int) 0x1 <<  8) // (TDES) Auto Mode: no action in TDES_CR is necessary (cf datasheet).
#define 	AT91C_TDES_SMOD_PDC                  ((unsigned int) 0x2 <<  8) // (TDES) PDC Mode (cf datasheet).
#define AT91C_TDES_OPMOD      ((unsigned int) 0x3 << 12) // (TDES) Operation Mode
#define 	AT91C_TDES_OPMOD_ECB                  ((unsigned int) 0x0 << 12) // (TDES) ECB Electronic CodeBook mode.
#define 	AT91C_TDES_OPMOD_CBC                  ((unsigned int) 0x1 << 12) // (TDES) CBC Cipher Block Chaining mode.
#define 	AT91C_TDES_OPMOD_OFB                  ((unsigned int) 0x2 << 12) // (TDES) OFB Output Feedback mode.
#define 	AT91C_TDES_OPMOD_CFB                  ((unsigned int) 0x3 << 12) // (TDES) CFB Cipher Feedback mode.
#define AT91C_TDES_LOD        ((unsigned int) 0x1 << 15) // (TDES) Last Output Data Mode
#define AT91C_TDES_CFBS       ((unsigned int) 0x3 << 16) // (TDES) Cipher Feedback Data Size
#define 	AT91C_TDES_CFBS_64_BIT               ((unsigned int) 0x0 << 16) // (TDES) 64-bit.
#define 	AT91C_TDES_CFBS_32_BIT               ((unsigned int) 0x1 << 16) // (TDES) 32-bit.
#define 	AT91C_TDES_CFBS_16_BIT               ((unsigned int) 0x2 << 16) // (TDES) 16-bit.
#define 	AT91C_TDES_CFBS_8_BIT                ((unsigned int) 0x3 << 16) // (TDES) 8-bit.
// -------- TDES_IER : (TDES Offset: 0x10) Interrupt Enable Register -------- 
#define AT91C_TDES_DATRDY     ((unsigned int) 0x1 <<  0) // (TDES) DATRDY
#define AT91C_TDES_ENDRX      ((unsigned int) 0x1 <<  1) // (TDES) PDC Read Buffer End
#define AT91C_TDES_ENDTX      ((unsigned int) 0x1 <<  2) // (TDES) PDC Write Buffer End
#define AT91C_TDES_RXBUFF     ((unsigned int) 0x1 <<  3) // (TDES) PDC Read Buffer Full
#define AT91C_TDES_TXBUFE     ((unsigned int) 0x1 <<  4) // (TDES) PDC Write Buffer Empty
#define AT91C_TDES_URAD       ((unsigned int) 0x1 <<  8) // (TDES) Unspecified Register Access Detection
// -------- TDES_IDR : (TDES Offset: 0x14) Interrupt Disable Register -------- 
// -------- TDES_IMR : (TDES Offset: 0x18) Interrupt Mask Register -------- 
// -------- TDES_ISR : (TDES Offset: 0x1c) Interrupt Status Register -------- 
#define AT91C_TDES_URAT       ((unsigned int) 0x3 << 12) // (TDES) Unspecified Register Access Type Status
#define 	AT91C_TDES_URAT_IN_DAT_WRITE_DATPROC ((unsigned int) 0x0 << 12) // (TDES) Input data register written during the data processing in PDC mode.
#define 	AT91C_TDES_URAT_OUT_DAT_READ_DATPROC ((unsigned int) 0x1 << 12) // (TDES) Output data register read during the data processing.
#define 	AT91C_TDES_URAT_MODEREG_WRITE_DATPROC ((unsigned int) 0x2 << 12) // (TDES) Mode register written during the data processing.
#define 	AT91C_TDES_URAT_WO_REG_READ          ((unsigned int) 0x3 << 12) // (TDES) Write-only register read access.

// *****************************************************************************
//               REGISTER ADDRESS DEFINITION FOR AT91SAM7X128
// *****************************************************************************
// ========== Register definition for SYS peripheral ========== 
// ========== Register definition for AIC peripheral ========== 
#define AT91C_AIC_IVR   ((AT91_REG *) 	0xFFFFF100) // (AIC) IRQ Vector Register
#define AT91C_AIC_SMR   ((AT91_REG *) 	0xFFFFF000) // (AIC) Source Mode Register
#define AT91C_AIC_FVR   ((AT91_REG *) 	0xFFFFF104) // (AIC) FIQ Vector Register
#define AT91C_AIC_DCR   ((AT91_REG *) 	0xFFFFF138) // (AIC) Debug Control Register (Protect)
#define AT91C_AIC_EOICR ((AT91_REG *) 	0xFFFFF130) // (AIC) End of Interrupt Command Register
#define AT91C_AIC_SVR   ((AT91_REG *) 	0xFFFFF080) // (AIC) Source Vector Register
#define AT91C_AIC_FFSR  ((AT91_REG *) 	0xFFFFF148) // (AIC) Fast Forcing Status Register
#define AT91C_AIC_ICCR  ((AT91_REG *) 	0xFFFFF128) // (AIC) Interrupt Clear Command Register
#define AT91C_AIC_ISR   ((AT91_REG *) 	0xFFFFF108) // (AIC) Interrupt Status Register
#define AT91C_AIC_IMR   ((AT91_REG *) 	0xFFFFF110) // (AIC) Interrupt Mask Register
#define AT91C_AIC_IPR   ((AT91_REG *) 	0xFFFFF10C) // (AIC) Interrupt Pending Register
#define AT91C_AIC_FFER  ((AT91_REG *) 	0xFFFFF140) // (AIC) Fast Forcing Enable Register
#define AT91C_AIC_IECR  ((AT91_REG *) 	0xFFFFF120) // (AIC) Interrupt Enable Command Register
#define AT91C_AIC_ISCR  ((AT91_REG *) 	0xFFFFF12C) // (AIC) Interrupt Set Command Register
#define AT91C_AIC_FFDR  ((AT91_REG *) 	0xFFFFF144) // (AIC) Fast Forcing Disable Register
#define AT91C_AIC_CISR  ((AT91_REG *) 	0xFFFFF114) // (AIC) Core Interrupt Status Register
#define AT91C_AIC_IDCR  ((AT91_REG *) 	0xFFFFF124) // (AIC) Interrupt Disable Command Register
#define AT91C_AIC_SPU   ((AT91_REG *) 	0xFFFFF134) // (AIC) Spurious Vector Register
// ========== Register definition for PDC_DBGU peripheral ========== 
#define AT91C_DBGU_TCR  ((AT91_REG *) 	0xFFFFF30C) // (PDC_DBGU) Transmit Counter Register
#define AT91C_DBGU_RNPR ((AT91_REG *) 	0xFFFFF310) // (PDC_DBGU) Receive Next Pointer Register
#define AT91C_DBGU_TNPR ((AT91_REG *) 	0xFFFFF318) // (PDC_DBGU) Transmit Next Pointer Register
#define AT91C_DBGU_TPR  ((AT91_REG *) 	0xFFFFF308) // (PDC_DBGU) Transmit Pointer Register
#define AT91C_DBGU_RPR  ((AT91_REG *) 	0xFFFFF300) // (PDC_DBGU) Receive Pointer Register
#define AT91C_DBGU_RCR  ((AT91_REG *) 	0xFFFFF304) // (PDC_DBGU) Receive Counter Register
#define AT91C_DBGU_RNCR ((AT91_REG *) 	0xFFFFF314) // (PDC_DBGU) Receive Next Counter Register
#define AT91C_DBGU_PTCR ((AT91_REG *) 	0xFFFFF320) // (PDC_DBGU) PDC Transfer Control Register
#define AT91C_DBGU_PTSR ((AT91_REG *) 	0xFFFFF324) // (PDC_DBGU) PDC Transfer Status Register
#define AT91C_DBGU_TNCR ((AT91_REG *) 	0xFFFFF31C) // (PDC_DBGU) Transmit Next Counter Register
// ========== Register definition for DBGU peripheral ========== 
#define AT91C_DBGU_EXID ((AT91_REG *) 	0xFFFFF244) // (DBGU) Chip ID Extension Register
#define AT91C_DBGU_BRGR ((AT91_REG *) 	0xFFFFF220) // (DBGU) Baud Rate Generator Register
#define AT91C_DBGU_IDR  ((AT91_REG *) 	0xFFFFF20C) // (DBGU) Interrupt Disable Register
#define AT91C_DBGU_CSR  ((AT91_REG *) 	0xFFFFF214) // (DBGU) Channel Status Register
#define AT91C_DBGU_CIDR ((AT91_REG *) 	0xFFFFF240) // (DBGU) Chip ID Register
#define AT91C_DBGU_MR   ((AT91_REG *) 	0xFFFFF204) // (DBGU) Mode Register
#define AT91C_DBGU_IMR  ((AT91_REG *) 	0xFFFFF210) // (DBGU) Interrupt Mask Register
#define AT91C_DBGU_CR   ((AT91_REG *) 	0xFFFFF200) // (DBGU) Control Register
#define AT91C_DBGU_FNTR ((AT91_REG *) 	0xFFFFF248) // (DBGU) Force NTRST Register
#define AT91C_DBGU_THR  ((AT91_REG *) 	0xFFFFF21C) // (DBGU) Transmitter Holding Register
#define AT91C_DBGU_RHR  ((AT91_REG *) 	0xFFFFF218) // (DBGU) Receiver Holding Register
#define AT91C_DBGU_IER  ((AT91_REG *) 	0xFFFFF208) // (DBGU) Interrupt Enable Register
// ========== Register definition for PIOA peripheral ========== 
#define AT91C_PIOA_ODR  ((AT91_REG *) 	0xFFFFF414) // (PIOA) Output Disable Registerr
#define AT91C_PIOA_SODR ((AT91_REG *) 	0xFFFFF430) // (PIOA) Set Output Data Register
#define AT91C_PIOA_ISR  ((AT91_REG *) 	0xFFFFF44C) // (PIOA) Interrupt Status Register
#define AT91C_PIOA_ABSR ((AT91_REG *) 	0xFFFFF478) // (PIOA) AB Select Status Register
#define AT91C_PIOA_IER  ((AT91_REG *) 	0xFFFFF440) // (PIOA) Interrupt Enable Register
#define AT91C_PIOA_PPUDR ((AT91_REG *) 	0xFFFFF460) // (PIOA) Pull-up Disable Register
#define AT91C_PIOA_IMR  ((AT91_REG *) 	0xFFFFF448) // (PIOA) Interrupt Mask Register
#define AT91C_PIOA_PER  ((AT91_REG *) 	0xFFFFF400) // (PIOA) PIO Enable Register
#define AT91C_PIOA_IFDR ((AT91_REG *) 	0xFFFFF424) // (PIOA) Input Filter Disable Register
#define AT91C_PIOA_OWDR ((AT91_REG *) 	0xFFFFF4A4) // (PIOA) Output Write Disable Register
#define AT91C_PIOA_MDSR ((AT91_REG *) 	0xFFFFF458) // (PIOA) Multi-driver Status Register
#define AT91C_PIOA_IDR  ((AT91_REG *) 	0xFFFFF444) // (PIOA) Interrupt Disable Register
#define AT91C_PIOA_ODSR ((AT91_REG *) 	0xFFFFF438) // (PIOA) Output Data Status Register
#define AT91C_PIOA_PPUSR ((AT91_REG *) 	0xFFFFF468) // (PIOA) Pull-up Status Register
#define AT91C_PIOA_OWSR ((AT91_REG *) 	0xFFFFF4A8) // (PIOA) Output Write Status Register
#define AT91C_PIOA_BSR  ((AT91_REG *) 	0xFFFFF474) // (PIOA) Select B Register
#define AT91C_PIOA_OWER ((AT91_REG *) 	0xFFFFF4A0) // (PIOA) Output Write Enable Register
#define AT91C_PIOA_IFER ((AT91_REG *) 	0xFFFFF420) // (PIOA) Input Filter Enable Register
#define AT91C_PIOA_PDSR ((AT91_REG *) 	0xFFFFF43C) // (PIOA) Pin Data Status Register
#define AT91C_PIOA_PPUER ((AT91_REG *) 	0xFFFFF464) // (PIOA) Pull-up Enable Register
#define AT91C_PIOA_OSR  ((AT91_REG *) 	0xFFFFF418) // (PIOA) Output Status Register
#define AT91C_PIOA_ASR  ((AT91_REG *) 	0xFFFFF470) // (PIOA) Select A Register
#define AT91C_PIOA_MDDR ((AT91_REG *) 	0xFFFFF454) // (PIOA) Multi-driver Disable Register
#define AT91C_PIOA_CODR ((AT91_REG *) 	0xFFFFF434) // (PIOA) Clear Output Data Register
#define AT91C_PIOA_MDER ((AT91_REG *) 	0xFFFFF450) // (PIOA) Multi-driver Enable Register
#define AT91C_PIOA_PDR  ((AT91_REG *) 	0xFFFFF404) // (PIOA) PIO Disable Register
#define AT91C_PIOA_IFSR ((AT91_REG *) 	0xFFFFF428) // (PIOA) Input Filter Status Register
#define AT91C_PIOA_OER  ((AT91_REG *) 	0xFFFFF410) // (PIOA) Output Enable Register
#define AT91C_PIOA_PSR  ((AT91_REG *) 	0xFFFFF408) // (PIOA) PIO Status Register
// ========== Register definition for PIOB peripheral ========== 
#define AT91C_PIOB_OWDR ((AT91_REG *) 	0xFFFFF6A4) // (PIOB) Output Write Disable Register
#define AT91C_PIOB_MDER ((AT91_REG *) 	0xFFFFF650) // (PIOB) Multi-driver Enable Register
#define AT91C_PIOB_PPUSR ((AT91_REG *) 	0xFFFFF668) // (PIOB) Pull-up Status Register
#define AT91C_PIOB_IMR  ((AT91_REG *) 	0xFFFFF648) // (PIOB) Interrupt Mask Register
#define AT91C_PIOB_ASR  ((AT91_REG *) 	0xFFFFF670) // (PIOB) Select A Register
#define AT91C_PIOB_PPUDR ((AT91_REG *) 	0xFFFFF660) // (PIOB) Pull-up Disable Register
#define AT91C_PIOB_PSR  ((AT91_REG *) 	0xFFFFF608) // (PIOB) PIO Status Register
#define AT91C_PIOB_IER  ((AT91_REG *) 	0xFFFFF640) // (PIOB) Interrupt Enable Register
#define AT91C_PIOB_CODR ((AT91_REG *) 	0xFFFFF634) // (PIOB) Clear Output Data Register
#define AT91C_PIOB_OWER ((AT91_REG *) 	0xFFFFF6A0) // (PIOB) Output Write Enable Register
#define AT91C_PIOB_ABSR ((AT91_REG *) 	0xFFFFF678) // (PIOB) AB Select Status Register
#define AT91C_PIOB_IFDR ((AT91_REG *) 	0xFFFFF624) // (PIOB) Input Filter Disable Register
#define AT91C_PIOB_PDSR ((AT91_REG *) 	0xFFFFF63C) // (PIOB) Pin Data Status Register
#define AT91C_PIOB_IDR  ((AT91_REG *) 	0xFFFFF644) // (PIOB) Interrupt Disable Register
#define AT91C_PIOB_OWSR ((AT91_REG *) 	0xFFFFF6A8) // (PIOB) Output Write Status Register
#define AT91C_PIOB_PDR  ((AT91_REG *) 	0xFFFFF604) // (PIOB) PIO Disable Register
#define AT91C_PIOB_ODR  ((AT91_REG *) 	0xFFFFF614) // (PIOB) Output Disable Registerr
#define AT91C_PIOB_IFSR ((AT91_REG *) 	0xFFFFF628) // (PIOB) Input Filter Status Register
#define AT91C_PIOB_PPUER ((AT91_REG *) 	0xFFFFF664) // (PIOB) Pull-up Enable Register
#define AT91C_PIOB_SODR ((AT91_REG *) 	0xFFFFF630) // (PIOB) Set Output Data Register
#define AT91C_PIOB_ISR  ((AT91_REG *) 	0xFFFFF64C) // (PIOB) Interrupt Status Register
#define AT91C_PIOB_ODSR ((AT91_REG *) 	0xFFFFF638) // (PIOB) Output Data Status Register
#define AT91C_PIOB_OSR  ((AT91_REG *) 	0xFFFFF618) // (PIOB) Output Status Register
#define AT91C_PIOB_MDSR ((AT91_REG *) 	0xFFFFF658) // (PIOB) Multi-driver Status Register
#define AT91C_PIOB_IFER ((AT91_REG *) 	0xFFFFF620) // (PIOB) Input Filter Enable Register
#define AT91C_PIOB_BSR  ((AT91_REG *) 	0xFFFFF674) // (PIOB) Select B Register
#define AT91C_PIOB_MDDR ((AT91_REG *) 	0xFFFFF654) // (PIOB) Multi-driver Disable Register
#define AT91C_PIOB_OER  ((AT91_REG *) 	0xFFFFF610) // (PIOB) Output Enable Register
#define AT91C_PIOB_PER  ((AT91_REG *) 	0xFFFFF600) // (PIOB) PIO Enable Register
// ========== Register definition for CKGR peripheral ========== 
#define AT91C_CKGR_MOR  ((AT91_REG *) 	0xFFFFFC20) // (CKGR) Main Oscillator Register
#define AT91C_CKGR_PLLR ((AT91_REG *) 	0xFFFFFC2C) // (CKGR) PLL Register
#define AT91C_CKGR_MCFR ((AT91_REG *) 	0xFFFFFC24) // (CKGR) Main Clock  Frequency Register
// ========== Register definition for PMC peripheral ========== 
#define AT91C_PMC_IDR   ((AT91_REG *) 	0xFFFFFC64) // (PMC) Interrupt Disable Register
#define AT91C_PMC_MOR   ((AT91_REG *) 	0xFFFFFC20) // (PMC) Main Oscillator Register
#define AT91C_PMC_PLLR  ((AT91_REG *) 	0xFFFFFC2C) // (PMC) PLL Register
#define AT91C_PMC_PCER  ((AT91_REG *) 	0xFFFFFC10) // (PMC) Peripheral Clock Enable Register
#define AT91C_PMC_PCKR  ((AT91_REG *) 	0xFFFFFC40) // (PMC) Programmable Clock Register
#define AT91C_PMC_MCKR  ((AT91_REG *) 	0xFFFFFC30) // (PMC) Master Clock Register
#define AT91C_PMC_SCDR  ((AT91_REG *) 	0xFFFFFC04) // (PMC) System Clock Disable Register
#define AT91C_PMC_PCDR  ((AT91_REG *) 	0xFFFFFC14) // (PMC) Peripheral Clock Disable Register
#define AT91C_PMC_SCSR  ((AT91_REG *) 	0xFFFFFC08) // (PMC) System Clock Status Register
#define AT91C_PMC_PCSR  ((AT91_REG *) 	0xFFFFFC18) // (PMC) Peripheral Clock Status Register
#define AT91C_PMC_MCFR  ((AT91_REG *) 	0xFFFFFC24) // (PMC) Main Clock  Frequency Register
#define AT91C_PMC_SCER  ((AT91_REG *) 	0xFFFFFC00) // (PMC) System Clock Enable Register
#define AT91C_PMC_IMR   ((AT91_REG *) 	0xFFFFFC6C) // (PMC) Interrupt Mask Register
#define AT91C_PMC_IER   ((AT91_REG *) 	0xFFFFFC60) // (PMC) Interrupt Enable Register
#define AT91C_PMC_SR    ((AT91_REG *) 	0xFFFFFC68) // (PMC) Status Register
// ========== Register definition for RSTC peripheral ========== 
#define AT91C_RSTC_RCR  ((AT91_REG *) 	0xFFFFFD00) // (RSTC) Reset Control Register
#define AT91C_RSTC_RMR  ((AT91_REG *) 	0xFFFFFD08) // (RSTC) Reset Mode Register
#define AT91C_RSTC_RSR  ((AT91_REG *) 	0xFFFFFD04) // (RSTC) Reset Status Register
// ========== Register definition for RTTC peripheral ========== 
#define AT91C_RTTC_RTSR ((AT91_REG *) 	0xFFFFFD2C) // (RTTC) Real-time Status Register
#define AT91C_RTTC_RTMR ((AT91_REG *) 	0xFFFFFD20) // (RTTC) Real-time Mode Register
#define AT91C_RTTC_RTVR ((AT91_REG *) 	0xFFFFFD28) // (RTTC) Real-time Value Register
#define AT91C_RTTC_RTAR ((AT91_REG *) 	0xFFFFFD24) // (RTTC) Real-time Alarm Register
// ========== Register definition for PITC peripheral ========== 
#define AT91C_PITC_PIVR ((AT91_REG *) 	0xFFFFFD38) // (PITC) Period Interval Value Register
#define AT91C_PITC_PISR ((AT91_REG *) 	0xFFFFFD34) // (PITC) Period Interval Status Register
#define AT91C_PITC_PIIR ((AT91_REG *) 	0xFFFFFD3C) // (PITC) Period Interval Image Register
#define AT91C_PITC_PIMR ((AT91_REG *) 	0xFFFFFD30) // (PITC) Period Interval Mode Register
// ========== Register definition for WDTC peripheral ========== 
#define AT91C_WDTC_WDCR ((AT91_REG *) 	0xFFFFFD40) // (WDTC) Watchdog Control Register
#define AT91C_WDTC_WDSR ((AT91_REG *) 	0xFFFFFD48) // (WDTC) Watchdog Status Register
#define AT91C_WDTC_WDMR ((AT91_REG *) 	0xFFFFFD44) // (WDTC) Watchdog Mode Register
// ========== Register definition for VREG peripheral ========== 
#define AT91C_VREG_MR   ((AT91_REG *) 	0xFFFFFD60) // (VREG) Voltage Regulator Mode Register
// ========== Register definition for MC peripheral ========== 
#define AT91C_MC_ASR    ((AT91_REG *) 	0xFFFFFF04) // (MC) MC Abort Status Register
#define AT91C_MC_RCR    ((AT91_REG *) 	0xFFFFFF00) // (MC) MC Remap Control Register
#define AT91C_MC_FCR    ((AT91_REG *) 	0xFFFFFF64) // (MC) MC Flash Command Register
#define AT91C_MC_AASR   ((AT91_REG *) 	0xFFFFFF08) // (MC) MC Abort Address Status Register
#define AT91C_MC_FSR    ((AT91_REG *) 	0xFFFFFF68) // (MC) MC Flash Status Register
#define AT91C_MC_FMR    ((AT91_REG *) 	0xFFFFFF60) // (MC) MC Flash Mode Register
// ========== Register definition for PDC_SPI1 peripheral ========== 
#define AT91C_SPI1_PTCR ((AT91_REG *) 	0xFFFE4120) // (PDC_SPI1) PDC Transfer Control Register
#define AT91C_SPI1_RPR  ((AT91_REG *) 	0xFFFE4100) // (PDC_SPI1) Receive Pointer Register
#define AT91C_SPI1_TNCR ((AT91_REG *) 	0xFFFE411C) // (PDC_SPI1) Transmit Next Counter Register
#define AT91C_SPI1_TPR  ((AT91_REG *) 	0xFFFE4108) // (PDC_SPI1) Transmit Pointer Register
#define AT91C_SPI1_TNPR ((AT91_REG *) 	0xFFFE4118) // (PDC_SPI1) Transmit Next Pointer Register
#define AT91C_SPI1_TCR  ((AT91_REG *) 	0xFFFE410C) // (PDC_SPI1) Transmit Counter Register
#define AT91C_SPI1_RCR  ((AT91_REG *) 	0xFFFE4104) // (PDC_SPI1) Receive Counter Register
#define AT91C_SPI1_RNPR ((AT91_REG *) 	0xFFFE4110) // (PDC_SPI1) Receive Next Pointer Register
#define AT91C_SPI1_RNCR ((AT91_REG *) 	0xFFFE4114) // (PDC_SPI1) Receive Next Counter Register
#define AT91C_SPI1_PTSR ((AT91_REG *) 	0xFFFE4124) // (PDC_SPI1) PDC Transfer Status Register
// ========== Register definition for SPI1 peripheral ========== 
#define AT91C_SPI1_IMR  ((AT91_REG *) 	0xFFFE401C) // (SPI1) Interrupt Mask Register
#define AT91C_SPI1_IER  ((AT91_REG *) 	0xFFFE4014) // (SPI1) Interrupt Enable Register
#define AT91C_SPI1_MR   ((AT91_REG *) 	0xFFFE4004) // (SPI1) Mode Register
#define AT91C_SPI1_RDR  ((AT91_REG *) 	0xFFFE4008) // (SPI1) Receive Data Register
#define AT91C_SPI1_IDR  ((AT91_REG *) 	0xFFFE4018) // (SPI1) Interrupt Disable Register
#define AT91C_SPI1_SR   ((AT91_REG *) 	0xFFFE4010) // (SPI1) Status Register
#define AT91C_SPI1_TDR  ((AT91_REG *) 	0xFFFE400C) // (SPI1) Transmit Data Register
#define AT91C_SPI1_CR   ((AT91_REG *) 	0xFFFE4000) // (SPI1) Control Register
#define AT91C_SPI1_CSR  ((AT91_REG *) 	0xFFFE4030) // (SPI1) Chip Select Register
// ========== Register definition for PDC_SPI0 peripheral ========== 
#define AT91C_SPI0_PTCR ((AT91_REG *) 	0xFFFE0120) // (PDC_SPI0) PDC Transfer Control Register
#define AT91C_SPI0_TPR  ((AT91_REG *) 	0xFFFE0108) // (PDC_SPI0) Transmit Pointer Register
#define AT91C_SPI0_TCR  ((AT91_REG *) 	0xFFFE010C) // (PDC_SPI0) Transmit Counter Register
#define AT91C_SPI0_RCR  ((AT91_REG *) 	0xFFFE0104) // (PDC_SPI0) Receive Counter Register
#define AT91C_SPI0_PTSR ((AT91_REG *) 	0xFFFE0124) // (PDC_SPI0) PDC Transfer Status Register
#define AT91C_SPI0_RNPR ((AT91_REG *) 	0xFFFE0110) // (PDC_SPI0) Receive Next Pointer Register
#define AT91C_SPI0_RPR  ((AT91_REG *) 	0xFFFE0100) // (PDC_SPI0) Receive Pointer Register
#define AT91C_SPI0_TNCR ((AT91_REG *) 	0xFFFE011C) // (PDC_SPI0) Transmit Next Counter Register
#define AT91C_SPI0_RNCR ((AT91_REG *) 	0xFFFE0114) // (PDC_SPI0) Receive Next Counter Register
#define AT91C_SPI0_TNPR ((AT91_REG *) 	0xFFFE0118) // (PDC_SPI0) Transmit Next Pointer Register
// ========== Register definition for SPI0 peripheral ========== 
#define AT91C_SPI0_IER  ((AT91_REG *) 	0xFFFE0014) // (SPI0) Interrupt Enable Register
#define AT91C_SPI0_SR   ((AT91_REG *) 	0xFFFE0010) // (SPI0) Status Register
#define AT91C_SPI0_IDR  ((AT91_REG *) 	0xFFFE0018) // (SPI0) Interrupt Disable Register
#define AT91C_SPI0_CR   ((AT91_REG *) 	0xFFFE0000) // (SPI0) Control Register
#define AT91C_SPI0_MR   ((AT91_REG *) 	0xFFFE0004) // (SPI0) Mode Register
#define AT91C_SPI0_IMR  ((AT91_REG *) 	0xFFFE001C) // (SPI0) Interrupt Mask Register
#define AT91C_SPI0_TDR  ((AT91_REG *) 	0xFFFE000C) // (SPI0) Transmit Data Register
#define AT91C_SPI0_RDR  ((AT91_REG *) 	0xFFFE0008) // (SPI0) Receive Data Register
#define AT91C_SPI0_CSR  ((AT91_REG *) 	0xFFFE0030) // (SPI0) Chip Select Register
// ========== Register definition for PDC_US1 peripheral ========== 
#define AT91C_US1_RNCR  ((AT91_REG *) 	0xFFFC4114) // (PDC_US1) Receive Next Counter Register
#define AT91C_US1_PTCR  ((AT91_REG *) 	0xFFFC4120) // (PDC_US1) PDC Transfer Control Register
#define AT91C_US1_TCR   ((AT91_REG *) 	0xFFFC410C) // (PDC_US1) Transmit Counter Register
#define AT91C_US1_PTSR  ((AT91_REG *) 	0xFFFC4124) // (PDC_US1) PDC Transfer Status Register
#define AT91C_US1_TNPR  ((AT91_REG *) 	0xFFFC4118) // (PDC_US1) Transmit Next Pointer Register
#define AT91C_US1_RCR   ((AT91_REG *) 	0xFFFC4104) // (PDC_US1) Receive Counter Register
#define AT91C_US1_RNPR  ((AT91_REG *) 	0xFFFC4110) // (PDC_US1) Receive Next Pointer Register
#define AT91C_US1_RPR   ((AT91_REG *) 	0xFFFC4100) // (PDC_US1) Receive Pointer Register
#define AT91C_US1_TNCR  ((AT91_REG *) 	0xFFFC411C) // (PDC_US1) Transmit Next Counter Register
#define AT91C_US1_TPR   ((AT91_REG *) 	0xFFFC4108) // (PDC_US1) Transmit Pointer Register
// ========== Register definition for US1 peripheral ========== 
#define AT91C_US1_IF    ((AT91_REG *) 	0xFFFC404C) // (US1) IRDA_FILTER Register
#define AT91C_US1_NER   ((AT91_REG *) 	0xFFFC4044) // (US1) Nb Errors Register
#define AT91C_US1_RTOR  ((AT91_REG *) 	0xFFFC4024) // (US1) Receiver Time-out Register
#define AT91C_US1_CSR   ((AT91_REG *) 	0xFFFC4014) // (US1) Channel Status Register
#define AT91C_US1_IDR   ((AT91_REG *) 	0xFFFC400C) // (US1) Interrupt Disable Register
#define AT91C_US1_IER   ((AT91_REG *) 	0xFFFC4008) // (US1) Interrupt Enable Register
#define AT91C_US1_THR   ((AT91_REG *) 	0xFFFC401C) // (US1) Transmitter Holding Register
#define AT91C_US1_TTGR  ((AT91_REG *) 	0xFFFC4028) // (US1) Transmitter Time-guard Register
#define AT91C_US1_RHR   ((AT91_REG *) 	0xFFFC4018) // (US1) Receiver Holding Register
#define AT91C_US1_BRGR  ((AT91_REG *) 	0xFFFC4020) // (US1) Baud Rate Generator Register
#define AT91C_US1_IMR   ((AT91_REG *) 	0xFFFC4010) // (US1) Interrupt Mask Register
#define AT91C_US1_FIDI  ((AT91_REG *) 	0xFFFC4040) // (US1) FI_DI_Ratio Register
#define AT91C_US1_CR    ((AT91_REG *) 	0xFFFC4000) // (US1) Control Register
#define AT91C_US1_MR    ((AT91_REG *) 	0xFFFC4004) // (US1) Mode Register
// ========== Register definition for PDC_US0 peripheral ========== 
#define AT91C_US0_TNPR  ((AT91_REG *) 	0xFFFC0118) // (PDC_US0) Transmit Next Pointer Register
#define AT91C_US0_RNPR  ((AT91_REG *) 	0xFFFC0110) // (PDC_US0) Receive Next Pointer Register
#define AT91C_US0_TCR   ((AT91_REG *) 	0xFFFC010C) // (PDC_US0) Transmit Counter Register
#define AT91C_US0_PTCR  ((AT91_REG *) 	0xFFFC0120) // (PDC_US0) PDC Transfer Control Register
#define AT91C_US0_PTSR  ((AT91_REG *) 	0xFFFC0124) // (PDC_US0) PDC Transfer Status Register
#define AT91C_US0_TNCR  ((AT91_REG *) 	0xFFFC011C) // (PDC_US0) Transmit Next Counter Register
#define AT91C_US0_TPR   ((AT91_REG *) 	0xFFFC0108) // (PDC_US0) Transmit Pointer Register
#define AT91C_US0_RCR   ((AT91_REG *) 	0xFFFC0104) // (PDC_US0) Receive Counter Register
#define AT91C_US0_RPR   ((AT91_REG *) 	0xFFFC0100) // (PDC_US0) Receive Pointer Register
#define AT91C_US0_RNCR  ((AT91_REG *) 	0xFFFC0114) // (PDC_US0) Receive Next Counter Register
// ========== Register definition for US0 peripheral ========== 
#define AT91C_US0_BRGR  ((AT91_REG *) 	0xFFFC0020) // (US0) Baud Rate Generator Register
#define AT91C_US0_NER   ((AT91_REG *) 	0xFFFC0044) // (US0) Nb Errors Register
#define AT91C_US0_CR    ((AT91_REG *) 	0xFFFC0000) // (US0) Control Register
#define AT91C_US0_IMR   ((AT91_REG *) 	0xFFFC0010) // (US0) Interrupt Mask Register
#define AT91C_US0_FIDI  ((AT91_REG *) 	0xFFFC0040) // (US0) FI_DI_Ratio Register
#define AT91C_US0_TTGR  ((AT91_REG *) 	0xFFFC0028) // (US0) Transmitter Time-guard Register
#define AT91C_US0_MR    ((AT91_REG *) 	0xFFFC0004) // (US0) Mode Register
#define AT91C_US0_RTOR  ((AT91_REG *) 	0xFFFC0024) // (US0) Receiver Time-out Register
#define AT91C_US0_CSR   ((AT91_REG *) 	0xFFFC0014) // (US0) Channel Status Register
#define AT91C_US0_RHR   ((AT91_REG *) 	0xFFFC0018) // (US0) Receiver Holding Register
#define AT91C_US0_IDR   ((AT91_REG *) 	0xFFFC000C) // (US0) Interrupt Disable Register
#define AT91C_US0_THR   ((AT91_REG *) 	0xFFFC001C) // (US0) Transmitter Holding Register
#define AT91C_US0_IF    ((AT91_REG *) 	0xFFFC004C) // (US0) IRDA_FILTER Register
#define AT91C_US0_IER   ((AT91_REG *) 	0xFFFC0008) // (US0) Interrupt Enable Register
// ========== Register definition for PDC_SSC peripheral ========== 
#define AT91C_SSC_TNCR  ((AT91_REG *) 	0xFFFD411C) // (PDC_SSC) Transmit Next Counter Register
#define AT91C_SSC_RPR   ((AT91_REG *) 	0xFFFD4100) // (PDC_SSC) Receive Pointer Register
#define AT91C_SSC_RNCR  ((AT91_REG *) 	0xFFFD4114) // (PDC_SSC) Receive Next Counter Register
#define AT91C_SSC_TPR   ((AT91_REG *) 	0xFFFD4108) // (PDC_SSC) Transmit Pointer Register
#define AT91C_SSC_PTCR  ((AT91_REG *) 	0xFFFD4120) // (PDC_SSC) PDC Transfer Control Register
#define AT91C_SSC_TCR   ((AT91_REG *) 	0xFFFD410C) // (PDC_SSC) Transmit Counter Register
#define AT91C_SSC_RCR   ((AT91_REG *) 	0xFFFD4104) // (PDC_SSC) Receive Counter Register
#define AT91C_SSC_RNPR  ((AT91_REG *) 	0xFFFD4110) // (PDC_SSC) Receive Next Pointer Register
#define AT91C_SSC_TNPR  ((AT91_REG *) 	0xFFFD4118) // (PDC_SSC) Transmit Next Pointer Register
#define AT91C_SSC_PTSR  ((AT91_REG *) 	0xFFFD4124) // (PDC_SSC) PDC Transfer Status Register
// ========== Register definition for SSC peripheral ========== 
#define AT91C_SSC_RHR   ((AT91_REG *) 	0xFFFD4020) // (SSC) Receive Holding Register
#define AT91C_SSC_RSHR  ((AT91_REG *) 	0xFFFD4030) // (SSC) Receive Sync Holding Register
#define AT91C_SSC_TFMR  ((AT91_REG *) 	0xFFFD401C) // (SSC) Transmit Frame Mode Register
#define AT91C_SSC_IDR   ((AT91_REG *) 	0xFFFD4048) // (SSC) Interrupt Disable Register
#define AT91C_SSC_THR   ((AT91_REG *) 	0xFFFD4024) // (SSC) Transmit Holding Register
#define AT91C_SSC_RCMR  ((AT91_REG *) 	0xFFFD4010) // (SSC) Receive Clock ModeRegister
#define AT91C_SSC_IER   ((AT91_REG *) 	0xFFFD4044) // (SSC) Interrupt Enable Register
#define AT91C_SSC_TSHR  ((AT91_REG *) 	0xFFFD4034) // (SSC) Transmit Sync Holding Register
#define AT91C_SSC_SR    ((AT91_REG *) 	0xFFFD4040) // (SSC) Status Register
#define AT91C_SSC_CMR   ((AT91_REG *) 	0xFFFD4004) // (SSC) Clock Mode Register
#define AT91C_SSC_TCMR  ((AT91_REG *) 	0xFFFD4018) // (SSC) Transmit Clock Mode Register
#define AT91C_SSC_CR    ((AT91_REG *) 	0xFFFD4000) // (SSC) Control Register
#define AT91C_SSC_IMR   ((AT91_REG *) 	0xFFFD404C) // (SSC) Interrupt Mask Register
#define AT91C_SSC_RFMR  ((AT91_REG *) 	0xFFFD4014) // (SSC) Receive Frame Mode Register
// ========== Register definition for TWI peripheral ========== 
#define AT91C_TWI_IER   ((AT91_REG *) 	0xFFFB8024) // (TWI) Interrupt Enable Register
#define AT91C_TWI_CR    ((AT91_REG *) 	0xFFFB8000) // (TWI) Control Register
#define AT91C_TWI_SR    ((AT91_REG *) 	0xFFFB8020) // (TWI) Status Register
#define AT91C_TWI_IMR   ((AT91_REG *) 	0xFFFB802C) // (TWI) Interrupt Mask Register
#define AT91C_TWI_THR   ((AT91_REG *) 	0xFFFB8034) // (TWI) Transmit Holding Register
#define AT91C_TWI_IDR   ((AT91_REG *) 	0xFFFB8028) // (TWI) Interrupt Disable Register
#define AT91C_TWI_IADR  ((AT91_REG *) 	0xFFFB800C) // (TWI) Internal Address Register
#define AT91C_TWI_MMR   ((AT91_REG *) 	0xFFFB8004) // (TWI) Master Mode Register
#define AT91C_TWI_CWGR  ((AT91_REG *) 	0xFFFB8010) // (TWI) Clock Waveform Generator Register
#define AT91C_TWI_RHR   ((AT91_REG *) 	0xFFFB8030) // (TWI) Receive Holding Register
// ========== Register definition for PWMC_CH3 peripheral ========== 
#define AT91C_PWMC_CH3_CUPDR ((AT91_REG *) 	0xFFFCC270) // (PWMC_CH3) Channel Update Register
#define AT91C_PWMC_CH3_Reserved ((AT91_REG *) 	0xFFFCC274) // (PWMC_CH3) Reserved
#define AT91C_PWMC_CH3_CPRDR ((AT91_REG *) 	0xFFFCC268) // (PWMC_CH3) Channel Period Register
#define AT91C_PWMC_CH3_CDTYR ((AT91_REG *) 	0xFFFCC264) // (PWMC_CH3) Channel Duty Cycle Register
#define AT91C_PWMC_CH3_CCNTR ((AT91_REG *) 	0xFFFCC26C) // (PWMC_CH3) Channel Counter Register
#define AT91C_PWMC_CH3_CMR ((AT91_REG *) 	0xFFFCC260) // (PWMC_CH3) Channel Mode Register
// ========== Register definition for PWMC_CH2 peripheral ========== 
#define AT91C_PWMC_CH2_Reserved ((AT91_REG *) 	0xFFFCC254) // (PWMC_CH2) Reserved
#define AT91C_PWMC_CH2_CMR ((AT91_REG *) 	0xFFFCC240) // (PWMC_CH2) Channel Mode Register
#define AT91C_PWMC_CH2_CCNTR ((AT91_REG *) 	0xFFFCC24C) // (PWMC_CH2) Channel Counter Register
#define AT91C_PWMC_CH2_CPRDR ((AT91_REG *) 	0xFFFCC248) // (PWMC_CH2) Channel Period Register
#define AT91C_PWMC_CH2_CUPDR ((AT91_REG *) 	0xFFFCC250) // (PWMC_CH2) Channel Update Register
#define AT91C_PWMC_CH2_CDTYR ((AT91_REG *) 	0xFFFCC244) // (PWMC_CH2) Channel Duty Cycle Register
// ========== Register definition for PWMC_CH1 peripheral ========== 
#define AT91C_PWMC_CH1_Reserved ((AT91_REG *) 	0xFFFCC234) // (PWMC_CH1) Reserved
#define AT91C_PWMC_CH1_CUPDR ((AT91_REG *) 	0xFFFCC230) // (PWMC_CH1) Channel Update Register
#define AT91C_PWMC_CH1_CPRDR ((AT91_REG *) 	0xFFFCC228) // (PWMC_CH1) Channel Period Register
#define AT91C_PWMC_CH1_CCNTR ((AT91_REG *) 	0xFFFCC22C) // (PWMC_CH1) Channel Counter Register
#define AT91C_PWMC_CH1_CDTYR ((AT91_REG *) 	0xFFFCC224) // (PWMC_CH1) Channel Duty Cycle Register
#define AT91C_PWMC_CH1_CMR ((AT91_REG *) 	0xFFFCC220) // (PWMC_CH1) Channel Mode Register
// ========== Register definition for PWMC_CH0 peripheral ========== 
#define AT91C_PWMC_CH0_Reserved ((AT91_REG *) 	0xFFFCC214) // (PWMC_CH0) Reserved
#define AT91C_PWMC_CH0_CPRDR ((AT91_REG *) 	0xFFFCC208) // (PWMC_CH0) Channel Period Register
#define AT91C_PWMC_CH0_CDTYR ((AT91_REG *) 	0xFFFCC204) // (PWMC_CH0) Channel Duty Cycle Register
#define AT91C_PWMC_CH0_CMR ((AT91_REG *) 	0xFFFCC200) // (PWMC_CH0) Channel Mode Register
#define AT91C_PWMC_CH0_CUPDR ((AT91_REG *) 	0xFFFCC210) // (PWMC_CH0) Channel Update Register
#define AT91C_PWMC_CH0_CCNTR ((AT91_REG *) 	0xFFFCC20C) // (PWMC_CH0) Channel Counter Register
// ========== Register definition for PWMC peripheral ========== 
#define AT91C_PWMC_IDR  ((AT91_REG *) 	0xFFFCC014) // (PWMC) PWMC Interrupt Disable Register
#define AT91C_PWMC_DIS  ((AT91_REG *) 	0xFFFCC008) // (PWMC) PWMC Disable Register
#define AT91C_PWMC_IER  ((AT91_REG *) 	0xFFFCC010) // (PWMC) PWMC Interrupt Enable Register
#define AT91C_PWMC_VR   ((AT91_REG *) 	0xFFFCC0FC) // (PWMC) PWMC Version Register
#define AT91C_PWMC_ISR  ((AT91_REG *) 	0xFFFCC01C) // (PWMC) PWMC Interrupt Status Register
#define AT91C_PWMC_SR   ((AT91_REG *) 	0xFFFCC00C) // (PWMC) PWMC Status Register
#define AT91C_PWMC_IMR  ((AT91_REG *) 	0xFFFCC018) // (PWMC) PWMC Interrupt Mask Register
#define AT91C_PWMC_MR   ((AT91_REG *) 	0xFFFCC000) // (PWMC) PWMC Mode Register
#define AT91C_PWMC_ENA  ((AT91_REG *) 	0xFFFCC004) // (PWMC) PWMC Enable Register
// ========== Register definition for UDP peripheral ========== 
#define AT91C_UDP_IMR   ((AT91_REG *) 	0xFFFB0018) // (UDP) Interrupt Mask Register
#define AT91C_UDP_FADDR ((AT91_REG *) 	0xFFFB0008) // (UDP) Function Address Register
#define AT91C_UDP_NUM   ((AT91_REG *) 	0xFFFB0000) // (UDP) Frame Number Register
#define AT91C_UDP_FDR   ((AT91_REG *) 	0xFFFB0050) // (UDP) Endpoint FIFO Data Register
#define AT91C_UDP_ISR   ((AT91_REG *) 	0xFFFB001C) // (UDP) Interrupt Status Register
#define AT91C_UDP_CSR   ((AT91_REG *) 	0xFFFB0030) // (UDP) Endpoint Control and Status Register
#define AT91C_UDP_IDR   ((AT91_REG *) 	0xFFFB0014) // (UDP) Interrupt Disable Register
#define AT91C_UDP_ICR   ((AT91_REG *) 	0xFFFB0020) // (UDP) Interrupt Clear Register
#define AT91C_UDP_RSTEP ((AT91_REG *) 	0xFFFB0028) // (UDP) Reset Endpoint Register
#define AT91C_UDP_TXVC  ((AT91_REG *) 	0xFFFB0074) // (UDP) Transceiver Control Register
#define AT91C_UDP_GLBSTATE ((AT91_REG *) 	0xFFFB0004) // (UDP) Global State Register
#define AT91C_UDP_IER   ((AT91_REG *) 	0xFFFB0010) // (UDP) Interrupt Enable Register
// ========== Register definition for TC0 peripheral ========== 
#define AT91C_TC0_SR    ((AT91_REG *) 	0xFFFA0020) // (TC0) Status Register
#define AT91C_TC0_RC    ((AT91_REG *) 	0xFFFA001C) // (TC0) Register C
#define AT91C_TC0_RB    ((AT91_REG *) 	0xFFFA0018) // (TC0) Register B
#define AT91C_TC0_CCR   ((AT91_REG *) 	0xFFFA0000) // (TC0) Channel Control Register
#define AT91C_TC0_CMR   ((AT91_REG *) 	0xFFFA0004) // (TC0) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC0_IER   ((AT91_REG *) 	0xFFFA0024) // (TC0) Interrupt Enable Register
#define AT91C_TC0_RA    ((AT91_REG *) 	0xFFFA0014) // (TC0) Register A
#define AT91C_TC0_IDR   ((AT91_REG *) 	0xFFFA0028) // (TC0) Interrupt Disable Register
#define AT91C_TC0_CV    ((AT91_REG *) 	0xFFFA0010) // (TC0) Counter Value
#define AT91C_TC0_IMR   ((AT91_REG *) 	0xFFFA002C) // (TC0) Interrupt Mask Register
// ========== Register definition for TC1 peripheral ========== 
#define AT91C_TC1_RB    ((AT91_REG *) 	0xFFFA0058) // (TC1) Register B
#define AT91C_TC1_CCR   ((AT91_REG *) 	0xFFFA0040) // (TC1) Channel Control Register
#define AT91C_TC1_IER   ((AT91_REG *) 	0xFFFA0064) // (TC1) Interrupt Enable Register
#define AT91C_TC1_IDR   ((AT91_REG *) 	0xFFFA0068) // (TC1) Interrupt Disable Register
#define AT91C_TC1_SR    ((AT91_REG *) 	0xFFFA0060) // (TC1) Status Register
#define AT91C_TC1_CMR   ((AT91_REG *) 	0xFFFA0044) // (TC1) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC1_RA    ((AT91_REG *) 	0xFFFA0054) // (TC1) Register A
#define AT91C_TC1_RC    ((AT91_REG *) 	0xFFFA005C) // (TC1) Register C
#define AT91C_TC1_IMR   ((AT91_REG *) 	0xFFFA006C) // (TC1) Interrupt Mask Register
#define AT91C_TC1_CV    ((AT91_REG *) 	0xFFFA0050) // (TC1) Counter Value
// ========== Register definition for TC2 peripheral ========== 
#define AT91C_TC2_CMR   ((AT91_REG *) 	0xFFFA0084) // (TC2) Channel Mode Register (Capture Mode / Waveform Mode)
#define AT91C_TC2_CCR   ((AT91_REG *) 	0xFFFA0080) // (TC2) Channel Control Register
#define AT91C_TC2_CV    ((AT91_REG *) 	0xFFFA0090) // (TC2) Counter Value
#define AT91C_TC2_RA    ((AT91_REG *) 	0xFFFA0094) // (TC2) Register A
#define AT91C_TC2_RB    ((AT91_REG *) 	0xFFFA0098) // (TC2) Register B
#define AT91C_TC2_IDR   ((AT91_REG *) 	0xFFFA00A8) // (TC2) Interrupt Disable Register
#define AT91C_TC2_IMR   ((AT91_REG *) 	0xFFFA00AC) // (TC2) Interrupt Mask Register
#define AT91C_TC2_RC    ((AT91_REG *) 	0xFFFA009C) // (TC2) Register C
#define AT91C_TC2_IER   ((AT91_REG *) 	0xFFFA00A4) // (TC2) Interrupt Enable Register
#define AT91C_TC2_SR    ((AT91_REG *) 	0xFFFA00A0) // (TC2) Status Register
// ========== Register definition for TCB peripheral ========== 
#define AT91C_TCB_BMR   ((AT91_REG *) 	0xFFFA00C4) // (TCB) TC Block Mode Register
#define AT91C_TCB_BCR   ((AT91_REG *) 	0xFFFA00C0) // (TCB) TC Block Control Register
// ========== Register definition for CAN_MB0 peripheral ========== 
#define AT91C_CAN_MB0_MDL ((AT91_REG *) 	0xFFFD0214) // (CAN_MB0) MailBox Data Low Register
#define AT91C_CAN_MB0_MAM ((AT91_REG *) 	0xFFFD0204) // (CAN_MB0) MailBox Acceptance Mask Register
#define AT91C_CAN_MB0_MCR ((AT91_REG *) 	0xFFFD021C) // (CAN_MB0) MailBox Control Register
#define AT91C_CAN_MB0_MID ((AT91_REG *) 	0xFFFD0208) // (CAN_MB0) MailBox ID Register
#define AT91C_CAN_MB0_MSR ((AT91_REG *) 	0xFFFD0210) // (CAN_MB0) MailBox Status Register
#define AT91C_CAN_MB0_MFID ((AT91_REG *) 	0xFFFD020C) // (CAN_MB0) MailBox Family ID Register
#define AT91C_CAN_MB0_MDH ((AT91_REG *) 	0xFFFD0218) // (CAN_MB0) MailBox Data High Register
#define AT91C_CAN_MB0_MMR ((AT91_REG *) 	0xFFFD0200) // (CAN_MB0) MailBox Mode Register
// ========== Register definition for CAN_MB1 peripheral ========== 
#define AT91C_CAN_MB1_MDL ((AT91_REG *) 	0xFFFD0234) // (CAN_MB1) MailBox Data Low Register
#define AT91C_CAN_MB1_MID ((AT91_REG *) 	0xFFFD0228) // (CAN_MB1) MailBox ID Register
#define AT91C_CAN_MB1_MMR ((AT91_REG *) 	0xFFFD0220) // (CAN_MB1) MailBox Mode Register
#define AT91C_CAN_MB1_MSR ((AT91_REG *) 	0xFFFD0230) // (CAN_MB1) MailBox Status Register
#define AT91C_CAN_MB1_MAM ((AT91_REG *) 	0xFFFD0224) // (CAN_MB1) MailBox Acceptance Mask Register
#define AT91C_CAN_MB1_MDH ((AT91_REG *) 	0xFFFD0238) // (CAN_MB1) MailBox Data High Register
#define AT91C_CAN_MB1_MCR ((AT91_REG *) 	0xFFFD023C) // (CAN_MB1) MailBox Control Register
#define AT91C_CAN_MB1_MFID ((AT91_REG *) 	0xFFFD022C) // (CAN_MB1) MailBox Family ID Register
// ========== Register definition for CAN_MB2 peripheral ========== 
#define AT91C_CAN_MB2_MCR ((AT91_REG *) 	0xFFFD025C) // (CAN_MB2) MailBox Control Register
#define AT91C_CAN_MB2_MDH ((AT91_REG *) 	0xFFFD0258) // (CAN_MB2) MailBox Data High Register
#define AT91C_CAN_MB2_MID ((AT91_REG *) 	0xFFFD0248) // (CAN_MB2) MailBox ID Register
#define AT91C_CAN_MB2_MDL ((AT91_REG *) 	0xFFFD0254) // (CAN_MB2) MailBox Data Low Register
#define AT91C_CAN_MB2_MMR ((AT91_REG *) 	0xFFFD0240) // (CAN_MB2) MailBox Mode Register
#define AT91C_CAN_MB2_MAM ((AT91_REG *) 	0xFFFD0244) // (CAN_MB2) MailBox Acceptance Mask Register
#define AT91C_CAN_MB2_MFID ((AT91_REG *) 	0xFFFD024C) // (CAN_MB2) MailBox Family ID Register
#define AT91C_CAN_MB2_MSR ((AT91_REG *) 	0xFFFD0250) // (CAN_MB2) MailBox Status Register
// ========== Register definition for CAN_MB3 peripheral ========== 
#define AT91C_CAN_MB3_MFID ((AT91_REG *) 	0xFFFD026C) // (CAN_MB3) MailBox Family ID Register
#define AT91C_CAN_MB3_MAM ((AT91_REG *) 	0xFFFD0264) // (CAN_MB3) MailBox Acceptance Mask Register
#define AT91C_CAN_MB3_MID ((AT91_REG *) 	0xFFFD0268) // (CAN_MB3) MailBox ID Register
#define AT91C_CAN_MB3_MCR ((AT91_REG *) 	0xFFFD027C) // (CAN_MB3) MailBox Control Register
#define AT91C_CAN_MB3_MMR ((AT91_REG *) 	0xFFFD0260) // (CAN_MB3) MailBox Mode Register
#define AT91C_CAN_MB3_MSR ((AT91_REG *) 	0xFFFD0270) // (CAN_MB3) MailBox Status Register
#define AT91C_CAN_MB3_MDL ((AT91_REG *) 	0xFFFD0274) // (CAN_MB3) MailBox Data Low Register
#define AT91C_CAN_MB3_MDH ((AT91_REG *) 	0xFFFD0278) // (CAN_MB3) MailBox Data High Register
// ========== Register definition for CAN_MB4 peripheral ========== 
#define AT91C_CAN_MB4_MID ((AT91_REG *) 	0xFFFD0288) // (CAN_MB4) MailBox ID Register
#define AT91C_CAN_MB4_MMR ((AT91_REG *) 	0xFFFD0280) // (CAN_MB4) MailBox Mode Register
#define AT91C_CAN_MB4_MDH ((AT91_REG *) 	0xFFFD0298) // (CAN_MB4) MailBox Data High Register
#define AT91C_CAN_MB4_MFID ((AT91_REG *) 	0xFFFD028C) // (CAN_MB4) MailBox Family ID Register
#define AT91C_CAN_MB4_MSR ((AT91_REG *) 	0xFFFD0290) // (CAN_MB4) MailBox Status Register
#define AT91C_CAN_MB4_MCR ((AT91_REG *) 	0xFFFD029C) // (CAN_MB4) MailBox Control Register
#define AT91C_CAN_MB4_MDL ((AT91_REG *) 	0xFFFD0294) // (CAN_MB4) MailBox Data Low Register
#define AT91C_CAN_MB4_MAM ((AT91_REG *) 	0xFFFD0284) // (CAN_MB4) MailBox Acceptance Mask Register
// ========== Register definition for CAN_MB5 peripheral ========== 
#define AT91C_CAN_MB5_MSR ((AT91_REG *) 	0xFFFD02B0) // (CAN_MB5) MailBox Status Register
#define AT91C_CAN_MB5_MCR ((AT91_REG *) 	0xFFFD02BC) // (CAN_MB5) MailBox Control Register
#define AT91C_CAN_MB5_MFID ((AT91_REG *) 	0xFFFD02AC) // (CAN_MB5) MailBox Family ID Register
#define AT91C_CAN_MB5_MDH ((AT91_REG *) 	0xFFFD02B8) // (CAN_MB5) MailBox Data High Register
#define AT91C_CAN_MB5_MID ((AT91_REG *) 	0xFFFD02A8) // (CAN_MB5) MailBox ID Register
#define AT91C_CAN_MB5_MMR ((AT91_REG *) 	0xFFFD02A0) // (CAN_MB5) MailBox Mode Register
#define AT91C_CAN_MB5_MDL ((AT91_REG *) 	0xFFFD02B4) // (CAN_MB5) MailBox Data Low Register
#define AT91C_CAN_MB5_MAM ((AT91_REG *) 	0xFFFD02A4) // (CAN_MB5) MailBox Acceptance Mask Register
// ========== Register definition for CAN_MB6 peripheral ========== 
#define AT91C_CAN_MB6_MFID ((AT91_REG *) 	0xFFFD02CC) // (CAN_MB6) MailBox Family ID Register
#define AT91C_CAN_MB6_MID ((AT91_REG *) 	0xFFFD02C8) // (CAN_MB6) MailBox ID Register
#define AT91C_CAN_MB6_MAM ((AT91_REG *) 	0xFFFD02C4) // (CAN_MB6) MailBox Acceptance Mask Register
#define AT91C_CAN_MB6_MSR ((AT91_REG *) 	0xFFFD02D0) // (CAN_MB6) MailBox Status Register
#define AT91C_CAN_MB6_MDL ((AT91_REG *) 	0xFFFD02D4) // (CAN_MB6) MailBox Data Low Register
#define AT91C_CAN_MB6_MCR ((AT91_REG *) 	0xFFFD02DC) // (CAN_MB6) MailBox Control Register
#define AT91C_CAN_MB6_MDH ((AT91_REG *) 	0xFFFD02D8) // (CAN_MB6) MailBox Data High Register
#define AT91C_CAN_MB6_MMR ((AT91_REG *) 	0xFFFD02C0) // (CAN_MB6) MailBox Mode Register
// ========== Register definition for CAN_MB7 peripheral ========== 
#define AT91C_CAN_MB7_MCR ((AT91_REG *) 	0xFFFD02FC) // (CAN_MB7) MailBox Control Register
#define AT91C_CAN_MB7_MDH ((AT91_REG *) 	0xFFFD02F8) // (CAN_MB7) MailBox Data High Register
#define AT91C_CAN_MB7_MFID ((AT91_REG *) 	0xFFFD02EC) // (CAN_MB7) MailBox Family ID Register
#define AT91C_CAN_MB7_MDL ((AT91_REG *) 	0xFFFD02F4) // (CAN_MB7) MailBox Data Low Register
#define AT91C_CAN_MB7_MID ((AT91_REG *) 	0xFFFD02E8) // (CAN_MB7) MailBox ID Register
#define AT91C_CAN_MB7_MMR ((AT91_REG *) 	0xFFFD02E0) // (CAN_MB7) MailBox Mode Register
#define AT91C_CAN_MB7_MAM ((AT91_REG *) 	0xFFFD02E4) // (CAN_MB7) MailBox Acceptance Mask Register
#define AT91C_CAN_MB7_MSR ((AT91_REG *) 	0xFFFD02F0) // (CAN_MB7) MailBox Status Register
// ========== Register definition for CAN peripheral ========== 
#define AT91C_CAN_TCR   ((AT91_REG *) 	0xFFFD0024) // (CAN) Transfer Command Register
#define AT91C_CAN_IMR   ((AT91_REG *) 	0xFFFD000C) // (CAN) Interrupt Mask Register
#define AT91C_CAN_IER   ((AT91_REG *) 	0xFFFD0004) // (CAN) Interrupt Enable Register
#define AT91C_CAN_ECR   ((AT91_REG *) 	0xFFFD0020) // (CAN) Error Counter Register
#define AT91C_CAN_TIMESTP ((AT91_REG *) 	0xFFFD001C) // (CAN) Time Stamp Register
#define AT91C_CAN_MR    ((AT91_REG *) 	0xFFFD0000) // (CAN) Mode Register
#define AT91C_CAN_IDR   ((AT91_REG *) 	0xFFFD0008) // (CAN) Interrupt Disable Register
#define AT91C_CAN_ACR   ((AT91_REG *) 	0xFFFD0028) // (CAN) Abort Command Register
#define AT91C_CAN_TIM   ((AT91_REG *) 	0xFFFD0018) // (CAN) Timer Register
#define AT91C_CAN_SR    ((AT91_REG *) 	0xFFFD0010) // (CAN) Status Register
#define AT91C_CAN_BR    ((AT91_REG *) 	0xFFFD0014) // (CAN) Baudrate Register
#define AT91C_CAN_VR    ((AT91_REG *) 	0xFFFD00FC) // (CAN) Version Register
// ========== Register definition for EMAC peripheral ========== 
#define AT91C_EMAC_ISR  ((AT91_REG *) 	0xFFFDC024) // (EMAC) Interrupt Status Register
#define AT91C_EMAC_SA4H ((AT91_REG *) 	0xFFFDC0B4) // (EMAC) Specific Address 4 Top, Last 2 bytes
#define AT91C_EMAC_SA1L ((AT91_REG *) 	0xFFFDC098) // (EMAC) Specific Address 1 Bottom, First 4 bytes
#define AT91C_EMAC_ELE  ((AT91_REG *) 	0xFFFDC078) // (EMAC) Excessive Length Errors Register
#define AT91C_EMAC_LCOL ((AT91_REG *) 	0xFFFDC05C) // (EMAC) Late Collision Register
#define AT91C_EMAC_RLE  ((AT91_REG *) 	0xFFFDC088) // (EMAC) Receive Length Field Mismatch Register
#define AT91C_EMAC_WOL  ((AT91_REG *) 	0xFFFDC0C4) // (EMAC) Wake On LAN Register
#define AT91C_EMAC_DTF  ((AT91_REG *) 	0xFFFDC058) // (EMAC) Deferred Transmission Frame Register
#define AT91C_EMAC_TUND ((AT91_REG *) 	0xFFFDC064) // (EMAC) Transmit Underrun Error Register
#define AT91C_EMAC_NCR  ((AT91_REG *) 	0xFFFDC000) // (EMAC) Network Control Register
#define AT91C_EMAC_SA4L ((AT91_REG *) 	0xFFFDC0B0) // (EMAC) Specific Address 4 Bottom, First 4 bytes
#define AT91C_EMAC_RSR  ((AT91_REG *) 	0xFFFDC020) // (EMAC) Receive Status Register
#define AT91C_EMAC_SA3L ((AT91_REG *) 	0xFFFDC0A8) // (EMAC) Specific Address 3 Bottom, First 4 bytes
#define AT91C_EMAC_TSR  ((AT91_REG *) 	0xFFFDC014) // (EMAC) Transmit Status Register
#define AT91C_EMAC_IDR  ((AT91_REG *) 	0xFFFDC02C) // (EMAC) Interrupt Disable Register
#define AT91C_EMAC_RSE  ((AT91_REG *) 	0xFFFDC074) // (EMAC) Receive Symbol Errors Register
#define AT91C_EMAC_ECOL ((AT91_REG *) 	0xFFFDC060) // (EMAC) Excessive Collision Register
#define AT91C_EMAC_TID  ((AT91_REG *) 	0xFFFDC0B8) // (EMAC) Type ID Checking Register
#define AT91C_EMAC_HRB  ((AT91_REG *) 	0xFFFDC090) // (EMAC) Hash Address Bottom[31:0]
#define AT91C_EMAC_TBQP ((AT91_REG *) 	0xFFFDC01C) // (EMAC) Transmit Buffer Queue Pointer
#define AT91C_EMAC_USRIO ((AT91_REG *) 	0xFFFDC0C0) // (EMAC) USER Input/Output Register
#define AT91C_EMAC_PTR  ((AT91_REG *) 	0xFFFDC038) // (EMAC) Pause Time Register
#define AT91C_EMAC_SA2H ((AT91_REG *) 	0xFFFDC0A4) // (EMAC) Specific Address 2 Top, Last 2 bytes
#define AT91C_EMAC_ROV  ((AT91_REG *) 	0xFFFDC070) // (EMAC) Receive Overrun Errors Register
#define AT91C_EMAC_ALE  ((AT91_REG *) 	0xFFFDC054) // (EMAC) Alignment Error Register
#define AT91C_EMAC_RJA  ((AT91_REG *) 	0xFFFDC07C) // (EMAC) Receive Jabbers Register
#define AT91C_EMAC_RBQP ((AT91_REG *) 	0xFFFDC018) // (EMAC) Receive Buffer Queue Pointer
#define AT91C_EMAC_TPF  ((AT91_REG *) 	0xFFFDC08C) // (EMAC) Transmitted Pause Frames Register
#define AT91C_EMAC_NCFGR ((AT91_REG *) 	0xFFFDC004) // (EMAC) Network Configuration Register
#define AT91C_EMAC_HRT  ((AT91_REG *) 	0xFFFDC094) // (EMAC) Hash Address Top[63:32]
#define AT91C_EMAC_USF  ((AT91_REG *) 	0xFFFDC080) // (EMAC) Undersize Frames Register
#define AT91C_EMAC_FCSE ((AT91_REG *) 	0xFFFDC050) // (EMAC) Frame Check Sequence Error Register
#define AT91C_EMAC_TPQ  ((AT91_REG *) 	0xFFFDC0BC) // (EMAC) Transmit Pause Quantum Register
#define AT91C_EMAC_MAN  ((AT91_REG *) 	0xFFFDC034) // (EMAC) PHY Maintenance Register
#define AT91C_EMAC_FTO  ((AT91_REG *) 	0xFFFDC040) // (EMAC) Frames Transmitted OK Register
#define AT91C_EMAC_REV  ((AT91_REG *) 	0xFFFDC0FC) // (EMAC) Revision Register
#define AT91C_EMAC_IMR  ((AT91_REG *) 	0xFFFDC030) // (EMAC) Interrupt Mask Register
#define AT91C_EMAC_SCF  ((AT91_REG *) 	0xFFFDC044) // (EMAC) Single Collision Frame Register
#define AT91C_EMAC_PFR  ((AT91_REG *) 	0xFFFDC03C) // (EMAC) Pause Frames received Register
#define AT91C_EMAC_MCF  ((AT91_REG *) 	0xFFFDC048) // (EMAC) Multiple Collision Frame Register
#define AT91C_EMAC_NSR  ((AT91_REG *) 	0xFFFDC008) // (EMAC) Network Status Register
#define AT91C_EMAC_SA2L ((AT91_REG *) 	0xFFFDC0A0) // (EMAC) Specific Address 2 Bottom, First 4 bytes
#define AT91C_EMAC_FRO  ((AT91_REG *) 	0xFFFDC04C) // (EMAC) Frames Received OK Register
#define AT91C_EMAC_IER  ((AT91_REG *) 	0xFFFDC028) // (EMAC) Interrupt Enable Register
#define AT91C_EMAC_SA1H ((AT91_REG *) 	0xFFFDC09C) // (EMAC) Specific Address 1 Top, Last 2 bytes
#define AT91C_EMAC_CSE  ((AT91_REG *) 	0xFFFDC068) // (EMAC) Carrier Sense Error Register
#define AT91C_EMAC_SA3H ((AT91_REG *) 	0xFFFDC0AC) // (EMAC) Specific Address 3 Top, Last 2 bytes
#define AT91C_EMAC_RRE  ((AT91_REG *) 	0xFFFDC06C) // (EMAC) Receive Ressource Error Register
#define AT91C_EMAC_STE  ((AT91_REG *) 	0xFFFDC084) // (EMAC) SQE Test Error Register
// ========== Register definition for PDC_ADC peripheral ========== 
#define AT91C_ADC_PTSR  ((AT91_REG *) 	0xFFFD8124) // (PDC_ADC) PDC Transfer Status Register
#define AT91C_ADC_PTCR  ((AT91_REG *) 	0xFFFD8120) // (PDC_ADC) PDC Transfer Control Register
#define AT91C_ADC_TNPR  ((AT91_REG *) 	0xFFFD8118) // (PDC_ADC) Transmit Next Pointer Register
#define AT91C_ADC_TNCR  ((AT91_REG *) 	0xFFFD811C) // (PDC_ADC) Transmit Next Counter Register
#define AT91C_ADC_RNPR  ((AT91_REG *) 	0xFFFD8110) // (PDC_ADC) Receive Next Pointer Register
#define AT91C_ADC_RNCR  ((AT91_REG *) 	0xFFFD8114) // (PDC_ADC) Receive Next Counter Register
#define AT91C_ADC_RPR   ((AT91_REG *) 	0xFFFD8100) // (PDC_ADC) Receive Pointer Register
#define AT91C_ADC_TCR   ((AT91_REG *) 	0xFFFD810C) // (PDC_ADC) Transmit Counter Register
#define AT91C_ADC_TPR   ((AT91_REG *) 	0xFFFD8108) // (PDC_ADC) Transmit Pointer Register
#define AT91C_ADC_RCR   ((AT91_REG *) 	0xFFFD8104) // (PDC_ADC) Receive Counter Register
// ========== Register definition for ADC peripheral ========== 
#define AT91C_ADC_CDR2  ((AT91_REG *) 	0xFFFD8038) // (ADC) ADC Channel Data Register 2
#define AT91C_ADC_CDR3  ((AT91_REG *) 	0xFFFD803C) // (ADC) ADC Channel Data Register 3
#define AT91C_ADC_CDR0  ((AT91_REG *) 	0xFFFD8030) // (ADC) ADC Channel Data Register 0
#define AT91C_ADC_CDR5  ((AT91_REG *) 	0xFFFD8044) // (ADC) ADC Channel Data Register 5
#define AT91C_ADC_CHDR  ((AT91_REG *) 	0xFFFD8014) // (ADC) ADC Channel Disable Register
#define AT91C_ADC_SR    ((AT91_REG *) 	0xFFFD801C) // (ADC) ADC Status Register
#define AT91C_ADC_CDR4  ((AT91_REG *) 	0xFFFD8040) // (ADC) ADC Channel Data Register 4
#define AT91C_ADC_CDR1  ((AT91_REG *) 	0xFFFD8034) // (ADC) ADC Channel Data Register 1
#define AT91C_ADC_LCDR  ((AT91_REG *) 	0xFFFD8020) // (ADC) ADC Last Converted Data Register
#define AT91C_ADC_IDR   ((AT91_REG *) 	0xFFFD8028) // (ADC) ADC Interrupt Disable Register
#define AT91C_ADC_CR    ((AT91_REG *) 	0xFFFD8000) // (ADC) ADC Control Register
#define AT91C_ADC_CDR7  ((AT91_REG *) 	0xFFFD804C) // (ADC) ADC Channel Data Register 7
#define AT91C_ADC_CDR6  ((AT91_REG *) 	0xFFFD8048) // (ADC) ADC Channel Data Register 6
#define AT91C_ADC_IER   ((AT91_REG *) 	0xFFFD8024) // (ADC) ADC Interrupt Enable Register
#define AT91C_ADC_CHER  ((AT91_REG *) 	0xFFFD8010) // (ADC) ADC Channel Enable Register
#define AT91C_ADC_CHSR  ((AT91_REG *) 	0xFFFD8018) // (ADC) ADC Channel Status Register
#define AT91C_ADC_MR    ((AT91_REG *) 	0xFFFD8004) // (ADC) ADC Mode Register
#define AT91C_ADC_IMR   ((AT91_REG *) 	0xFFFD802C) // (ADC) ADC Interrupt Mask Register
// ========== Register definition for PDC_AES peripheral ========== 
#define AT91C_AES_TPR   ((AT91_REG *) 	0xFFFA4108) // (PDC_AES) Transmit Pointer Register
#define AT91C_AES_PTCR  ((AT91_REG *) 	0xFFFA4120) // (PDC_AES) PDC Transfer Control Register
#define AT91C_AES_RNPR  ((AT91_REG *) 	0xFFFA4110) // (PDC_AES) Receive Next Pointer Register
#define AT91C_AES_TNCR  ((AT91_REG *) 	0xFFFA411C) // (PDC_AES) Transmit Next Counter Register
#define AT91C_AES_TCR   ((AT91_REG *) 	0xFFFA410C) // (PDC_AES) Transmit Counter Register
#define AT91C_AES_RCR   ((AT91_REG *) 	0xFFFA4104) // (PDC_AES) Receive Counter Register
#define AT91C_AES_RNCR  ((AT91_REG *) 	0xFFFA4114) // (PDC_AES) Receive Next Counter Register
#define AT91C_AES_TNPR  ((AT91_REG *) 	0xFFFA4118) // (PDC_AES) Transmit Next Pointer Register
#define AT91C_AES_RPR   ((AT91_REG *) 	0xFFFA4100) // (PDC_AES) Receive Pointer Register
#define AT91C_AES_PTSR  ((AT91_REG *) 	0xFFFA4124) // (PDC_AES) PDC Transfer Status Register
// ========== Register definition for AES peripheral ========== 
#define AT91C_AES_IVxR  ((AT91_REG *) 	0xFFFA4060) // (AES) Initialization Vector x Register
#define AT91C_AES_MR    ((AT91_REG *) 	0xFFFA4004) // (AES) Mode Register
#define AT91C_AES_VR    ((AT91_REG *) 	0xFFFA40FC) // (AES) AES Version Register
#define AT91C_AES_ODATAxR ((AT91_REG *) 	0xFFFA4050) // (AES) Output Data x Register
#define AT91C_AES_IDATAxR ((AT91_REG *) 	0xFFFA4040) // (AES) Input Data x Register
#define AT91C_AES_CR    ((AT91_REG *) 	0xFFFA4000) // (AES) Control Register
#define AT91C_AES_IDR   ((AT91_REG *) 	0xFFFA4014) // (AES) Interrupt Disable Register
#define AT91C_AES_IMR   ((AT91_REG *) 	0xFFFA4018) // (AES) Interrupt Mask Register
#define AT91C_AES_IER   ((AT91_REG *) 	0xFFFA4010) // (AES) Interrupt Enable Register
#define AT91C_AES_KEYWxR ((AT91_REG *) 	0xFFFA4020) // (AES) Key Word x Register
#define AT91C_AES_ISR   ((AT91_REG *) 	0xFFFA401C) // (AES) Interrupt Status Register
// ========== Register definition for PDC_TDES peripheral ========== 
#define AT91C_TDES_RNCR ((AT91_REG *) 	0xFFFA8114) // (PDC_TDES) Receive Next Counter Register
#define AT91C_TDES_TCR  ((AT91_REG *) 	0xFFFA810C) // (PDC_TDES) Transmit Counter Register
#define AT91C_TDES_RCR  ((AT91_REG *) 	0xFFFA8104) // (PDC_TDES) Receive Counter Register
#define AT91C_TDES_TNPR ((AT91_REG *) 	0xFFFA8118) // (PDC_TDES) Transmit Next Pointer Register
#define AT91C_TDES_RNPR ((AT91_REG *) 	0xFFFA8110) // (PDC_TDES) Receive Next Pointer Register
#define AT91C_TDES_RPR  ((AT91_REG *) 	0xFFFA8100) // (PDC_TDES) Receive Pointer Register
#define AT91C_TDES_TNCR ((AT91_REG *) 	0xFFFA811C) // (PDC_TDES) Transmit Next Counter Register
#define AT91C_TDES_TPR  ((AT91_REG *) 	0xFFFA8108) // (PDC_TDES) Transmit Pointer Register
#define AT91C_TDES_PTSR ((AT91_REG *) 	0xFFFA8124) // (PDC_TDES) PDC Transfer Status Register
#define AT91C_TDES_PTCR ((AT91_REG *) 	0xFFFA8120) // (PDC_TDES) PDC Transfer Control Register
// ========== Register definition for TDES peripheral ========== 
#define AT91C_TDES_KEY2WxR ((AT91_REG *) 	0xFFFA8028) // (TDES) Key 2 Word x Register
#define AT91C_TDES_KEY3WxR ((AT91_REG *) 	0xFFFA8030) // (TDES) Key 3 Word x Register
#define AT91C_TDES_IDR  ((AT91_REG *) 	0xFFFA8014) // (TDES) Interrupt Disable Register
#define AT91C_TDES_VR   ((AT91_REG *) 	0xFFFA80FC) // (TDES) TDES Version Register
#define AT91C_TDES_IVxR ((AT91_REG *) 	0xFFFA8060) // (TDES) Initialization Vector x Register
#define AT91C_TDES_ODATAxR ((AT91_REG *) 	0xFFFA8050) // (TDES) Output Data x Register
#define AT91C_TDES_IMR  ((AT91_REG *) 	0xFFFA8018) // (TDES) Interrupt Mask Register
#define AT91C_TDES_MR   ((AT91_REG *) 	0xFFFA8004) // (TDES) Mode Register
#define AT91C_TDES_CR   ((AT91_REG *) 	0xFFFA8000) // (TDES) Control Register
#define AT91C_TDES_IER  ((AT91_REG *) 	0xFFFA8010) // (TDES) Interrupt Enable Register
#define AT91C_TDES_ISR  ((AT91_REG *) 	0xFFFA801C) // (TDES) Interrupt Status Register
#define AT91C_TDES_IDATAxR ((AT91_REG *) 	0xFFFA8040) // (TDES) Input Data x Register
#define AT91C_TDES_KEY1WxR ((AT91_REG *) 	0xFFFA8020) // (TDES) Key 1 Word x Register

// *****************************************************************************
//               PIO DEFINITIONS FOR AT91SAM7X128
// *****************************************************************************
#define AT91C_PIO_PA0        ((unsigned int) 1 <<  0) // Pin Controlled by PA0
#define AT91C_PA0_RXD0     ((unsigned int) AT91C_PIO_PA0) //  USART 0 Receive Data
#define AT91C_PIO_PA1        ((unsigned int) 1 <<  1) // Pin Controlled by PA1
#define AT91C_PA1_TXD0     ((unsigned int) AT91C_PIO_PA1) //  USART 0 Transmit Data
#define AT91C_PIO_PA10       ((unsigned int) 1 << 10) // Pin Controlled by PA10
#define AT91C_PA10_TWD      ((unsigned int) AT91C_PIO_PA10) //  TWI Two-wire Serial Data
#define AT91C_PIO_PA11       ((unsigned int) 1 << 11) // Pin Controlled by PA11
#define AT91C_PA11_TWCK     ((unsigned int) AT91C_PIO_PA11) //  TWI Two-wire Serial Clock
#define AT91C_PIO_PA12       ((unsigned int) 1 << 12) // Pin Controlled by PA12
#define AT91C_PA12_NPCS00   ((unsigned int) AT91C_PIO_PA12) //  SPI 0 Peripheral Chip Select 0
#define AT91C_PIO_PA13       ((unsigned int) 1 << 13) // Pin Controlled by PA13
#define AT91C_PA13_NPCS01   ((unsigned int) AT91C_PIO_PA13) //  SPI 0 Peripheral Chip Select 1
#define AT91C_PA13_PCK1     ((unsigned int) AT91C_PIO_PA13) //  PMC Programmable Clock Output 1
#define AT91C_PIO_PA14       ((unsigned int) 1 << 14) // Pin Controlled by PA14
#define AT91C_PA14_NPCS02   ((unsigned int) AT91C_PIO_PA14) //  SPI 0 Peripheral Chip Select 2
#define AT91C_PA14_IRQ1     ((unsigned int) AT91C_PIO_PA14) //  External Interrupt 1
#define AT91C_PIO_PA15       ((unsigned int) 1 << 15) // Pin Controlled by PA15
#define AT91C_PA15_NPCS03   ((unsigned int) AT91C_PIO_PA15) //  SPI 0 Peripheral Chip Select 3
#define AT91C_PA15_TCLK2    ((unsigned int) AT91C_PIO_PA15) //  Timer Counter 2 external clock input
#define AT91C_PIO_PA16       ((unsigned int) 1 << 16) // Pin Controlled by PA16
#define AT91C_PA16_MISO0    ((unsigned int) AT91C_PIO_PA16) //  SPI 0 Master In Slave
#define AT91C_PIO_PA17       ((unsigned int) 1 << 17) // Pin Controlled by PA17
#define AT91C_PA17_MOSI0    ((unsigned int) AT91C_PIO_PA17) //  SPI 0 Master Out Slave
#define AT91C_PIO_PA18       ((unsigned int) 1 << 18) // Pin Controlled by PA18
#define AT91C_PA18_SPCK0    ((unsigned int) AT91C_PIO_PA18) //  SPI 0 Serial Clock
#define AT91C_PIO_PA19       ((unsigned int) 1 << 19) // Pin Controlled by PA19
#define AT91C_PA19_CANRX    ((unsigned int) AT91C_PIO_PA19) //  CAN Receive
#define AT91C_PIO_PA2        ((unsigned int) 1 <<  2) // Pin Controlled by PA2
#define AT91C_PA2_SCK0     ((unsigned int) AT91C_PIO_PA2) //  USART 0 Serial Clock
#define AT91C_PA2_NPCS11   ((unsigned int) AT91C_PIO_PA2) //  SPI 1 Peripheral Chip Select 1
#define AT91C_PIO_PA20       ((unsigned int) 1 << 20) // Pin Controlled by PA20
#define AT91C_PA20_CANTX    ((unsigned int) AT91C_PIO_PA20) //  CAN Transmit
#define AT91C_PIO_PA21       ((unsigned int) 1 << 21) // Pin Controlled by PA21
#define AT91C_PA21_TF       ((unsigned int) AT91C_PIO_PA21) //  SSC Transmit Frame Sync
#define AT91C_PA21_NPCS10   ((unsigned int) AT91C_PIO_PA21) //  SPI 1 Peripheral Chip Select 0
#define AT91C_PIO_PA22       ((unsigned int) 1 << 22) // Pin Controlled by PA22
#define AT91C_PA22_TK       ((unsigned int) AT91C_PIO_PA22) //  SSC Transmit Clock
#define AT91C_PA22_SPCK1    ((unsigned int) AT91C_PIO_PA22) //  SPI 1 Serial Clock
#define AT91C_PIO_PA23       ((unsigned int) 1 << 23) // Pin Controlled by PA23
#define AT91C_PA23_TD       ((unsigned int) AT91C_PIO_PA23) //  SSC Transmit data
#define AT91C_PA23_MOSI1    ((unsigned int) AT91C_PIO_PA23) //  SPI 1 Master Out Slave
#define AT91C_PIO_PA24       ((unsigned int) 1 << 24) // Pin Controlled by PA24
#define AT91C_PA24_RD       ((unsigned int) AT91C_PIO_PA24) //  SSC Receive Data
#define AT91C_PA24_MISO1    ((unsigned int) AT91C_PIO_PA24) //  SPI 1 Master In Slave
#define AT91C_PIO_PA25       ((unsigned int) 1 << 25) // Pin Controlled by PA25
#define AT91C_PA25_RK       ((unsigned int) AT91C_PIO_PA25) //  SSC Receive Clock
#define AT91C_PA25_NPCS11   ((unsigned int) AT91C_PIO_PA25) //  SPI 1 Peripheral Chip Select 1
#define AT91C_PIO_PA26       ((unsigned int) 1 << 26) // Pin Controlled by PA26
#define AT91C_PA26_RF       ((unsigned int) AT91C_PIO_PA26) //  SSC Receive Frame Sync
#define AT91C_PA26_NPCS12   ((unsigned int) AT91C_PIO_PA26) //  SPI 1 Peripheral Chip Select 2
#define AT91C_PIO_PA27       ((unsigned int) 1 << 27) // Pin Controlled by PA27
#define AT91C_PA27_DRXD     ((unsigned int) AT91C_PIO_PA27) //  DBGU Debug Receive Data
#define AT91C_PA27_PCK3     ((unsigned int) AT91C_PIO_PA27) //  PMC Programmable Clock Output 3
#define AT91C_PIO_PA28       ((unsigned int) 1 << 28) // Pin Controlled by PA28
#define AT91C_PA28_DTXD     ((unsigned int) AT91C_PIO_PA28) //  DBGU Debug Transmit Data
#define AT91C_PIO_PA29       ((unsigned int) 1 << 29) // Pin Controlled by PA29
#define AT91C_PA29_FIQ      ((unsigned int) AT91C_PIO_PA29) //  AIC Fast Interrupt Input
#define AT91C_PA29_NPCS13   ((unsigned int) AT91C_PIO_PA29) //  SPI 1 Peripheral Chip Select 3
#define AT91C_PIO_PA3        ((unsigned int) 1 <<  3) // Pin Controlled by PA3
#define AT91C_PA3_RTS0     ((unsigned int) AT91C_PIO_PA3) //  USART 0 Ready To Send
#define AT91C_PA3_NPCS12   ((unsigned int) AT91C_PIO_PA3) //  SPI 1 Peripheral Chip Select 2
#define AT91C_PIO_PA30       ((unsigned int) 1 << 30) // Pin Controlled by PA30
#define AT91C_PA30_IRQ0     ((unsigned int) AT91C_PIO_PA30) //  External Interrupt 0
#define AT91C_PA30_PCK2     ((unsigned int) AT91C_PIO_PA30) //  PMC Programmable Clock Output 2
#define AT91C_PIO_PA4        ((unsigned int) 1 <<  4) // Pin Controlled by PA4
#define AT91C_PA4_CTS0     ((unsigned int) AT91C_PIO_PA4) //  USART 0 Clear To Send
#define AT91C_PA4_NPCS13   ((unsigned int) AT91C_PIO_PA4) //  SPI 1 Peripheral Chip Select 3
#define AT91C_PIO_PA5        ((unsigned int) 1 <<  5) // Pin Controlled by PA5
#define AT91C_PA5_RXD1     ((unsigned int) AT91C_PIO_PA5) //  USART 1 Receive Data
#define AT91C_PIO_PA6        ((unsigned int) 1 <<  6) // Pin Controlled by PA6
#define AT91C_PA6_TXD1     ((unsigned int) AT91C_PIO_PA6) //  USART 1 Transmit Data
#define AT91C_PIO_PA7        ((unsigned int) 1 <<  7) // Pin Controlled by PA7
#define AT91C_PA7_SCK1     ((unsigned int) AT91C_PIO_PA7) //  USART 1 Serial Clock
#define AT91C_PA7_NPCS01   ((unsigned int) AT91C_PIO_PA7) //  SPI 0 Peripheral Chip Select 1
#define AT91C_PIO_PA8        ((unsigned int) 1 <<  8) // Pin Controlled by PA8
#define AT91C_PA8_RTS1     ((unsigned int) AT91C_PIO_PA8) //  USART 1 Ready To Send
#define AT91C_PA8_NPCS02   ((unsigned int) AT91C_PIO_PA8) //  SPI 0 Peripheral Chip Select 2
#define AT91C_PIO_PA9        ((unsigned int) 1 <<  9) // Pin Controlled by PA9
#define AT91C_PA9_CTS1     ((unsigned int) AT91C_PIO_PA9) //  USART 1 Clear To Send
#define AT91C_PA9_NPCS03   ((unsigned int) AT91C_PIO_PA9) //  SPI 0 Peripheral Chip Select 3
#define AT91C_PIO_PB0        ((unsigned int) 1 <<  0) // Pin Controlled by PB0
#define AT91C_PB0_ETXCK_EREFCK ((unsigned int) AT91C_PIO_PB0) //  Ethernet MAC Transmit Clock/Reference Clock
#define AT91C_PB0_PCK0     ((unsigned int) AT91C_PIO_PB0) //  PMC Programmable Clock Output 0
#define AT91C_PIO_PB1        ((unsigned int) 1 <<  1) // Pin Controlled by PB1
#define AT91C_PB1_ETXEN    ((unsigned int) AT91C_PIO_PB1) //  Ethernet MAC Transmit Enable
#define AT91C_PIO_PB10       ((unsigned int) 1 << 10) // Pin Controlled by PB10
#define AT91C_PB10_ETX2     ((unsigned int) AT91C_PIO_PB10) //  Ethernet MAC Transmit Data 2
#define AT91C_PB10_NPCS11   ((unsigned int) AT91C_PIO_PB10) //  SPI 1 Peripheral Chip Select 1
#define AT91C_PIO_PB11       ((unsigned int) 1 << 11) // Pin Controlled by PB11
#define AT91C_PB11_ETX3     ((unsigned int) AT91C_PIO_PB11) //  Ethernet MAC Transmit Data 3
#define AT91C_PB11_NPCS12   ((unsigned int) AT91C_PIO_PB11) //  SPI 1 Peripheral Chip Select 2
#define AT91C_PIO_PB12       ((unsigned int) 1 << 12) // Pin Controlled by PB12
#define AT91C_PB12_ETXER    ((unsigned int) AT91C_PIO_PB12) //  Ethernet MAC Transmikt Coding Error
#define AT91C_PB12_TCLK0    ((unsigned int) AT91C_PIO_PB12) //  Timer Counter 0 external clock input
#define AT91C_PIO_PB13       ((unsigned int) 1 << 13) // Pin Controlled by PB13
#define AT91C_PB13_ERX2     ((unsigned int) AT91C_PIO_PB13) //  Ethernet MAC Receive Data 2
#define AT91C_PB13_NPCS01   ((unsigned int) AT91C_PIO_PB13) //  SPI 0 Peripheral Chip Select 1
#define AT91C_PIO_PB14       ((unsigned int) 1 << 14) // Pin Controlled by PB14
#define AT91C_PB14_ERX3     ((unsigned int) AT91C_PIO_PB14) //  Ethernet MAC Receive Data 3
#define AT91C_PB14_NPCS02   ((unsigned int) AT91C_PIO_PB14) //  SPI 0 Peripheral Chip Select 2
#define AT91C_PIO_PB15       ((unsigned int) 1 << 15) // Pin Controlled by PB15
#define AT91C_PB15_ERXDV    ((unsigned int) AT91C_PIO_PB15) //  Ethernet MAC Receive Data Valid
#define AT91C_PIO_PB16       ((unsigned int) 1 << 16) // Pin Controlled by PB16
#define AT91C_PB16_ECOL     ((unsigned int) AT91C_PIO_PB16) //  Ethernet MAC Collision Detected
#define AT91C_PB16_NPCS13   ((unsigned int) AT91C_PIO_PB16) //  SPI 1 Peripheral Chip Select 3
#define AT91C_PIO_PB17       ((unsigned int) 1 << 17) // Pin Controlled by PB17
#define AT91C_PB17_ERXCK    ((unsigned int) AT91C_PIO_PB17) //  Ethernet MAC Receive Clock
#define AT91C_PB17_NPCS03   ((unsigned int) AT91C_PIO_PB17) //  SPI 0 Peripheral Chip Select 3
#define AT91C_PIO_PB18       ((unsigned int) 1 << 18) // Pin Controlled by PB18
#define AT91C_PB18_EF100    ((unsigned int) AT91C_PIO_PB18) //  Ethernet MAC Force 100 Mbits/sec
#define AT91C_PB18_ADTRG    ((unsigned int) AT91C_PIO_PB18) //  ADC External Trigger
#define AT91C_PIO_PB19       ((unsigned int) 1 << 19) // Pin Controlled by PB19
#define AT91C_PB19_PWM0     ((unsigned int) AT91C_PIO_PB19) //  PWM Channel 0
#define AT91C_PB19_TCLK1    ((unsigned int) AT91C_PIO_PB19) //  Timer Counter 1 external clock input
#define AT91C_PIO_PB2        ((unsigned int) 1 <<  2) // Pin Controlled by PB2
#define AT91C_PB2_ETX0     ((unsigned int) AT91C_PIO_PB2) //  Ethernet MAC Transmit Data 0
#define AT91C_PIO_PB20       ((unsigned int) 1 << 20) // Pin Controlled by PB20
#define AT91C_PB20_PWM1     ((unsigned int) AT91C_PIO_PB20) //  PWM Channel 1
#define AT91C_PB20_PCK0     ((unsigned int) AT91C_PIO_PB20) //  PMC Programmable Clock Output 0
#define AT91C_PIO_PB21       ((unsigned int) 1 << 21) // Pin Controlled by PB21
#define AT91C_PB21_PWM2     ((unsigned int) AT91C_PIO_PB21) //  PWM Channel 2
#define AT91C_PB21_PCK1     ((unsigned int) AT91C_PIO_PB21) //  PMC Programmable Clock Output 1
#define AT91C_PIO_PB22       ((unsigned int) 1 << 22) // Pin Controlled by PB22
#define AT91C_PB22_PWM3     ((unsigned int) AT91C_PIO_PB22) //  PWM Channel 3
#define AT91C_PB22_PCK2     ((unsigned int) AT91C_PIO_PB22) //  PMC Programmable Clock Output 2
#define AT91C_PIO_PB23       ((unsigned int) 1 << 23) // Pin Controlled by PB23
#define AT91C_PB23_TIOA0    ((unsigned int) AT91C_PIO_PB23) //  Timer Counter 0 Multipurpose Timer I/O Pin A
#define AT91C_PB23_DCD1     ((unsigned int) AT91C_PIO_PB23) //  USART 1 Data Carrier Detect
#define AT91C_PIO_PB24       ((unsigned int) 1 << 24) // Pin Controlled by PB24
#define AT91C_PB24_TIOB0    ((unsigned int) AT91C_PIO_PB24) //  Timer Counter 0 Multipurpose Timer I/O Pin B
#define AT91C_PB24_DSR1     ((unsigned int) AT91C_PIO_PB24) //  USART 1 Data Set ready
#define AT91C_PIO_PB25       ((unsigned int) 1 << 25) // Pin Controlled by PB25
#define AT91C_PB25_TIOA1    ((unsigned int) AT91C_PIO_PB25) //  Timer Counter 1 Multipurpose Timer I/O Pin A
#define AT91C_PB25_DTR1     ((unsigned int) AT91C_PIO_PB25) //  USART 1 Data Terminal ready
#define AT91C_PIO_PB26       ((unsigned int) 1 << 26) // Pin Controlled by PB26
#define AT91C_PB26_TIOB1    ((unsigned int) AT91C_PIO_PB26) //  Timer Counter 1 Multipurpose Timer I/O Pin B
#define AT91C_PB26_RI1      ((unsigned int) AT91C_PIO_PB26) //  USART 1 Ring Indicator
#define AT91C_PIO_PB27       ((unsigned int) 1 << 27) // Pin Controlled by PB27
#define AT91C_PB27_TIOA2    ((unsigned int) AT91C_PIO_PB27) //  Timer Counter 2 Multipurpose Timer I/O Pin A
#define AT91C_PB27_PWM0     ((unsigned int) AT91C_PIO_PB27) //  PWM Channel 0
#define AT91C_PIO_PB28       ((unsigned int) 1 << 28) // Pin Controlled by PB28
#define AT91C_PB28_TIOB2    ((unsigned int) AT91C_PIO_PB28) //  Timer Counter 2 Multipurpose Timer I/O Pin B
#define AT91C_PB28_PWM1     ((unsigned int) AT91C_PIO_PB28) //  PWM Channel 1
#define AT91C_PIO_PB29       ((unsigned int) 1 << 29) // Pin Controlled by PB29
#define AT91C_PB29_PCK1     ((unsigned int) AT91C_PIO_PB29) //  PMC Programmable Clock Output 1
#define AT91C_PB29_PWM2     ((unsigned int) AT91C_PIO_PB29) //  PWM Channel 2
#define AT91C_PIO_PB3        ((unsigned int) 1 <<  3) // Pin Controlled by PB3
#define AT91C_PB3_ETX1     ((unsigned int) AT91C_PIO_PB3) //  Ethernet MAC Transmit Data 1
#define AT91C_PIO_PB30       ((unsigned int) 1 << 30) // Pin Controlled by PB30
#define AT91C_PB30_PCK2     ((unsigned int) AT91C_PIO_PB30) //  PMC Programmable Clock Output 2
#define AT91C_PB30_PWM3     ((unsigned int) AT91C_PIO_PB30) //  PWM Channel 3
#define AT91C_PIO_PB4        ((unsigned int) 1 <<  4) // Pin Controlled by PB4
#define AT91C_PB4_ECRS_ECRSDV ((unsigned int) AT91C_PIO_PB4) //  Ethernet MAC Carrier Sense/Carrier Sense and Data Valid
#define AT91C_PIO_PB5        ((unsigned int) 1 <<  5) // Pin Controlled by PB5
#define AT91C_PB5_ERX0     ((unsigned int) AT91C_PIO_PB5) //  Ethernet MAC Receive Data 0
#define AT91C_PIO_PB6        ((unsigned int) 1 <<  6) // Pin Controlled by PB6
#define AT91C_PB6_ERX1     ((unsigned int) AT91C_PIO_PB6) //  Ethernet MAC Receive Data 1
#define AT91C_PIO_PB7        ((unsigned int) 1 <<  7) // Pin Controlled by PB7
#define AT91C_PB7_ERXER    ((unsigned int) AT91C_PIO_PB7) //  Ethernet MAC Receive Error
#define AT91C_PIO_PB8        ((unsigned int) 1 <<  8) // Pin Controlled by PB8
#define AT91C_PB8_EMDC     ((unsigned int) AT91C_PIO_PB8) //  Ethernet MAC Management Data Clock
#define AT91C_PIO_PB9        ((unsigned int) 1 <<  9) // Pin Controlled by PB9
#define AT91C_PB9_EMDIO    ((unsigned int) AT91C_PIO_PB9) //  Ethernet MAC Management Data Input/Output

// *****************************************************************************
//               PERIPHERAL ID DEFINITIONS FOR AT91SAM7X128
// *****************************************************************************
#define AT91C_ID_FIQ    ((unsigned int)  0) // Advanced Interrupt Controller (FIQ)
#define AT91C_ID_SYS    ((unsigned int)  1) // System Peripheral
#define AT91C_ID_PIOA   ((unsigned int)  2) // Parallel IO Controller A
#define AT91C_ID_PIOB   ((unsigned int)  3) // Parallel IO Controller B
#define AT91C_ID_SPI0   ((unsigned int)  4) // Serial Peripheral Interface 0
#define AT91C_ID_SPI1   ((unsigned int)  5) // Serial Peripheral Interface 1
#define AT91C_ID_US0    ((unsigned int)  6) // USART 0
#define AT91C_ID_US1    ((unsigned int)  7) // USART 1
#define AT91C_ID_SSC    ((unsigned int)  8) // Serial Synchronous Controller
#define AT91C_ID_TWI    ((unsigned int)  9) // Two-Wire Interface
#define AT91C_ID_PWMC   ((unsigned int) 10) // PWM Controller
#define AT91C_ID_UDP    ((unsigned int) 11) // USB Device Port
#define AT91C_ID_TC0    ((unsigned int) 12) // Timer Counter 0
#define AT91C_ID_TC1    ((unsigned int) 13) // Timer Counter 1
#define AT91C_ID_TC2    ((unsigned int) 14) // Timer Counter 2
#define AT91C_ID_CAN    ((unsigned int) 15) // Control Area Network Controller
#define AT91C_ID_EMAC   ((unsigned int) 16) // Ethernet MAC
#define AT91C_ID_ADC    ((unsigned int) 17) // Analog-to-Digital Converter
#define AT91C_ID_AES    ((unsigned int) 18) // Advanced Encryption Standard 128-bit
#define AT91C_ID_TDES   ((unsigned int) 19) // Triple Data Encryption Standard
#define AT91C_ID_20_Reserved ((unsigned int) 20) // Reserved
#define AT91C_ID_21_Reserved ((unsigned int) 21) // Reserved
#define AT91C_ID_22_Reserved ((unsigned int) 22) // Reserved
#define AT91C_ID_23_Reserved ((unsigned int) 23) // Reserved
#define AT91C_ID_24_Reserved ((unsigned int) 24) // Reserved
#define AT91C_ID_25_Reserved ((unsigned int) 25) // Reserved
#define AT91C_ID_26_Reserved ((unsigned int) 26) // Reserved
#define AT91C_ID_27_Reserved ((unsigned int) 27) // Reserved
#define AT91C_ID_28_Reserved ((unsigned int) 28) // Reserved
#define AT91C_ID_29_Reserved ((unsigned int) 29) // Reserved
#define AT91C_ID_IRQ0   ((unsigned int) 30) // Advanced Interrupt Controller (IRQ0)
#define AT91C_ID_IRQ1   ((unsigned int) 31) // Advanced Interrupt Controller (IRQ1)

// *****************************************************************************
//               BASE ADDRESS DEFINITIONS FOR AT91SAM7X128
// *****************************************************************************
#define AT91C_BASE_SYS       ((AT91PS_SYS) 	0xFFFFF000) // (SYS) Base Address
#define AT91C_BASE_AIC       ((AT91PS_AIC) 	0xFFFFF000) // (AIC) Base Address
#define AT91C_BASE_PDC_DBGU  ((AT91PS_PDC) 	0xFFFFF300) // (PDC_DBGU) Base Address
#define AT91C_BASE_DBGU      ((AT91PS_DBGU) 	0xFFFFF200) // (DBGU) Base Address
#define AT91C_BASE_PIOA      ((AT91PS_PIO) 	0xFFFFF400) // (PIOA) Base Address
#define AT91C_BASE_PIOB      ((AT91PS_PIO) 	0xFFFFF600) // (PIOB) Base Address
#define AT91C_BASE_CKGR      ((AT91PS_CKGR) 	0xFFFFFC20) // (CKGR) Base Address
#define AT91C_BASE_PMC       ((AT91PS_PMC) 	0xFFFFFC00) // (PMC) Base Address
#define AT91C_BASE_RSTC      ((AT91PS_RSTC) 	0xFFFFFD00) // (RSTC) Base Address
#define AT91C_BASE_RTTC      ((AT91PS_RTTC) 	0xFFFFFD20) // (RTTC) Base Address
#define AT91C_BASE_PITC      ((AT91PS_PITC) 	0xFFFFFD30) // (PITC) Base Address
#define AT91C_BASE_WDTC      ((AT91PS_WDTC) 	0xFFFFFD40) // (WDTC) Base Address
#define AT91C_BASE_VREG      ((AT91PS_VREG) 	0xFFFFFD60) // (VREG) Base Address
#define AT91C_BASE_MC        ((AT91PS_MC) 	0xFFFFFF00) // (MC) Base Address
#define AT91C_BASE_PDC_SPI1  ((AT91PS_PDC) 	0xFFFE4100) // (PDC_SPI1) Base Address
#define AT91C_BASE_SPI1      ((AT91PS_SPI) 	0xFFFE4000) // (SPI1) Base Address
#define AT91C_BASE_PDC_SPI0  ((AT91PS_PDC) 	0xFFFE0100) // (PDC_SPI0) Base Address
#define AT91C_BASE_SPI0      ((AT91PS_SPI) 	0xFFFE0000) // (SPI0) Base Address
#define AT91C_BASE_PDC_US1   ((AT91PS_PDC) 	0xFFFC4100) // (PDC_US1) Base Address
#define AT91C_BASE_US1       ((AT91PS_USART) 	0xFFFC4000) // (US1) Base Address
#define AT91C_BASE_PDC_US0   ((AT91PS_PDC) 	0xFFFC0100) // (PDC_US0) Base Address
#define AT91C_BASE_US0       ((AT91PS_USART) 	0xFFFC0000) // (US0) Base Address
#define AT91C_BASE_PDC_SSC   ((AT91PS_PDC) 	0xFFFD4100) // (PDC_SSC) Base Address
#define AT91C_BASE_SSC       ((AT91PS_SSC) 	0xFFFD4000) // (SSC) Base Address
#define AT91C_BASE_TWI       ((AT91PS_TWI) 	0xFFFB8000) // (TWI) Base Address
#define AT91C_BASE_PWMC_CH3  ((AT91PS_PWMC_CH) 	0xFFFCC260) // (PWMC_CH3) Base Address
#define AT91C_BASE_PWMC_CH2  ((AT91PS_PWMC_CH) 	0xFFFCC240) // (PWMC_CH2) Base Address
#define AT91C_BASE_PWMC_CH1  ((AT91PS_PWMC_CH) 	0xFFFCC220) // (PWMC_CH1) Base Address
#define AT91C_BASE_PWMC_CH0  ((AT91PS_PWMC_CH) 	0xFFFCC200) // (PWMC_CH0) Base Address
#define AT91C_BASE_PWMC      ((AT91PS_PWMC) 	0xFFFCC000) // (PWMC) Base Address
#define AT91C_BASE_UDP       ((AT91PS_UDP) 	0xFFFB0000) // (UDP) Base Address
#define AT91C_BASE_TC0       ((AT91PS_TC) 	0xFFFA0000) // (TC0) Base Address
#define AT91C_BASE_TC1       ((AT91PS_TC) 	0xFFFA0040) // (TC1) Base Address
#define AT91C_BASE_TC2       ((AT91PS_TC) 	0xFFFA0080) // (TC2) Base Address
#define AT91C_BASE_TCB       ((AT91PS_TCB) 	0xFFFA0000) // (TCB) Base Address
#define AT91C_BASE_CAN_MB0   ((AT91PS_CAN_MB) 	0xFFFD0200) // (CAN_MB0) Base Address
#define AT91C_BASE_CAN_MB1   ((AT91PS_CAN_MB) 	0xFFFD0220) // (CAN_MB1) Base Address
#define AT91C_BASE_CAN_MB2   ((AT91PS_CAN_MB) 	0xFFFD0240) // (CAN_MB2) Base Address
#define AT91C_BASE_CAN_MB3   ((AT91PS_CAN_MB) 	0xFFFD0260) // (CAN_MB3) Base Address
#define AT91C_BASE_CAN_MB4   ((AT91PS_CAN_MB) 	0xFFFD0280) // (CAN_MB4) Base Address
#define AT91C_BASE_CAN_MB5   ((AT91PS_CAN_MB) 	0xFFFD02A0) // (CAN_MB5) Base Address
#define AT91C_BASE_CAN_MB6   ((AT91PS_CAN_MB) 	0xFFFD02C0) // (CAN_MB6) Base Address
#define AT91C_BASE_CAN_MB7   ((AT91PS_CAN_MB) 	0xFFFD02E0) // (CAN_MB7) Base Address
#define AT91C_BASE_CAN       ((AT91PS_CAN) 	0xFFFD0000) // (CAN) Base Address
#define AT91C_BASE_EMAC      ((AT91PS_EMAC) 	0xFFFDC000) // (EMAC) Base Address
#define AT91C_BASE_PDC_ADC   ((AT91PS_PDC) 	0xFFFD8100) // (PDC_ADC) Base Address
#define AT91C_BASE_ADC       ((AT91PS_ADC) 	0xFFFD8000) // (ADC) Base Address
#define AT91C_BASE_PDC_AES   ((AT91PS_PDC) 	0xFFFA4100) // (PDC_AES) Base Address
#define AT91C_BASE_AES       ((AT91PS_AES) 	0xFFFA4000) // (AES) Base Address
#define AT91C_BASE_PDC_TDES  ((AT91PS_PDC) 	0xFFFA8100) // (PDC_TDES) Base Address
#define AT91C_BASE_TDES      ((AT91PS_TDES) 	0xFFFA8000) // (TDES) Base Address

// *****************************************************************************
//               MEMORY MAPPING DEFINITIONS FOR AT91SAM7X128
// *****************************************************************************
#define AT91C_ISRAM	 ((char *) 	0x00200000) // Internal SRAM base address
#define AT91C_ISRAM_SIZE	 ((unsigned int) 0x00008000) // Internal SRAM size in byte (32 Kbyte)
#define AT91C_IFLASH	 ((char *) 	0x00100000) // Internal ROM base address
#define AT91C_IFLASH_SIZE	 ((unsigned int) 0x00020000) // Internal ROM size in byte (128 Kbyte)

#endif
