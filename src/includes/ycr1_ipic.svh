//////////////////////////////////////////////////////////////////////////////
// SPDX-FileCopyrightText: 2021, Dinesh Annayya                           ////
//                                                                        ////
// Licensed under the Apache License, Version 2.0 (the "License");        ////
// you may not use this file except in compliance with the License.       ////
// You may obtain a copy of the License at                                ////
//                                                                        ////
//      http://www.apache.org/licenses/LICENSE-2.0                        ////
//                                                                        ////
// Unless required by applicable law or agreed to in writing, software    ////
// distributed under the License is distributed on an "AS IS" BASIS,      ////
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.///
// See the License for the specific language governing permissions and    ////
// limitations under the License.                                         ////
// SPDX-License-Identifier: Apache-2.0                                    ////
// SPDX-FileContributor: Dinesh Annayya <dinesha@opencores.org>           ////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
////                                                                      ////
////  yifive IPIC header file                                             ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr1.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     IPIC header file                                                 ////
////                                                                      ////
////  To Do:                                                              ////
////    nothing                                                           ////
////                                                                      ////
////  Author(s):                                                          ////
////      - Dinesh Annayya, dinesha@opencores.org                         ////
////                                                                      ////
////  Revision :                                                          ////
////     v0:    Jan 2021- Initial version picked from syntacore/scr1      ////
////     v1:    June 7, 2021, Dinesh A                                    ////
////             opentool(iverilog/yosys) related cleanup                 ////
////                                                                      ////
//////////////////////////////////////////////////////////////////////////////


`ifndef YCR1_IPIC_SVH
`define YCR1_IPIC_SVH

`include "ycr1_arch_description.svh"

`ifdef YCR1_IPIC_EN
//-------------------------------------------------------------------------------
// Parameters declaration
//-------------------------------------------------------------------------------
parameter                                   YCR1_IRQ_VECT_NUM       = 16;   // must be power of 2 in the current implementation
parameter                                   YCR1_IRQ_VECT_WIDTH     = $clog2(YCR1_IRQ_VECT_NUM+1);
parameter                                   YCR1_IRQ_LINES_NUM      = YCR1_IRQ_VECT_NUM;
parameter                                   YCR1_IRQ_LINES_WIDTH    = $clog2(YCR1_IRQ_LINES_NUM);
parameter   logic [YCR1_IRQ_VECT_WIDTH-1:0] YCR1_IRQ_VOID_VECT_NUM  = YCR1_IRQ_VECT_WIDTH'(YCR1_IRQ_VECT_NUM);
parameter                                   YCR1_IRQ_IDX_WIDTH      = $clog2(YCR1_IRQ_VECT_NUM);

// Address decoding parameters
parameter   logic [2:0]                     YCR1_IPIC_CISV          = 3'h0;    // RO
parameter   logic [2:0]                     YCR1_IPIC_CICSR         = 3'h1;    // {IP, IE}
parameter   logic [2:0]                     YCR1_IPIC_IPR           = 3'h2;    // RW1C
parameter   logic [2:0]                     YCR1_IPIC_ISVR          = 3'h3;    // RO
parameter   logic [2:0]                     YCR1_IPIC_EOI           = 3'h4;    // RZW
parameter   logic [2:0]                     YCR1_IPIC_SOI           = 3'h5;    // RZW
parameter   logic [2:0]                     YCR1_IPIC_IDX           = 3'h6;    // RW
parameter   logic [2:0]                     YCR1_IPIC_ICSR          = 3'h7;    // RW

parameter                                   YCR1_IPIC_ICSR_IP       = 0;
parameter                                   YCR1_IPIC_ICSR_IE       = 1;
parameter                                   YCR1_IPIC_ICSR_IM       = 2;
parameter                                   YCR1_IPIC_ICSR_INV      = 3;
parameter                                   YCR1_IPIC_ICSR_IS       = 4;
parameter                                   YCR1_IPIC_ICSR_PRV_LSB  = 8;
parameter                                   YCR1_IPIC_ICSR_PRV_MSB  = 9;
parameter                                   YCR1_IPIC_ICSR_LN_LSB   = 12;
parameter                                   YCR1_IPIC_ICSR_LN_MSB   = YCR1_IPIC_ICSR_LN_LSB
                                                                    + YCR1_IRQ_LINES_WIDTH;

parameter   logic [1:0]                     YCR1_IPIC_PRV_M         = 2'b11;

//-------------------------------------------------------------------------------
// Types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    YCR1_CSR2IPIC_RD,
    YCR1_CSR2IPIC_WR
`ifdef YCR1_XPROP_EN
    ,
    YCR1_CSR2IPIC_ERROR = 'x
`endif // YCR1_XPROP_EN
} type_ycr1_csr2ipic_wr_e;

`endif // YCR1_IPIC_EN
`endif // YCR1_IPIC_SVH
