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
////  yifive HART Debug Unit definitions file                             ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     HART Debug Unit definitions file                                 ////
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

`ifndef YCR_INCLUDE_HDU_DEFS
`define YCR_INCLUDE_HDU_DEFS

`include "ycr_arch_description.svh"
`include "ycr_csr.svh"

`ifdef YCR_MMU_EN
 `define YCR_HDU_FEATURE_MPRVEN
`endif // YCR_MMU_EN

//==============================================================================
// Parameters
//==============================================================================
//localparam int unsigned YCR_HDU_DEBUGCSR_BASE_ADDR      = 12'h7B0;
localparam int unsigned YCR_HDU_DEBUGCSR_ADDR_SPAN      = 4; // YOSYS FIX
localparam int unsigned YCR_HDU_DEBUGCSR_ADDR_WIDTH     = $clog2(YCR_HDU_DEBUGCSR_ADDR_SPAN);
localparam bit [3:0]    YCR_HDU_DEBUGCSR_DCSR_XDEBUGVER = 4'h4;
localparam int unsigned YCR_HDU_PBUF_ADDR_SPAN          = 8;
localparam int unsigned YCR_HDU_PBUF_ADDR_WIDTH         = $clog2(YCR_HDU_PBUF_ADDR_SPAN);
localparam int unsigned YCR_HDU_DATA_REG_WIDTH          = 32;
localparam int unsigned YCR_HDU_CORE_INSTR_WIDTH        = 32;


//==============================================================================
// Types
//==============================================================================

// HART Debug States:
typedef enum logic [1:0] {
    YCR_HDU_DBGSTATE_RESET         = 2'b00,
    YCR_HDU_DBGSTATE_RUN           = 2'b01,
    YCR_HDU_DBGSTATE_DHALTED       = 2'b10,
    YCR_HDU_DBGSTATE_DRUN          = 2'b11
`ifdef YCR_XPROP_EN
    ,
    YCR_HDU_DBGSTATE_XXX           = 'X
`endif // YCR_XPROP_EN
} type_ycr_hdu_dbgstates_e;

typedef enum logic [1:0] {
    YCR_HDU_PBUFSTATE_IDLE          = 2'b00,
    YCR_HDU_PBUFSTATE_FETCH         = 2'b01,
    YCR_HDU_PBUFSTATE_EXCINJECT     = 2'b10,
    YCR_HDU_PBUFSTATE_WAIT4END      = 2'b11
`ifdef YCR_XPROP_EN
    ,
    YCR_HDU_PBUFSTATE_XXX           = 'X
`endif // YCR_XPROP_EN
} type_ycr_hdu_pbufstates_e;

typedef enum logic {
    YCR_HDU_HARTCMD_RESUME         = 1'b0,
    YCR_HDU_HARTCMD_HALT           = 1'b1
`ifdef YCR_XPROP_EN
    ,
    YCR_HDU_HARTCMD_XXX            = 1'bX
`endif // YCR_XPROP_EN
} type_ycr_hdu_hart_command_e;

typedef enum logic {
    YCR_HDU_FETCH_SRC_NORMAL       = 1'b0,
    YCR_HDU_FETCH_SRC_PBUF         = 1'b1
`ifdef YCR_XPROP_EN
    ,
    YCR_HDU_FETCH_SRC_XXX          = 1'bX
`endif // YCR_XPROP_EN
} type_ycr_hdu_fetch_src_e;

typedef struct packed {
    //logic                               reset_n;
    logic                               except;
    logic                               ebreak;
    type_ycr_hdu_dbgstates_e           dbg_state;
} type_ycr_hdu_hartstatus_s;

// Debug Mode Redirection control:
typedef struct packed {
    logic                               sstep;          // Single Step
    logic                               ebreak;         // Redirection after EBREAK execution
} type_ycr_hdu_redirect_s;

typedef struct packed {
    logic                               irq_dsbl;
    type_ycr_hdu_fetch_src_e           fetch_src;
    logic                               pc_advmt_dsbl;
    logic                               hwbrkpt_dsbl;
    type_ycr_hdu_redirect_s            redirect;
} type_ycr_hdu_runctrl_s;

// HART Halt Status:
typedef enum logic [2:0] {
    YCR_HDU_HALTCAUSE_NONE         = 3'b000,
    YCR_HDU_HALTCAUSE_EBREAK       = 3'b001,
    YCR_HDU_HALTCAUSE_TMREQ        = 3'b010,
    YCR_HDU_HALTCAUSE_DMREQ        = 3'b011,
    YCR_HDU_HALTCAUSE_SSTEP        = 3'b100,
    YCR_HDU_HALTCAUSE_RSTEXIT      = 3'b101
`ifdef YCR_XPROP_EN
    ,
    YCR_HDU_HALTCAUSE_XXX          = 'X
`endif // YCR_XPROP_EN
} type_ycr_hdu_haltcause_e;

typedef struct packed {
    logic                               except;
    type_ycr_hdu_haltcause_e           cause;
} type_ycr_hdu_haltstatus_s;


// Debug CSR map
localparam YCR_HDU_DBGCSR_OFFS_DCSR       = YCR_HDU_DEBUGCSR_ADDR_WIDTH'( 'd0 );
localparam YCR_HDU_DBGCSR_OFFS_DPC        = YCR_HDU_DEBUGCSR_ADDR_WIDTH'( 'd1 );
localparam YCR_HDU_DBGCSR_OFFS_DSCRATCH0  = YCR_HDU_DEBUGCSR_ADDR_WIDTH'( 'd2 );
localparam YCR_HDU_DBGCSR_OFFS_DSCRATCH1  = YCR_HDU_DEBUGCSR_ADDR_WIDTH'( 'd3 );

localparam bit [YCR_CSR_ADDR_WIDTH-1:0] YCR_HDU_DBGCSR_ADDR_DCSR      = YCR_CSR_ADDR_HDU_MBASE + YCR_HDU_DBGCSR_OFFS_DCSR;
localparam bit [YCR_CSR_ADDR_WIDTH-1:0] YCR_HDU_DBGCSR_ADDR_DPC       = YCR_CSR_ADDR_HDU_MBASE + YCR_HDU_DBGCSR_OFFS_DPC;
localparam bit [YCR_CSR_ADDR_WIDTH-1:0] YCR_HDU_DBGCSR_ADDR_DSCRATCH0 = YCR_CSR_ADDR_HDU_MBASE + YCR_HDU_DBGCSR_OFFS_DSCRATCH0;
localparam bit [YCR_CSR_ADDR_WIDTH-1:0] YCR_HDU_DBGCSR_ADDR_DSCRATCH1 = YCR_CSR_ADDR_HDU_MBASE + YCR_HDU_DBGCSR_OFFS_DSCRATCH1;

// Debug CSRs :: DCSR
typedef enum int {
    YCR_HDU_DCSR_PRV_BIT_R         = 0,
    YCR_HDU_DCSR_PRV_BIT_L         = 1,
    YCR_HDU_DCSR_STEP_BIT          = 2,
    YCR_HDU_DCSR_RSRV0_BIT_R       = 3,
    YCR_HDU_DCSR_RSRV0_BIT_L       = 5,
    YCR_HDU_DCSR_CAUSE_BIT_R       = 6,
    YCR_HDU_DCSR_CAUSE_BIT_L       = 8,
    YCR_HDU_DCSR_RSRV1_BIT_R       = 9,
    YCR_HDU_DCSR_RSRV1_BIT_L       = 10,
    YCR_HDU_DCSR_STEPIE_BIT        = 11,
    YCR_HDU_DCSR_RSRV2_BIT_R       = 12,
    YCR_HDU_DCSR_RSRV2_BIT_L       = 14,
    YCR_HDU_DCSR_EBREAKM_BIT       = 15,
    YCR_HDU_DCSR_RSRV3_BIT_R       = 16,
    YCR_HDU_DCSR_RSRV3_BIT_L       = 27,
    YCR_HDU_DCSR_XDEBUGVER_BIT_R   = 28,
    YCR_HDU_DCSR_XDEBUGVER_BIT_L   = 31
} type_ycr_hdu_dcsr_bits_e;

//localparam int unsigned YCR_HDU_DEBUGCSR_DCSR_PRV_WIDTH = YCR_HDU_DCSR_PRV_BIT_L-YCR_HDU_DCSR_PRV_BIT_R+1;

typedef struct packed {
    logic [YCR_HDU_DCSR_XDEBUGVER_BIT_L-YCR_HDU_DCSR_XDEBUGVER_BIT_R:0]   xdebugver;
    logic [YCR_HDU_DCSR_RSRV3_BIT_L-YCR_HDU_DCSR_RSRV3_BIT_R:0]           rsrv3;
    logic                                                                   ebreakm;
    logic [YCR_HDU_DCSR_RSRV2_BIT_L-YCR_HDU_DCSR_RSRV2_BIT_R:0]           rsrv2;
    logic                                                                   stepie;
    logic [YCR_HDU_DCSR_RSRV1_BIT_L-YCR_HDU_DCSR_RSRV1_BIT_R:0]           rsrv1;
    logic [YCR_HDU_DCSR_CAUSE_BIT_L-YCR_HDU_DCSR_CAUSE_BIT_R:0]           cause;
    logic [YCR_HDU_DCSR_RSRV0_BIT_L-YCR_HDU_DCSR_RSRV0_BIT_R:0]           rsrv0;
    logic                                                                   step;
    logic [YCR_HDU_DCSR_PRV_BIT_L-YCR_HDU_DCSR_PRV_BIT_R:0]               prv;
} type_ycr_hdu_dcsr_s;


`endif // YCR_INCLUDE_HDU_DEFS
