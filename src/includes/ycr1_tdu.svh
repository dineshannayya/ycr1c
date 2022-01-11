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
////  yifive Trigger Debug Module header                                  ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr1.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     Trigger Debug Module header                                      ////
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

`ifndef YCR1_INCLUDE_TDU_DEFS
`define YCR1_INCLUDE_TDU_DEFS

//`include "ycr1_arch_description.svh"

`ifdef YCR1_TDU_EN
//`include "ycr1_csr.svh"

`include "ycr1_arch_description.svh"
//`include "ycr1_arch_types.svh"
`include "ycr1_csr.svh"

parameter int unsigned  YCR1_TDU_MTRIG_NUM             = YCR1_TDU_TRIG_NUM;
`ifdef YCR1_TDU_ICOUNT_EN
parameter int unsigned  YCR1_TDU_ALLTRIG_NUM           = YCR1_TDU_MTRIG_NUM + 1'b1;
`else
parameter int unsigned  YCR1_TDU_ALLTRIG_NUM           = YCR1_TDU_MTRIG_NUM;
`endif

parameter int unsigned  YCR1_TDU_ADDR_W                = `YCR1_XLEN;
parameter int unsigned  YCR1_TDU_DATA_W                = `YCR1_XLEN;

// Register map
parameter                                     YCR1_CSR_ADDR_TDU_OFFS_W        = 3;
parameter bit [YCR1_CSR_ADDR_TDU_OFFS_W-1:0]  YCR1_CSR_ADDR_TDU_OFFS_TSELECT  = 'h0;
parameter bit [YCR1_CSR_ADDR_TDU_OFFS_W-1:0]  YCR1_CSR_ADDR_TDU_OFFS_TDATA1   = 'h1;
parameter bit [YCR1_CSR_ADDR_TDU_OFFS_W-1:0]  YCR1_CSR_ADDR_TDU_OFFS_TDATA2   = 'h2;
parameter bit [YCR1_CSR_ADDR_TDU_OFFS_W-1:0]  YCR1_CSR_ADDR_TDU_OFFS_TINFO    = 'h4;


parameter bit [YCR1_CSR_ADDR_WIDTH-1:0] YCR1_CSR_ADDR_TDU_TSELECT       = YCR1_CSR_ADDR_TDU_MBASE + YCR1_CSR_ADDR_TDU_OFFS_TSELECT;
parameter bit [YCR1_CSR_ADDR_WIDTH-1:0] YCR1_CSR_ADDR_TDU_TDATA1        = YCR1_CSR_ADDR_TDU_MBASE + YCR1_CSR_ADDR_TDU_OFFS_TDATA1;
parameter bit [YCR1_CSR_ADDR_WIDTH-1:0] YCR1_CSR_ADDR_TDU_TDATA2        = YCR1_CSR_ADDR_TDU_MBASE + YCR1_CSR_ADDR_TDU_OFFS_TDATA2;
parameter bit [YCR1_CSR_ADDR_WIDTH-1:0] YCR1_CSR_ADDR_TDU_TINFO         = YCR1_CSR_ADDR_TDU_MBASE + YCR1_CSR_ADDR_TDU_OFFS_TINFO;

// TDATA1
parameter int unsigned  YCR1_TDU_TDATA1_TYPE_HI        = `YCR1_XLEN-1;
parameter int unsigned  YCR1_TDU_TDATA1_TYPE_LO        = `YCR1_XLEN-4;
parameter int unsigned  YCR1_TDU_TDATA1_DMODE          = `YCR1_XLEN-5;

// TDATA1: constant bits values
parameter bit           YCR1_TDU_TDATA1_DMODE_VAL      = 1'b0;

// MCONTROL: bits number
parameter int unsigned  YCR1_TDU_MCONTROL_MASKMAX_HI   = `YCR1_XLEN-6;
parameter int unsigned  YCR1_TDU_MCONTROL_MASKMAX_LO   = `YCR1_XLEN-11;
parameter int unsigned  YCR1_TDU_MCONTROL_RESERVEDB_HI = `YCR1_XLEN-12;
parameter int unsigned  YCR1_TDU_MCONTROL_RESERVEDB_LO = 21;
parameter int unsigned  YCR1_TDU_MCONTROL_HIT          = 20;
parameter int unsigned  YCR1_TDU_MCONTROL_SELECT       = 19;
parameter int unsigned  YCR1_TDU_MCONTROL_TIMING       = 18;
parameter int unsigned  YCR1_TDU_MCONTROL_ACTION_HI    = 17;
parameter int unsigned  YCR1_TDU_MCONTROL_ACTION_LO    = 12;
parameter int unsigned  YCR1_TDU_MCONTROL_CHAIN        = 11;
parameter int unsigned  YCR1_TDU_MCONTROL_MATCH_HI     = 10;
parameter int unsigned  YCR1_TDU_MCONTROL_MATCH_LO     = 7;
parameter int unsigned  YCR1_TDU_MCONTROL_M            = 6;
parameter int unsigned  YCR1_TDU_MCONTROL_RESERVEDA    = 5;
parameter int unsigned  YCR1_TDU_MCONTROL_S            = 4;
parameter int unsigned  YCR1_TDU_MCONTROL_U            = 3;
parameter int unsigned  YCR1_TDU_MCONTROL_EXECUTE      = 2;
parameter int unsigned  YCR1_TDU_MCONTROL_STORE        = 1;
parameter int unsigned  YCR1_TDU_MCONTROL_LOAD         = 0;

// MCONTROL: constant bits values
parameter bit [YCR1_TDU_TDATA1_TYPE_HI-YCR1_TDU_TDATA1_TYPE_LO:0]
                        YCR1_TDU_MCONTROL_TYPE_VAL           = 2'd2;

parameter bit           YCR1_TDU_MCONTROL_SELECT_VAL         = 1'b0;
parameter bit           YCR1_TDU_MCONTROL_TIMING_VAL         = 1'b0;

parameter bit [YCR1_TDU_MCONTROL_MASKMAX_HI-YCR1_TDU_MCONTROL_MASKMAX_LO:0]
                        YCR1_TDU_MCONTROL_MASKMAX_VAL        = 1'b0;

parameter bit           YCR1_TDU_MCONTROL_RESERVEDA_VAL      = 1'b0;

// ICOUNT: bits number
parameter int unsigned  YCR1_TDU_ICOUNT_DMODE          = `YCR1_XLEN-5;
parameter int unsigned  YCR1_TDU_ICOUNT_RESERVEDB_HI   = `YCR1_XLEN-6;
parameter int unsigned  YCR1_TDU_ICOUNT_RESERVEDB_LO   = 25;
parameter int unsigned  YCR1_TDU_ICOUNT_HIT            = 24;
parameter int unsigned  YCR1_TDU_ICOUNT_COUNT_HI       = 23;
parameter int unsigned  YCR1_TDU_ICOUNT_COUNT_LO       = 10;
parameter int unsigned  YCR1_TDU_ICOUNT_M              = 9;
parameter int unsigned  YCR1_TDU_ICOUNT_RESERVEDA      = 8;
parameter int unsigned  YCR1_TDU_ICOUNT_S              = 7;
parameter int unsigned  YCR1_TDU_ICOUNT_U              = 6;
parameter int unsigned  YCR1_TDU_ICOUNT_ACTION_HI      = 5;
parameter int unsigned  YCR1_TDU_ICOUNT_ACTION_LO      = 0;

// ICOUNT: constant bits values
parameter bit [YCR1_TDU_TDATA1_TYPE_HI-YCR1_TDU_TDATA1_TYPE_LO:0]
                        YCR1_TDU_ICOUNT_TYPE_VAL             = 2'd3;

parameter bit [YCR1_TDU_ICOUNT_RESERVEDB_HI-YCR1_TDU_ICOUNT_RESERVEDB_LO:0]
                        YCR1_TDU_ICOUNT_RESERVEDB_VAL        = 1'b0;

parameter bit           YCR1_TDU_ICOUNT_RESERVEDA_VAL        = 1'b0;

// CPU pipeline monitors
typedef struct packed {
    logic                                           vd;
    logic                                           req;
    logic [`YCR1_XLEN-1:0]                          addr;
} type_ycr1_brkm_instr_mon_s;

typedef struct packed {
    logic                                           vd;
    logic                                           load;
    logic                                           store;
    logic [`YCR1_XLEN-1:0]                          addr;
} type_ycr1_brkm_lsu_mon_s;

`endif // YCR1_TDU_EN

`endif // YCR1_INCLUDE_TDU_DEFS
