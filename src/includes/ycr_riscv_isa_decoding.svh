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
////  yifive RISC-V ISA definitions file                                  ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     RISC-V ISA definitions file                                      ////
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

`ifndef YCR_RISCV_ISA_DECODING_SVH
`define YCR_RISCV_ISA_DECODING_SVH

`include "ycr_arch_description.svh"
`include "ycr_arch_types.svh"

//-------------------------------------------------------------------------------
// Instruction types
//-------------------------------------------------------------------------------
//typedef enum logic [1:0] {
parameter    YCR_INSTR_RVC0     = 2'b00;
parameter    YCR_INSTR_RVC1     = 2'b01;
parameter    YCR_INSTR_RVC2     = 2'b10;
parameter    YCR_INSTR_RVI      = 2'b11;
//} type_ycr_instr_type_e;

//-------------------------------------------------------------------------------
// RV32I opcodes (bits 6:2)
//-------------------------------------------------------------------------------
//typedef enum logic [6:2] {
parameter    YCR_OPCODE_LOAD        = 5'b00000;
parameter    YCR_OPCODE_MISC_MEM    = 5'b00011;
parameter    YCR_OPCODE_OP_IMM      = 5'b00100;
parameter    YCR_OPCODE_AUIPC       = 5'b00101;
parameter    YCR_OPCODE_STORE       = 5'b01000;
parameter    YCR_OPCODE_OP          = 5'b01100;
parameter    YCR_OPCODE_LUI         = 5'b01101;
parameter    YCR_OPCODE_BRANCH      = 5'b11000;
parameter    YCR_OPCODE_JALR        = 5'b11001;
parameter    YCR_OPCODE_JAL         = 5'b11011;
parameter    YCR_OPCODE_SYSTEM      = 5'b11100;
//} type_ycr_rvi_opcode_e;


//-------------------------------------------------------------------------------
// IALU main operands
//-------------------------------------------------------------------------------
localparam YCR_IALU_OP_ALL_NUM_E = 2;
localparam YCR_IALU_OP_WIDTH_E   = $clog2(YCR_IALU_OP_ALL_NUM_E);
typedef enum logic [YCR_IALU_OP_WIDTH_E-1:0] {
    YCR_IALU_OP_REG_IMM,          // op1 = rs1; op2 = imm
    YCR_IALU_OP_REG_REG           // op1 = rs1; op2 = rs2
} type_ycr_ialu_op_sel_e;

//-------------------------------------------------------------------------------
// IALU main commands
//-------------------------------------------------------------------------------
`ifdef YCR_RVM_EXT
localparam YCR_IALU_CMD_ALL_NUM_E    = 23;
`else // ~YCR_RVM_EXT
localparam YCR_IALU_CMD_ALL_NUM_E    = 15;
`endif // ~YCR_RVM_EXT
localparam YCR_IALU_CMD_WIDTH_E      = $clog2(YCR_IALU_CMD_ALL_NUM_E);
typedef enum logic [YCR_IALU_CMD_WIDTH_E-1:0] {
    YCR_IALU_CMD_NONE  = '0,   // IALU disable
    YCR_IALU_CMD_AND,          // op1 & op2
    YCR_IALU_CMD_OR,           // op1 | op2
    YCR_IALU_CMD_XOR,          // op1 ^ op2
    YCR_IALU_CMD_ADD,          // op1 + op2
    YCR_IALU_CMD_SUB,          // op1 - op2
    YCR_IALU_CMD_SUB_LT,       // op1 < op2
    YCR_IALU_CMD_SUB_LTU,      // op1 u< op2
    YCR_IALU_CMD_SUB_EQ,       // op1 = op2
    YCR_IALU_CMD_SUB_NE,       // op1 != op2
    YCR_IALU_CMD_SUB_GE,       // op1 >= op2
    YCR_IALU_CMD_SUB_GEU,      // op1 u>= op2
    YCR_IALU_CMD_SLL,          // op1 << op2
    YCR_IALU_CMD_SRL,          // op1 >> op2
    YCR_IALU_CMD_SRA           // op1 >>> op2
`ifdef YCR_RVM_EXT
    ,
    YCR_IALU_CMD_MUL,          // low(unsig(op1) * unsig(op2))
    YCR_IALU_CMD_MULHU,        // high(unsig(op1) * unsig(op2))
    YCR_IALU_CMD_MULHSU,       // high(op1 * unsig(op2))
    YCR_IALU_CMD_MULH,         // high(op1 * op2)
    YCR_IALU_CMD_DIV,          // op1 / op2
    YCR_IALU_CMD_DIVU,         // op1 u/ op2
    YCR_IALU_CMD_REM,          // op1 % op2
    YCR_IALU_CMD_REMU          // op1 u% op2
`endif  // YCR_RVM_EXT
} type_ycr_ialu_cmd_sel_e;

//-------------------------------------------------------------------------------
// IALU SUM2 operands (result is JUMP/BRANCH target, LOAD/STORE address)
//-------------------------------------------------------------------------------
localparam YCR_SUM2_OP_ALL_NUM_E    = 2;
localparam YCR_SUM2_OP_WIDTH_E      = $clog2(YCR_SUM2_OP_ALL_NUM_E);
typedef enum logic [YCR_SUM2_OP_WIDTH_E-1:0] {
    YCR_SUM2_OP_PC_IMM,        // op1 = curr_pc; op2 = imm (AUIPC, target new_pc for JAL and branches)
    YCR_SUM2_OP_REG_IMM        // op1 = rs1; op2 = imm (target new_pc for JALR, LOAD/STORE address)
`ifdef YCR_XPROP_EN
    ,
    YCR_SUM2_OP_ERROR = 'x
`endif // YCR_XPROP_EN
} type_ycr_ialu_sum2_op_sel_e;

//-------------------------------------------------------------------------------
// LSU commands
//-------------------------------------------------------------------------------
localparam YCR_LSU_CMD_ALL_NUM_E   = 9;
localparam YCR_LSU_CMD_WIDTH_E     = $clog2(YCR_LSU_CMD_ALL_NUM_E);
typedef enum logic [YCR_LSU_CMD_WIDTH_E-1:0] {
    YCR_LSU_CMD_NONE = '0,
    YCR_LSU_CMD_LB,
    YCR_LSU_CMD_LH,
    YCR_LSU_CMD_LW,
    YCR_LSU_CMD_LBU,
    YCR_LSU_CMD_LHU,
    YCR_LSU_CMD_SB,
    YCR_LSU_CMD_SH,
    YCR_LSU_CMD_SW
} type_ycr_lsu_cmd_sel_e;

//-------------------------------------------------------------------------------
// CSR operands
//-------------------------------------------------------------------------------
localparam YCR_CSR_OP_ALL_NUM_E   = 2;
localparam YCR_CSR_OP_WIDTH_E     = $clog2(YCR_CSR_OP_ALL_NUM_E);
typedef enum logic [YCR_CSR_OP_WIDTH_E-1:0] {
    YCR_CSR_OP_IMM,
    YCR_CSR_OP_REG
} type_ycr_csr_op_sel_e;

//-------------------------------------------------------------------------------
// CSR commands
//-------------------------------------------------------------------------------
localparam YCR_CSR_CMD_ALL_NUM_E   = 4;
localparam YCR_CSR_CMD_WIDTH_E     = $clog2(YCR_CSR_CMD_ALL_NUM_E);
typedef enum logic [YCR_CSR_CMD_WIDTH_E-1:0] {
    YCR_CSR_CMD_NONE = '0,
    YCR_CSR_CMD_WRITE,
    YCR_CSR_CMD_SET,
    YCR_CSR_CMD_CLEAR
} type_ycr_csr_cmd_sel_e;

//-------------------------------------------------------------------------------
// MPRF rd writeback source
//-------------------------------------------------------------------------------
localparam YCR_RD_WB_ALL_NUM_E = 7;
localparam YCR_RD_WB_WIDTH_E   = $clog2(YCR_RD_WB_ALL_NUM_E);
typedef enum logic [YCR_RD_WB_WIDTH_E-1:0] {
    YCR_RD_WB_NONE = '0,
    YCR_RD_WB_IALU,            // IALU main result
    YCR_RD_WB_SUM2,            // IALU SUM2 result (AUIPC)
    YCR_RD_WB_IMM,             // LUI
    YCR_RD_WB_INC_PC,          // JAL(R)
    YCR_RD_WB_LSU,             // Load from DMEM
    YCR_RD_WB_CSR              // Read CSR
} type_ycr_rd_wb_sel_e;

//-------------------------------------------------------------------------------
// IDU to EXU full command structure
//-------------------------------------------------------------------------------
localparam YCR_GPR_FIELD_WIDTH = 5;

typedef struct packed {
    logic                               instr_rvc;      // used with a different meaning for IFU access fault exception
    type_ycr_ialu_op_sel_e             ialu_op;
    type_ycr_ialu_cmd_sel_e            ialu_cmd;
    type_ycr_ialu_sum2_op_sel_e        sum2_op;
    type_ycr_lsu_cmd_sel_e             lsu_cmd;
    type_ycr_csr_op_sel_e              csr_op;
    type_ycr_csr_cmd_sel_e             csr_cmd;
    type_ycr_rd_wb_sel_e               rd_wb_sel;
    logic                               jump_req;
    logic                               branch_req;
    logic                               mret_req;
    logic                               fencei_req;
    logic                               wfi_req;
    logic [YCR_GPR_FIELD_WIDTH-1:0]    rs1_addr;       // also used as zimm for CSRRxI instructions
    logic [YCR_GPR_FIELD_WIDTH-1:0]    rs2_addr;
    logic [YCR_GPR_FIELD_WIDTH-1:0]    rd_addr;
    logic [`YCR_XLEN-1:0]              imm;            // used as {funct3, CSR address} for CSR instructions
                                                        // used as instruction field for illegal instruction exception
    logic                               exc_req;
    type_ycr_exc_code_e                exc_code;
} type_ycr_exu_cmd_s;

`endif // YCR_RISCV_ISA_DECODING_SVH

