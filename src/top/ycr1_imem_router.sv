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
////  yifive Instruction memory router                                    ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr1.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     Instruction memory router                                        ////
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

`include "ycr1_memif.svh"
`include "ycr1_arch_description.svh"

module ycr1_imem_router
#(
    parameter YCR1_ADDR_MASK    = `YCR1_IMEM_AWIDTH'hFFFF0000,
    parameter YCR1_ADDR_PATTERN = `YCR1_IMEM_AWIDTH'h00010000
)
(
    // Control signals
    input   logic                           rst_n,
    input   logic                           clk,

    // Core interface
    output  logic                           imem_req_ack,
    input   logic                           imem_req,
    input   logic                           imem_cmd,
    input   logic [`YCR1_IMEM_AWIDTH-1:0]   imem_addr,
    output  logic [`YCR1_IMEM_DWIDTH-1:0]   imem_rdata,
    output  logic [1:0]                     imem_resp,

    // PORT0 interface
    input   logic                           port0_req_ack,
    output  logic                           port0_req,
    output  logic                           port0_cmd,
    output  logic [`YCR1_IMEM_AWIDTH-1:0]   port0_addr,
    input   logic [`YCR1_IMEM_DWIDTH-1:0]   port0_rdata,
    input   logic [1:0]                     port0_resp,

    // PORT1 interface
    input   logic                           port1_req_ack,
    output  logic                           port1_req,
    output  logic                           port1_cmd,
    output  logic [`YCR1_IMEM_AWIDTH-1:0]   port1_addr,
    input   logic [`YCR1_IMEM_DWIDTH-1:0]   port1_rdata,
    input   logic [1:0]                     port1_resp
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    YCR1_FSM_ADDR,
    YCR1_FSM_DATA
} type_ycr1_fsm_e;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
type_ycr1_fsm_e                 fsm;
logic                           port_sel;
logic                           port_sel_r;
logic [`YCR1_IMEM_DWIDTH-1:0]   sel_rdata;
logic [1:0]                     sel_resp;
logic                           sel_req_ack;

//-------------------------------------------------------------------------------
// FSM
//-------------------------------------------------------------------------------
assign port_sel = ((imem_addr & YCR1_ADDR_MASK) == YCR1_ADDR_PATTERN);

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm        <= YCR1_FSM_ADDR;
        port_sel_r <= 1'b0;
    end else begin
        case (fsm)
            YCR1_FSM_ADDR : begin
                if (imem_req & sel_req_ack) begin
                    fsm <= YCR1_FSM_DATA;
                    port_sel_r <= port_sel;
                end
            end
            YCR1_FSM_DATA : begin
                case (sel_resp)
                    YCR1_MEM_RESP_RDY_OK : begin
                        if (imem_req & sel_req_ack) begin
                            fsm <= YCR1_FSM_DATA;
                            port_sel_r <= port_sel;
                        end else begin
                            fsm <= YCR1_FSM_ADDR;
                        end
                    end
                    YCR1_MEM_RESP_RDY_ER : begin
                        fsm <= YCR1_FSM_ADDR;
                    end
                    default : begin
                    end
                endcase
            end
            default : begin
            end
        endcase
    end
end

always_comb begin
    if ((fsm == YCR1_FSM_ADDR) | ((fsm == YCR1_FSM_DATA) & (sel_resp == YCR1_MEM_RESP_RDY_OK))) begin
        sel_req_ack = (port_sel) ? port1_req_ack : port0_req_ack;
    end else begin
        sel_req_ack = 1'b0;
    end
end

assign sel_rdata = (port_sel_r) ? port1_rdata : port0_rdata;
assign sel_resp  = (port_sel_r) ? port1_resp  : port0_resp;

//-------------------------------------------------------------------------------
// Interface to core
//-------------------------------------------------------------------------------
assign imem_req_ack = sel_req_ack;
assign imem_rdata   = sel_rdata;
assign imem_resp    = sel_resp;

//-------------------------------------------------------------------------------
// Interface to PORT0
//-------------------------------------------------------------------------------
always_comb begin
    port0_req = 1'b0;
    case (fsm)
        YCR1_FSM_ADDR : begin
            port0_req = imem_req & ~port_sel;
        end
        YCR1_FSM_DATA : begin
            if (sel_resp == YCR1_MEM_RESP_RDY_OK) begin
                port0_req = imem_req & ~port_sel;
            end
        end
        default : begin
        end
    endcase
end

`ifdef YCR1_XPROP_EN
assign port0_cmd   = (~port_sel) ? imem_cmd  : YCR1_MEM_CMD_ERROR;
assign port0_addr  = (~port_sel) ? imem_addr : 'x;
`else // YCR1_XPROP_EN
assign port0_cmd   = imem_cmd ;
assign port0_addr  = imem_addr;
`endif // YCR1_XPROP_EN

//-------------------------------------------------------------------------------
// Interface to PORT1
//-------------------------------------------------------------------------------
always_comb begin
    port1_req = 1'b0;
    case (fsm)
        YCR1_FSM_ADDR : begin
            port1_req = imem_req & port_sel;
        end
        YCR1_FSM_DATA : begin
            if (sel_resp == YCR1_MEM_RESP_RDY_OK) begin
                port1_req = imem_req & port_sel;
            end
        end
        default : begin
        end
    endcase
end

`ifdef YCR1_XPROP_EN
assign port1_cmd   = (port_sel) ? imem_cmd  : YCR1_MEM_CMD_ERROR;
assign port1_addr  = (port_sel) ? imem_addr : 'x;
`else // YCR1_XPROP_EN
assign port1_cmd   = imem_cmd ;
assign port1_addr  = imem_addr;
`endif // YCR1_XPROP_EN

`ifdef YCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

YCR1_SVA_IMEM_RT_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    imem_req |-> !$isunknown({port_sel, imem_cmd})
    ) else $error("IMEM router Error: unknown values");

`endif // YCR1_TRGT_SIMULATION

endmodule : ycr1_imem_router
