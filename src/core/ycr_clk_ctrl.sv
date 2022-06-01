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
////  yifive clock control                                                ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     clock control                                                    ////
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

`include "ycr_arch_description.svh"

`ifdef YCR_CLKCTRL_EN
module ycr_clk_ctrl (
    input   logic   clk,                            // Clock control module clock
    input   logic   rst_n,                          // Clock control module reset
    input   logic   test_mode,                      // DFT Test Mode
    input   logic   test_rst_n,                     // DFT Test reset

    input   logic   pipe2clkctl_sleep_req_i,        // CLK disable request from pipe
    input   logic   pipe2clkctl_wake_req_i,         // CLK enable request from pipe

    output  logic   clkctl2pipe_clk_alw_on_o,       // Not gated pipe CLK
    output  logic   clkctl2pipe_clk_o,              // Gated pipe
    output  logic   clkctl2pipe_clk_en_o,           // CLK enabled flag
    output  logic   clkctl2pipe_clk_dbgc_o          // CLK for pipe debug subsystem
);

logic ctrl_rst_n;

assign clkctl2pipe_clk_alw_on_o = clk;
assign clkctl2pipe_clk_dbgc_o   = clk;
assign ctrl_rst_n   = (test_mode) ? test_rst_n : rst_n;

always_ff @(posedge clk, negedge ctrl_rst_n) begin
    if (~ctrl_rst_n) begin
        clkctl2pipe_clk_en_o <= 1'b1;
    end else begin
        if (clkctl2pipe_clk_en_o) begin
            if (pipe2clkctl_sleep_req_i & ~pipe2clkctl_wake_req_i) begin
                clkctl2pipe_clk_en_o <= 1'b0;
            end
        end else begin // ~clkctl2pipe_clk_en_o
            if (pipe2clkctl_wake_req_i) begin
                clkctl2pipe_clk_en_o <= 1'b1;
            end
        end // pipeline
    end
end

ycr_cg i_ycr_cg_pipe (
    .clk        (clk                 ),
    .clk_en     (clkctl2pipe_clk_en_o),
    .test_mode  (test_mode           ),
    .clk_out    (clkctl2pipe_clk_o   )
);

endmodule : ycr_clk_ctrl

`endif // YCR_CLKCTRL_EN
