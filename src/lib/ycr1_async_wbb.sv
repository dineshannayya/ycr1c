//////////////////////////////////////////////////////////////////////////////
// SPDX-FileCopyrightText: 2021 , Dinesh Annayya                          
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0
// SPDX-FileContributor: Created by Dinesh Annayya <dinesha@opencores.org>
//
//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Async Wishbone Interface iBurst Enable and lack             ////
////                                                              ////
////  This file is part of the YIFive cores project               ////
////  http://www.opencores.org/cores/yifive/                      ////
////                                                              ////
////  Description                                                 ////
////      This block does async Wishbone from one clock to other  ////
////      clock domain
////                                                              ////
////  To Do:                                                      ////
////    nothing                                                   ////
////                                                              ////
////  Author(s):                                                  ////
////      - Dinesh Annayya, dinesha@opencores.org                 ////
////                                                              ////
////  Revision :                                                  ////
////    0.1 - 25th Feb 2021, Dinesh A                             ////
////          initial version                                     ////
////    0.2 - 28th Feb 2021, Dinesh A                             ////
////          reduced the response FIFO path depth to 2 as        ////
////          return path used by only read logic and read is     ////
////          blocking request and expect only one location will  ////
////          be used                                             ////
////    0.3 - 20 Jan 2022, Dinesh A                               ////
////          added wishbone burst mode. Additional signal added  ////
////           A. *bl  - 10 Bit word Burst count, 1 - 1 DW(32 bit)////
////           B. *lack - Last Burst ack                          //// 
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

module ycr1_async_wbb 
     #(parameter AW  = 32,
       parameter BW  = 4,
       parameter BL  = 10,
       parameter DW  = 32)
       (

    // Master Port
       input   logic               wbm_rst_n   ,  // Regular Reset signal
       input   logic               wbm_clk_i   ,  // System clock
       input   logic               wbm_cyc_i   ,  // strobe/request
       input   logic               wbm_stb_i   ,  // strobe/request
       input   logic [AW-1:0]      wbm_adr_i   ,  // address
       input   logic               wbm_we_i    ,  // write
       input   logic [DW-1:0]      wbm_dat_i   ,  // data output
       input   logic [BW-1:0]      wbm_sel_i   ,  // byte enable
       input   logic [BL-1:0]      wbm_bl_i    ,  // Burst Count
       output  logic [DW-1:0]      wbm_dat_o   ,  // data input
       output  logic               wbm_ack_o   ,  // acknowlegement
       output  logic               wbm_lack_o  ,  // Last Burst access
       output  logic               wbm_err_o   ,  // error

    // Slave Port
       input   logic               wbs_rst_n   ,  // Regular Reset signal
       input   logic               wbs_clk_i   ,  // System clock
       output  logic               wbs_cyc_o   ,  // strobe/request
       output  logic               wbs_stb_o   ,  // strobe/request
       output  logic [AW-1:0]      wbs_adr_o   ,  // address
       output  logic               wbs_we_o    ,  // write
       output  logic [DW-1:0]      wbs_dat_o   ,  // data output
       output  logic [BW-1:0]      wbs_sel_o   ,  // byte enable
       output  logic [BL-1:0]      wbs_bl_o    ,  // Burst Count
       output  logic               wbs_bry_o   ,  // Busrt WData Avialble Or Ready To accept Rdata  
       input   logic [DW-1:0]      wbs_dat_i   ,  // data input
       input   logic               wbs_ack_i   ,  // acknowlegement
       input   logic               wbs_lack_i  ,  // Last Ack
       input   logic               wbs_err_i      // error

    );



parameter CFW = AW+DW+BW+BL+1 ; // COMMAND FIFO WIDTH
parameter RFW = DW+1+1 ;        // RESPONSE FIFO WIDTH

//-------------------------------------------------
//  Master Interface
// -------------------------------------------------
logic           PendingRd     ; // Pending Read Transaction
logic           m_cmd_wr_en       ;
logic [CFW-1:0] m_cmd_wr_data     ;
logic           m_cmd_wr_full     ;
logic           m_cmd_wr_afull    ;

logic           m_resp_rd_empty    ;
logic           m_resp_rd_aempty   ;
logic           m_resp_rd_en       ;
logic [RFW-1:0] m_resp_rd_data     ;

// Master Write Interface


assign m_cmd_wr_en = (!PendingRd) && wbm_stb_i && !m_cmd_wr_full && !m_cmd_wr_afull;

assign m_cmd_wr_data = {wbm_adr_i,wbm_we_i,wbm_dat_i,wbm_sel_i,wbm_bl_i};

always@(negedge wbm_rst_n or posedge wbm_clk_i)
begin
   if(wbm_rst_n == 0) begin
      PendingRd <= 1'b0;
   end else begin
      if((!PendingRd) && wbm_stb_i && (!wbm_we_i) && m_cmd_wr_en) begin
      PendingRd <= 1'b1;
      end else if(PendingRd && wbm_stb_i && (!wbm_we_i) && wbm_lack_o) begin
         PendingRd <= 1'b0;
      end
   end
end


// Response Path
assign wbm_ack_o = (wbm_stb_i && (!wbm_we_i)) ? !m_resp_rd_empty : 1'b0; // Read Logic

assign m_resp_rd_en   = !m_resp_rd_empty;
assign wbm_dat_o      = m_resp_rd_data[DW-1:0];
assign wbm_lack_o     = (!m_resp_rd_empty) ? m_resp_rd_data[RFW-2] : 1'b0 ;
assign wbm_err_o      = (!m_resp_rd_empty) ? m_resp_rd_data[RFW-1] : 1'b0;


//------------------------------
// Slave Interface
//-------------------------------

logic [CFW-1:0] s_cmd_rd_data      ;
logic        s_cmd_rd_empty     ;
logic        s_cmd_rd_aempty    ;
logic        s_cmd_rd_en        ;
logic        s_resp_wr_en        ;
logic [RFW-1:0] s_resp_wr_data      ;
logic        s_resp_wr_full      ;
logic        s_resp_wr_afull     ;
logic        wbs_ack_f          ;
logic        wbs_stb_l          ;
logic        wbs_burst          ;

wire wbs_stb_pedge = (wbs_stb_l == 1'b0) && wbs_stb_o;


always@(negedge wbs_rst_n or posedge wbs_clk_i)
begin
   if(wbs_rst_n == 0) begin
      wbs_ack_f <= 1'b0;
      wbs_stb_l <= 1'b0;
      wbs_burst <= 'h0;
   end else begin
      wbs_ack_f <= wbs_lack_i;
      wbs_stb_l <= wbs_stb_o;
      if(wbs_stb_pedge && wbs_bl_o > 'h1)
         wbs_burst <= 1'b1;
      else if(wbs_lack_i)
         wbs_burst <= 1'b0;
   end
end


// Read Interface
assign {wbs_adr_o,wbs_we_o,wbs_dat_o,wbs_sel_o,wbs_bl_o} = (s_cmd_rd_empty) ? '0:  s_cmd_rd_data;
// All the downstream logic expect Stobe is getting de-asserted 
// atleast for 1 cycle after ack is generated
// In Burst Mode, Keep the stb high untill lack received
assign wbs_stb_o = (wbs_ack_f) ? 1'b0 : (wbs_burst) ? 1'b1 : ((s_cmd_rd_empty) ? 1'b0: 1'b1);
assign wbs_cyc_o = (wbs_ack_f) ? 1'b0 : (wbs_burst) ? 1'b1 : ((s_cmd_rd_empty) ? 1'b0: 1'b1);

// Generate bust ready only we have space inside response fifo
// In Write Phase, 
//      Generate burst ready, only when we have wdata & space in response fifo 
// In Read Phase 
//      Generate burst ready, only when space in response fifo 
//
assign wbs_bry_o = (wbs_we_o) ? ((s_cmd_rd_empty || s_resp_wr_afull || s_resp_wr_full ) ? 1'b0: 1'b1) :
	                         (s_resp_wr_afull || s_resp_wr_full ) ? 1'b0: 1'b1;

// During Write phase, cmd fifo will have wdata, so dequeue for every ack
// During Read Phase, cmd fifo will be written only one time, hold the bus
// untill last ack received
assign s_cmd_rd_en = (wbs_stb_o && wbs_we_o) ? wbs_ack_i: wbs_lack_i;

// Write Interface
// response send only for read logic
assign s_resp_wr_en   = wbs_stb_o & wbs_ack_i & !s_resp_wr_full;
assign s_resp_wr_data = {wbs_err_i,wbs_lack_i,wbs_dat_i};

async_fifo #(.W(CFW), .DP(4), .WR_FAST(1), .RD_FAST(1)) u_cmd_if (
	           // Sync w.r.t WR clock
	           .wr_clk        (wbm_clk_i         ),
                   .wr_reset_n    (wbm_rst_n         ),
                   .wr_en         (m_cmd_wr_en       ),
                   .wr_data       (m_cmd_wr_data     ),
                   .full          (m_cmd_wr_full     ),                 
                   .afull         (m_cmd_wr_afull    ),                 

		   // Sync w.r.t RD Clock
                   .rd_clk        (wbs_clk_i         ),
                   .rd_reset_n    (wbs_rst_n         ),
                   .rd_en         (s_cmd_rd_en       ),
                   .empty         (s_cmd_rd_empty    ), // sync'ed to rd_clk
                   .aempty        (s_cmd_rd_aempty   ), // sync'ed to rd_clk
                   .rd_data       (s_cmd_rd_data     )
	     );


// Response used only for read path, 
// As cache access will be busrt of 512 location, To 
// support continous ack, depth is increase to 8 location
async_fifo #(.W(RFW), .DP(4), .WR_FAST(1), .RD_FAST(1)) u_resp_if (
	           // Sync w.r.t WR clock
	           .wr_clk        (wbs_clk_i          ),
                   .wr_reset_n    (wbs_rst_n          ),
                   .wr_en         (s_resp_wr_en       ),
                   .wr_data       (s_resp_wr_data     ),
                   .full          (s_resp_wr_full     ),                 
                   .afull         (s_resp_wr_afull    ),                 

		   // Sync w.r.t RD Clock
                   .rd_clk        (wbm_clk_i          ),
                   .rd_reset_n    (wbm_rst_n          ),
                   .rd_en         (m_resp_rd_en       ),
                   .empty         (m_resp_rd_empty    ), // sync'ed to rd_clk
                   .aempty        (m_resp_rd_aempty   ), // sync'ed to rd_clk
                   .rd_data       (m_resp_rd_data     )
	     );



endmodule
