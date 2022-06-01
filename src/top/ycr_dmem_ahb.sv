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
////  Data memory AHB bridge                                              ////
////                                                                      ////
////  This file is part of the yifive cores project                       ////
////  https://github.com/dineshannayya/ycr.git                           ////
////                                                                      ////
////  Description:                                                        ////
////     Data memory AHB bridge                                           ////
////                                                                      ////
////  To Do:                                                              ////
////    nothing                                                           ////
////                                                                      ////
////  Author(s):                                                          ////
////      - Dinesh Annayya, dinesha@opencores.org                         ////
////                                                                      ////
////  Revision :                                                          ////
////     v0:    Initial version picked from syntacore/scr1                ////
////     v1:    June 7, 2021, Dinesh A                                    ////
////              Open source tool related cleanup                        ////
//////////////////////////////////////////////////////////////////////////////

`include "ycr_ahb.svh"
`include "ycr_memif.svh"

module ycr_dmem_ahb (
    // Control Signals
    input   logic                           rst_n,
    input   logic                           clk,

    // Core Interface
    output  logic                           dmem_req_ack,
    input   logic                           dmem_req,
    input   logic                           dmem_cmd,
    input   logic [1:0]                     dmem_width,
    input   logic   [YCR_AHB_WIDTH-1:0]    dmem_addr,
    input   logic   [YCR_AHB_WIDTH-1:0]    dmem_wdata,
    output  logic   [YCR_AHB_WIDTH-1:0]    dmem_rdata,
    output  logic [1:0]                     dmem_resp,

    // AHB Interface
    output  logic   [3:0]                   hprot,
    output  logic   [2:0]                   hburst,
    output  logic   [2:0]                   hsize,
    output  logic   [1:0]                   htrans,
    output  logic                           hmastlock,
    output  logic   [YCR_AHB_WIDTH-1:0]    haddr,
    output  logic                           hwrite,
    output  logic   [YCR_AHB_WIDTH-1:0]    hwdata,
    input   logic                           hready,
    input   logic   [YCR_AHB_WIDTH-1:0]    hrdata,
    input   logic                           hresp

);

//-------------------------------------------------------------------------------
// Local Parameters
//-------------------------------------------------------------------------------
`ifndef YCR_DMEM_AHB_OUT_BP
localparam  YCR_FIFO_WIDTH = 2;
localparam  YCR_FIFO_CNT_WIDTH = $clog2(YCR_FIFO_WIDTH+1);
`endif // YCR_DMEM_AHB_OUT_BP

//-------------------------------------------------------------------------------
// Local type declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    YCR_FSM_ADDR = 1'b0,
    YCR_FSM_DATA = 1'b1,
    YCR_FSM_ERR  = 1'bx
} type_ycr_fsm_e;

typedef struct packed {
    logic                           hwrite;
    logic   [2:0]                   hwidth;
    logic   [YCR_AHB_WIDTH-1:0]    haddr;
    logic   [YCR_AHB_WIDTH-1:0]    hwdata;
} type_ycr_req_fifo_s;

typedef struct packed {
    logic                           hwrite;
    logic   [2:0]                   hwidth;
    logic   [1:0]                   haddr;
    logic   [YCR_AHB_WIDTH-1:0]    hwdata;
} type_ycr_data_fifo_s;

typedef struct packed {
    logic                           hresp;
    logic   [2:0]                   hwidth;
    logic   [1:0]                   haddr;
    logic   [YCR_AHB_WIDTH-1:0]    hrdata;
} type_ycr_resp_fifo_s;

//-------------------------------------------------------------------------------
// Local functions
//-------------------------------------------------------------------------------
function automatic logic   [2:0] ycr_conv_mem2ahb_width (
    input   logic [1:0]              dmem_width
);
    logic   [2:0]   tmp;
begin
    case (dmem_width)
        YCR_MEM_WIDTH_BYTE : begin
            tmp = YCR_HSIZE_8B;
        end
        YCR_MEM_WIDTH_HWORD : begin
            tmp = YCR_HSIZE_16B;
        end
        YCR_MEM_WIDTH_WORD : begin
            tmp = YCR_HSIZE_32B;
        end
        default : begin
            tmp = YCR_HSIZE_ERR;
        end
    endcase
    ycr_conv_mem2ahb_width =  tmp; // cp.11
end
endfunction

function automatic logic[YCR_AHB_WIDTH-1:0] ycr_conv_mem2ahb_wdata (
    input   logic   [1:0]                   dmem_addr,
    input   logic [1:0]                     dmem_width,
    input   logic   [YCR_AHB_WIDTH-1:0]    dmem_wdata
);
    logic   [YCR_AHB_WIDTH-1:0]  tmp;
begin
    tmp = 'x;
    case (dmem_width)
        YCR_MEM_WIDTH_BYTE : begin
            case (dmem_addr)
                2'b00 : begin
                    tmp[7:0]   = dmem_wdata[7:0];
                end
                2'b01 : begin
                    tmp[15:8]  = dmem_wdata[7:0];
                end
                2'b10 : begin
                    tmp[23:16] = dmem_wdata[7:0];
                end
                2'b11 : begin
                    tmp[31:24] = dmem_wdata[7:0];
                end
                default : begin
                end
            endcase
        end
        YCR_MEM_WIDTH_HWORD : begin
            case (dmem_addr[1])
                1'b0 : begin
                    tmp[15:0]  = dmem_wdata[15:0];
                end
                1'b1 : begin
                    tmp[31:16] = dmem_wdata[15:0];
                end
                default : begin
                end
            endcase
        end
        YCR_MEM_WIDTH_WORD : begin
            tmp = dmem_wdata;
        end
        default : begin
        end
    endcase
    ycr_conv_mem2ahb_wdata = tmp;
end
endfunction

function automatic logic[YCR_AHB_WIDTH-1:0] ycr_conv_ahb2mem_rdata (
    input   logic [2:0]                 hwidth,
    input   logic [1:0]                 haddr,
    input   logic [YCR_AHB_WIDTH-1:0]  hrdata
);
    logic   [YCR_AHB_WIDTH-1:0]  tmp;
begin
    tmp = 'x;
    case (hwidth)
        YCR_HSIZE_8B : begin
            case (haddr)
                2'b00 : tmp[7:0] = hrdata[7:0];
                2'b01 : tmp[7:0] = hrdata[15:8];
                2'b10 : tmp[7:0] = hrdata[23:16];
                2'b11 : tmp[7:0] = hrdata[31:24];
                default : begin
                end
            endcase
        end
        YCR_HSIZE_16B : begin
            case (haddr[1])
                1'b0 : tmp[15:0] = hrdata[15:0];
                1'b1 : tmp[15:0] = hrdata[31:16];
                default : begin
                end
            endcase
        end
        YCR_HSIZE_32B : begin
            tmp = hrdata;
        end
        default : begin
        end
    endcase
    ycr_conv_ahb2mem_rdata = tmp;
end
endfunction

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
type_ycr_fsm_e                             fsm;
logic                                       req_fifo_rd;
logic                                       req_fifo_wr;
logic                                       req_fifo_up;
`ifdef YCR_DMEM_AHB_OUT_BP
type_ycr_req_fifo_s                        req_fifo_new;
type_ycr_req_fifo_s                        req_fifo_r;
type_ycr_req_fifo_s [0:0]                  req_fifo;
`else // YCR_DMEM_AHB_OUT_BP
type_ycr_req_fifo_s [0:YCR_FIFO_WIDTH-1]  req_fifo;
type_ycr_req_fifo_s [0:YCR_FIFO_WIDTH-1]  req_fifo_new;
logic       [YCR_FIFO_CNT_WIDTH-1:0]       req_fifo_cnt;
logic       [YCR_FIFO_CNT_WIDTH-1:0]       req_fifo_cnt_new;
`endif // YCR_DMEM_AHB_OUT_BP
logic                                       req_fifo_empty;
logic                                       req_fifo_full;

type_ycr_data_fifo_s                       data_fifo;
type_ycr_resp_fifo_s                       resp_fifo;
logic                                       resp_fifo_hready;

//-------------------------------------------------------------------------------
// Interface to Core
//-------------------------------------------------------------------------------
assign dmem_req_ack = ~req_fifo_full;
assign req_fifo_wr  = ~req_fifo_full & dmem_req;

assign dmem_rdata = ycr_conv_ahb2mem_rdata(resp_fifo.hwidth, resp_fifo.haddr, resp_fifo.hrdata);

assign dmem_resp = (resp_fifo_hready)
                    ? (resp_fifo.hresp == YCR_HRESP_OKAY)
                        ? YCR_MEM_RESP_RDY_OK
                        : YCR_MEM_RESP_RDY_ER
                    : YCR_MEM_RESP_NOTRDY ;

//-------------------------------------------------------------------------------
// REQ_FIFO
//-------------------------------------------------------------------------------
`ifdef YCR_DMEM_AHB_OUT_BP
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        req_fifo_full <= 1'b0;
    end else begin
        if (~req_fifo_full) begin
            req_fifo_full <= dmem_req & ~req_fifo_rd;
        end else begin
            req_fifo_full <= ~req_fifo_rd;
        end
    end
end
assign req_fifo_empty = ~(req_fifo_full | dmem_req);

assign req_fifo_up = ~req_fifo_rd & req_fifo_wr;
always_ff @(posedge clk) begin
    if (req_fifo_up) begin
        req_fifo_r <= req_fifo_new;
    end
end

assign req_fifo_new.hwrite = dmem_req ? (dmem_cmd == YCR_MEM_CMD_WR)       : 1'b0;
assign req_fifo_new.hwidth = dmem_req ? ycr_conv_mem2ahb_width(dmem_width) : '0;
assign req_fifo_new.haddr  = dmem_req ? dmem_addr                           : '0;
assign req_fifo_new.hwdata = (dmem_req & (dmem_cmd == YCR_MEM_CMD_WR))
                                ? ycr_conv_mem2ahb_wdata(dmem_addr[1:0], dmem_width, dmem_wdata)
                                : '0;
assign req_fifo[0] = (req_fifo_full) ? req_fifo_r: req_fifo_new;

`else // YCR_DMEM_AHB_OUT_BP
always_comb begin
    req_fifo_up      = 1'b0;
    req_fifo_cnt_new = req_fifo_cnt;
    req_fifo_new     = req_fifo;
    case ({req_fifo_rd, req_fifo_wr})
        2'b00 : begin
            // nothing todo
        end
        2'b01: begin
            // FIFO write
            req_fifo_up = 1'b1;
            req_fifo_new[req_fifo_cnt].hwrite = (dmem_cmd == YCR_MEM_CMD_WR);
            req_fifo_new[req_fifo_cnt].hwidth = ycr_conv_mem2ahb_width(dmem_width);
            req_fifo_new[req_fifo_cnt].haddr  = dmem_addr;
            req_fifo_new[req_fifo_cnt].hwdata = ycr_conv_mem2ahb_wdata(dmem_addr[1:0], dmem_width, dmem_wdata);
            req_fifo_cnt_new = req_fifo_cnt + 1'b1;
        end
        2'b10 : begin
            // FIFO read
            req_fifo_up = 1'b1;
            req_fifo_new[0] = req_fifo_new[1];
            req_fifo_new[1].hwrite = 1'b0;
            req_fifo_new[1].hwidth = YCR_HSIZE_32B;
            req_fifo_new[1].haddr  = 'x;
            req_fifo_new[1].hwdata = 'x;
            req_fifo_cnt_new = req_fifo_cnt - 1'b1;
        end
        2'b11 : begin
            // Read and Write FIFO. It is possible only when fifo_cnt = 1
            req_fifo_up = 1'b1;
            req_fifo_new[0].hwrite = (dmem_cmd == YCR_MEM_CMD_WR);
            req_fifo_new[0].hwidth = ycr_conv_mem2ahb_width(dmem_width);
            req_fifo_new[0].haddr  = dmem_addr;
            req_fifo_new[0].hwdata = ycr_conv_mem2ahb_wdata(dmem_addr[1:0], dmem_width, dmem_wdata);
        end
        default : begin
            req_fifo_up      = 'x;
            req_fifo_cnt_new = 'x;
            req_fifo_new     = 'x;
        end
    endcase
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        req_fifo_cnt <= '0;
    end else begin
        if (req_fifo_up) begin
            req_fifo_cnt <= req_fifo_cnt_new;
        end
    end
end
assign req_fifo_full  = (req_fifo_cnt == YCR_FIFO_WIDTH);
assign req_fifo_empty = ~(|req_fifo_cnt);

always_ff @(posedge clk) begin
    if (req_fifo_up) begin
        req_fifo <= req_fifo_new;
    end
end
`endif // YCR_DMEM_AHB_OUT_BP
//-------------------------------------------------------------------------------
// FSM
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm <= YCR_FSM_ADDR;
    end else begin
        case (fsm)
            YCR_FSM_ADDR : begin
                if (hready) begin
                    fsm <= (req_fifo_empty) ? YCR_FSM_ADDR : YCR_FSM_DATA;
                end
            end
            YCR_FSM_DATA : begin
                if (hready) begin
                    if (hresp == YCR_HRESP_OKAY) begin
                        fsm <= (req_fifo_empty) ? YCR_FSM_ADDR : YCR_FSM_DATA;
                    end else begin
                        fsm <= YCR_FSM_ADDR;
                    end
                end
            end
            default : begin
                fsm <= YCR_FSM_ERR;
            end
        endcase
    end
end

always_comb begin
    req_fifo_rd = 1'b0;
    case (fsm)
        YCR_FSM_ADDR : begin
            if (hready) begin
                req_fifo_rd = ~req_fifo_empty;
            end
        end
        YCR_FSM_DATA : begin
            if (hready) begin
                req_fifo_rd = ~req_fifo_empty & (hresp == YCR_HRESP_OKAY);
            end
        end
        default : begin
            req_fifo_rd = 1'bx;
        end
    endcase
end

//-------------------------------------------------------------------------------
// FIFO data
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    case (fsm)
        YCR_FSM_ADDR : begin
            if (~req_fifo_empty) begin
                data_fifo.hwrite <= req_fifo[0].hwrite;
                data_fifo.hwidth <= req_fifo[0].hwidth;
                data_fifo.haddr  <= req_fifo[0].haddr[1:0];
                data_fifo.hwdata <= req_fifo[0].hwdata;
            end
        end
        YCR_FSM_DATA : begin
            if (hready) begin
                if (hresp == YCR_HRESP_OKAY) begin
                    if (~req_fifo_empty) begin
                        data_fifo.hwrite <= req_fifo[0].hwrite;
                        data_fifo.hwidth <= req_fifo[0].hwidth;
                        data_fifo.haddr  <= req_fifo[0].haddr[1:0];
                        data_fifo.hwdata <= req_fifo[0].hwdata;
                    end
                end
            end
        end
        default : begin
        end
    endcase
end

//-------------------------------------------------------------------------------
// FIFO response
//-------------------------------------------------------------------------------
`ifdef YCR_DMEM_AHB_IN_BP
assign resp_fifo_hready = (fsm == YCR_FSM_DATA) ? hready : 1'b0;
assign resp_fifo.hresp  = hresp;
assign resp_fifo.hwidth = data_fifo.hwidth;
assign resp_fifo.haddr  = data_fifo.haddr;
assign resp_fifo.hrdata = hrdata;
`else // YCR_DMEM_AHB_IN_BP
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        resp_fifo_hready <= 1'b0;
    end else begin
        resp_fifo_hready <= (fsm == YCR_FSM_DATA) ? hready : 1'b0;
    end
end

always_ff @(posedge clk) begin
    if (hready & (fsm == YCR_FSM_DATA)) begin
        resp_fifo.hresp  <= hresp;
        resp_fifo.hwidth <= data_fifo.hwidth;
        resp_fifo.haddr  <= data_fifo.haddr;
        resp_fifo.hrdata <= hrdata;
    end
end
`endif // YCR_DMEM_AHB_IN_BP

//-------------------------------------------------------------------------------
// Interface to AHB
//-------------------------------------------------------------------------------
assign hprot[YCR_HPROT_DATA]  = 1'b1;
assign hprot[YCR_HPROT_PRV]   = 1'b0;
assign hprot[YCR_HPROT_BUF]   = 1'b0;
assign hprot[YCR_HPROT_CACHE] = 1'b0;

assign hburst       = YCR_HBURST_SINGLE;
assign hsize        = req_fifo[0].hwidth;
assign hmastlock    = 1'b0;

always_comb begin
    htrans = YCR_HTRANS_IDLE;
    case (fsm)
        YCR_FSM_ADDR : begin
            if (~req_fifo_empty) begin
                htrans = YCR_HTRANS_NONSEQ;
            end
        end
        YCR_FSM_DATA : begin
            if (hready) begin
                if (hresp == YCR_HRESP_OKAY) begin
                    if (~req_fifo_empty) begin
                        htrans = YCR_HTRANS_NONSEQ;
                    end
                end
            end
        end
        default : begin
            htrans = YCR_HTRANS_ERR;
        end
    endcase
end

assign haddr  = req_fifo[0].haddr;
assign hwrite = req_fifo[0].hwrite;
assign hwdata = data_fifo.hwdata;

endmodule : ycr_dmem_ahb
