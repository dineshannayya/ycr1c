// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef VERILATED_VYCR1_ASYNC_WBB_H_
#define VERILATED_VYCR1_ASYNC_WBB_H_  // guard

#include "verilated_heavy.h"

//==========

class Vycr1_async_wbb__Syms;

//----------

VL_MODULE(Vycr1_async_wbb) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(wbm_rst_n,0,0);
    VL_IN8(wbm_clk_i,0,0);
    VL_IN8(wbs_rst_n,0,0);
    VL_IN8(wbs_clk_i,0,0);
    VL_IN8(wbm_cyc_i,0,0);
    VL_IN8(wbm_stb_i,0,0);
    VL_IN8(wbm_we_i,0,0);
    VL_IN8(wbm_sel_i,3,0);
    VL_OUT8(wbm_ack_o,0,0);
    VL_OUT8(wbm_lack_o,0,0);
    VL_OUT8(wbm_err_o,0,0);
    VL_OUT8(wbs_cyc_o,0,0);
    VL_OUT8(wbs_stb_o,0,0);
    VL_OUT8(wbs_we_o,0,0);
    VL_OUT8(wbs_sel_o,3,0);
    VL_IN8(wbs_ack_i,0,0);
    VL_IN8(wbs_lack_i,0,0);
    VL_IN8(wbs_err_i,0,0);
    VL_IN16(wbm_bl_i,9,0);
    VL_OUT16(wbs_bl_o,9,0);
    VL_IN(wbm_adr_i,31,0);
    VL_IN(wbm_dat_i,31,0);
    VL_OUT(wbm_dat_o,31,0);
    VL_OUT(wbs_adr_o,31,0);
    VL_OUT(wbs_dat_o,31,0);
    VL_IN(wbs_dat_i,31,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*0:0*/ async_wb__DOT__PendingRd;
    CData/*0:0*/ async_wb__DOT__m_cmd_wr_en;
    CData/*0:0*/ async_wb__DOT__s_resp_wr_en;
    CData/*0:0*/ async_wb__DOT__wbs_ack_f;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_0;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_1;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__wr_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__grey_wr_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__grey_rd_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__wr_ptr_inc;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__wr_cnt;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_0;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_1;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__rd_ptr;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__rd_ptr_inc;
    CData/*2:0*/ async_wb__DOT__u_cmd_if__DOT__rd_cnt;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_0;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_1;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_rd_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__wr_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__grey_wr_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__grey_rd_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__wr_ptr_inc;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__wr_cnt;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_0;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_1;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__sync_wr_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__rd_ptr;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__rd_ptr_inc;
    CData/*1:0*/ async_wb__DOT__u_resp_if__DOT__rd_cnt;
    VlWide<3>/*78:0*/ async_wb__DOT__u_cmd_if__DOT__rd_data_c;
    QData/*33:0*/ async_wb__DOT__u_resp_if__DOT__rd_data_c;
    VlUnpacked<VlWide<3>/*78:0*/, 4> async_wb__DOT__u_cmd_if__DOT__mem;
    VlUnpacked<QData/*33:0*/, 2> async_wb__DOT__u_resp_if__DOT__mem;
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey;
    CData/*0:0*/ __Vclklast__TOP__wbs_clk_i;
    CData/*0:0*/ __Vclklast__TOP__wbs_rst_n;
    CData/*0:0*/ __Vclklast__TOP__wbm_clk_i;
    CData/*0:0*/ __Vclklast__TOP__wbm_rst_n;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8;
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    Vycr1_async_wbb__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vycr1_async_wbb);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// If contextp is null, then the model will use the default global context
    /// If name is "", then makes a wrapper with a
    /// single model invisible with respect to DPI scope names.
    Vycr1_async_wbb(VerilatedContext* contextp, const char* name = "TOP");
    Vycr1_async_wbb(const char* name = "TOP")
      : Vycr1_async_wbb(nullptr, name) {}
    /// Destroy the model; called (often implicitly) by application code
    ~Vycr1_async_wbb();
    
    // API METHODS
    /// Return current simulation context for this model.
    /// Used to get to e.g. simulation time via contextp()->time()
    VerilatedContext* contextp();
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    
    // INTERNAL METHODS
    static void _eval_initial_loop(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    void __Vconfigure(Vycr1_async_wbb__Syms* symsp, bool first);
  private:
    static QData _change_request(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static QData _change_request_1(Vycr1_async_wbb__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__10(Vycr1_async_wbb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(Vycr1_async_wbb__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(Vycr1_async_wbb__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(Vycr1_async_wbb__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _multiclk__TOP__7(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _multiclk__TOP__9(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__1(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__2(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__3(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__4(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__6(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _sequent__TOP__8(Vycr1_async_wbb__Syms* __restrict vlSymsp);
    static void _settle__TOP__5(Vycr1_async_wbb__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
