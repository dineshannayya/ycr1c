// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vycr1_async_wbb.h for the primary calling header

#include "Vycr1_async_wbb.h"
#include "Vycr1_async_wbb__Syms.h"

//==========

VerilatedContext* Vycr1_async_wbb::contextp() {
    return __VlSymsp->_vm_contextp__;
}

void Vycr1_async_wbb::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vycr1_async_wbb::eval\n"); );
    Vycr1_async_wbb__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("ycr1_async_wbb.sv", 74, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vycr1_async_wbb::_eval_initial_loop(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("ycr1_async_wbb.sv", 74, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__1(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__1\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->async_wb__DOT__wbs_ack_f = ((IData)(vlTOPp->wbs_rst_n) 
                                        & (IData)(vlTOPp->wbs_ack_i));
    if (vlTOPp->wbs_rst_n) {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_1 
            = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_0;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_1 
            = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_0;
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_1 = 0U;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_1 = 0U;
    }
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_1;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8 
        = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 
        = ((0xffU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | (0x100U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8) 
                  >> 6U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8) 
                                   >> 6U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 
        = ((0x13fU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__Vfuncout) 
              << 6U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8) 
                  >> 4U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8) 
                                   >> 4U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 
        = ((0x1cfU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__Vfuncout) 
              << 4U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8) 
                  >> 2U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8) 
                                   >> 2U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 
        = ((0x1f3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__Vfuncout) 
              << 2U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 
        = ((0x1fcU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8)) 
           | (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__Vfuncout));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__Vfuncout 
        = (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr 
        = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__Vfuncout;
    if (vlTOPp->wbs_rst_n) {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_0 
            = vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_rd_ptr;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_0 
            = vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_wr_ptr;
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_0 = 0U;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_0 = 0U;
    }
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_1;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8 
        = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 
        = ((0xffU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | (0x100U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8) 
                  >> 6U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8) 
                                   >> 6U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 
        = ((0x13fU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__Vfuncout) 
              << 6U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8) 
                  >> 4U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8) 
                                   >> 4U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 
        = ((0x1cfU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__Vfuncout) 
              << 4U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8) 
                  >> 2U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8) 
                                   >> 2U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 
        = ((0x1f3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__Vfuncout) 
              << 2U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 
        = ((0x1fcU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8)) 
           | (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__Vfuncout));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__Vfuncout 
        = (7U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8));
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr 
        = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__Vfuncout;
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__2(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__2\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin;
    CData/*0:0*/ __Vdly__async_wb__DOT__PendingRd;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8;
    // Body
    __Vdly__async_wb__DOT__PendingRd = vlTOPp->async_wb__DOT__PendingRd;
    if (vlTOPp->wbm_rst_n) {
        if (((((~ (IData)(vlTOPp->async_wb__DOT__PendingRd)) 
               & (IData)(vlTOPp->wbm_stb_i)) & (~ (IData)(vlTOPp->wbm_we_i))) 
             & (IData)(vlTOPp->async_wb__DOT__m_cmd_wr_en))) {
            __Vdly__async_wb__DOT__PendingRd = 1U;
        } else {
            if (((((IData)(vlTOPp->async_wb__DOT__PendingRd) 
                   & (IData)(vlTOPp->wbm_stb_i)) & 
                  (~ (IData)(vlTOPp->wbm_we_i))) & (IData)(vlTOPp->wbm_ack_o))) {
                __Vdly__async_wb__DOT__PendingRd = 0U;
            }
        }
    } else {
        __Vdly__async_wb__DOT__PendingRd = 0U;
    }
    if (vlTOPp->wbm_rst_n) {
        if (vlTOPp->async_wb__DOT__m_cmd_wr_en) {
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin 
                = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8 
                = __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin;
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8 
                = ((0x1fcU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8)) 
                   | (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__2__Vfuncout));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8) 
                         >> 2U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8 
                = ((0x1f3U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__3__Vfuncout) 
                      << 2U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8) 
                         >> 4U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8 
                = ((0x1cfU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__4__Vfuncout) 
                      << 4U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8) 
                         >> 6U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8 
                = ((0x13fU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__5__Vfuncout) 
                      << 6U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8 
                = ((0xffU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8)) 
                   | (0x100U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__bin_8)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__Vfuncout 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__grey_8));
            vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_wr_ptr 
                = __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__1__Vfuncout;
        }
    } else {
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_wr_ptr = 0U;
    }
    if (vlTOPp->wbm_rst_n) {
        if ((0U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt))) {
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin 
                = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8 
                = __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin;
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8 
                = ((0x1fcU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8)) 
                   | (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__35__Vfuncout));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8) 
                         >> 2U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8 
                = ((0x1f3U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__36__Vfuncout) 
                      << 2U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8) 
                         >> 4U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8 
                = ((0x1cfU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__37__Vfuncout) 
                      << 4U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8) 
                         >> 6U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8 
                = ((0x13fU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__38__Vfuncout) 
                      << 6U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8 
                = ((0xffU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8)) 
                   | (0x100U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__bin_8)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__Vfuncout 
                = (3U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__grey_8));
            vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_rd_ptr 
                = __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__34__Vfuncout;
        }
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_rd_ptr = 0U;
    }
    if (vlTOPp->wbm_rst_n) {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_1 
            = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_0;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_1 
            = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_0;
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_1 = 0U;
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_1 = 0U;
    }
    vlTOPp->async_wb__DOT__PendingRd = __Vdly__async_wb__DOT__PendingRd;
    if (vlTOPp->wbm_rst_n) {
        if ((0U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt))) {
            vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr 
                = vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr_inc;
        }
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr = 0U;
    }
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_1;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8 
        = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 
        = ((0xffU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | (0x100U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8) 
                  >> 6U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8) 
                                   >> 6U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 
        = ((0x13fU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__Vfuncout) 
              << 6U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8) 
                  >> 4U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8) 
                                   >> 4U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 
        = ((0x1cfU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__Vfuncout) 
              << 4U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8) 
                  >> 2U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8) 
                                   >> 2U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 
        = ((0x1f3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__Vfuncout) 
              << 2U));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 
        = ((0x1fcU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8)) 
           | (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__Vfuncout));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__Vfuncout 
        = (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr 
        = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__Vfuncout;
    vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_0 
        = ((IData)(vlTOPp->wbm_rst_n) ? (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_wr_ptr)
            : 0U);
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_1;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8 
        = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 
        = ((0xffU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | (0x100U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8) 
                  >> 6U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8) 
                                   >> 6U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 
        = ((0x13fU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__Vfuncout) 
              << 6U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8) 
                  >> 4U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8) 
                                   >> 4U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 
        = ((0x1cfU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__Vfuncout) 
              << 4U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey 
        = ((4U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8) 
                  >> 2U)) | (3U & ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8) 
                                   >> 2U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 
        = ((0x1f3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__Vfuncout) 
              << 2U));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | (3U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__Vfuncout 
        = ((4U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
            ? ((2U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                ? ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                    ? 1U : 0U) : ((1U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                                   ? 2U : 3U)) : ((2U 
                                                   & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                                                   ? 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                                                    ? 2U
                                                    : 3U)
                                                   : 
                                                  ((1U 
                                                    & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey))
                                                    ? 1U
                                                    : 0U)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 
        = ((0x1fcU & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8)) 
           | (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__Vfuncout));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__Vfuncout 
        = (7U & (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8));
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr 
        = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__Vfuncout;
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_0 
        = ((IData)(vlTOPp->wbm_rst_n) ? (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_rd_ptr)
            : 0U);
    vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr_inc 
        = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr)));
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__3(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__3\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*0:0*/ __Vdlyvdim0__async_wb__DOT__u_resp_if__DOT__mem__v0;
    CData/*0:0*/ __Vdlyvset__async_wb__DOT__u_resp_if__DOT__mem__v0;
    QData/*33:0*/ __Vdlyvval__async_wb__DOT__u_resp_if__DOT__mem__v0;
    // Body
    __Vdlyvset__async_wb__DOT__u_resp_if__DOT__mem__v0 = 0U;
    if (VL_UNLIKELY(((IData)(vlTOPp->async_wb__DOT__s_resp_wr_en) 
                     & (2U == (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_cnt))))) {
        VL_WRITEF("%20#%Nasync_wb.u_resp_if Error! afifo overflow!\n",
                  64,VL_TIME_UNITED_Q(1),vlSymsp->name());
        VL_STOP_MT("async_fifo.sv", 329, "");
    }
    if (VL_UNLIKELY(((IData)(vlTOPp->wbs_ack_i) & (0U 
                                                   == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))))) {
        VL_WRITEF("%20#%Nasync_wb.u_cmd_if error! afifo underflow!\n",
                  64,VL_TIME_UNITED_Q(1),vlSymsp->name());
        VL_STOP_MT("async_fifo.sv", 336, "");
    }
    if (vlTOPp->async_wb__DOT__s_resp_wr_en) {
        __Vdlyvval__async_wb__DOT__u_resp_if__DOT__mem__v0 
            = (((QData)((IData)(vlTOPp->wbs_err_i)) 
                << 0x21U) | (((QData)((IData)(vlTOPp->wbs_lack_i)) 
                              << 0x20U) | (QData)((IData)(vlTOPp->wbs_dat_i))));
        __Vdlyvset__async_wb__DOT__u_resp_if__DOT__mem__v0 = 1U;
        __Vdlyvdim0__async_wb__DOT__u_resp_if__DOT__mem__v0 
            = (1U & (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr));
    }
    if (__Vdlyvset__async_wb__DOT__u_resp_if__DOT__mem__v0) {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__mem[__Vdlyvdim0__async_wb__DOT__u_resp_if__DOT__mem__v0] 
            = __Vdlyvval__async_wb__DOT__u_resp_if__DOT__mem__v0;
    }
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__4(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__4\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*1:0*/ __Vdlyvdim0__async_wb__DOT__u_cmd_if__DOT__mem__v0;
    CData/*0:0*/ __Vdlyvset__async_wb__DOT__u_cmd_if__DOT__mem__v0;
    VlWide<3>/*78:0*/ __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0;
    // Body
    if (VL_UNLIKELY(((0U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt)) 
                     & (0U == (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt))))) {
        VL_WRITEF("%20#%Nasync_wb.u_resp_if error! afifo underflow!\n",
                  64,VL_TIME_UNITED_Q(1),vlSymsp->name());
        VL_STOP_MT("async_fifo.sv", 336, "");
    }
    if (VL_UNLIKELY(((IData)(vlTOPp->async_wb__DOT__m_cmd_wr_en) 
                     & (4U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt))))) {
        VL_WRITEF("%20#%Nasync_wb.u_cmd_if Error! afifo overflow!\n",
                  64,VL_TIME_UNITED_Q(1),vlSymsp->name());
        VL_STOP_MT("async_fifo.sv", 329, "");
    }
    __Vdlyvset__async_wb__DOT__u_cmd_if__DOT__mem__v0 = 0U;
    if (vlTOPp->async_wb__DOT__m_cmd_wr_en) {
        __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[0U] 
            = (IData)((((QData)((IData)(vlTOPp->wbm_we_i)) 
                        << 0x2eU) | (((QData)((IData)(vlTOPp->wbm_dat_i)) 
                                      << 0xeU) | (QData)((IData)(
                                                                 (((IData)(vlTOPp->wbm_sel_i) 
                                                                   << 0xaU) 
                                                                  | (IData)(vlTOPp->wbm_bl_i)))))));
        __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[1U] 
            = ((0xffff8000U & (vlTOPp->wbm_adr_i << 0xfU)) 
               | (IData)(((((QData)((IData)(vlTOPp->wbm_we_i)) 
                            << 0x2eU) | (((QData)((IData)(vlTOPp->wbm_dat_i)) 
                                          << 0xeU) 
                                         | (QData)((IData)(
                                                           (((IData)(vlTOPp->wbm_sel_i) 
                                                             << 0xaU) 
                                                            | (IData)(vlTOPp->wbm_bl_i)))))) 
                          >> 0x20U)));
        __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[2U] 
            = (0x7fffU & (vlTOPp->wbm_adr_i >> 0x11U));
        __Vdlyvset__async_wb__DOT__u_cmd_if__DOT__mem__v0 = 1U;
        __Vdlyvdim0__async_wb__DOT__u_cmd_if__DOT__mem__v0 
            = (3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr));
    }
    if (__Vdlyvset__async_wb__DOT__u_cmd_if__DOT__mem__v0) {
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem[__Vdlyvdim0__async_wb__DOT__u_cmd_if__DOT__mem__v0][0U] 
            = __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[0U];
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem[__Vdlyvdim0__async_wb__DOT__u_cmd_if__DOT__mem__v0][1U] 
            = __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[1U];
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem[__Vdlyvdim0__async_wb__DOT__u_cmd_if__DOT__mem__v0][2U] 
            = __Vdlyvval__async_wb__DOT__u_cmd_if__DOT__mem__v0[2U];
    }
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__6(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__6\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__Vfuncout;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin;
    CData/*1:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__Vfuncout;
    CData/*2:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8;
    SData/*8:0*/ __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8;
    // Body
    if (vlTOPp->wbs_rst_n) {
        if (vlTOPp->async_wb__DOT__s_resp_wr_en) {
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin 
                = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8 
                = __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin;
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8 
                = ((0x1fcU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8)) 
                   | (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__24__Vfuncout));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8) 
                         >> 2U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8 
                = ((0x1f3U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__25__Vfuncout) 
                      << 2U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8) 
                         >> 4U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8 
                = ((0x1cfU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__26__Vfuncout) 
                      << 4U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8) 
                         >> 6U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8 
                = ((0x13fU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__do_grey__27__Vfuncout) 
                      << 6U));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8 
                = ((0xffU & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8)) 
                   | (0x100U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__bin_8)));
            __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__Vfuncout 
                = (3U & (IData)(__Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__grey_8));
            vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_wr_ptr 
                = __Vfunc_async_wb__DOT__u_resp_if__DOT__bin2grey__23__Vfuncout;
        }
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__grey_wr_ptr = 0U;
    }
    if (vlTOPp->wbs_rst_n) {
        if (vlTOPp->wbs_ack_i) {
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin 
                = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8 
                = __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin;
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8 
                = ((0x1fcU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8)) 
                   | (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__13__Vfuncout));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8) 
                         >> 2U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8 
                = ((0x1f3U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__14__Vfuncout) 
                      << 2U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8) 
                         >> 4U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8 
                = ((0x1cfU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__15__Vfuncout) 
                      << 4U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin 
                = (7U & ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8) 
                         >> 6U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__Vfuncout 
                = ((4U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                    ? ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                            ? 0U : 1U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                                           ? 3U : 2U))
                    : ((2U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                        ? ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                            ? 2U : 3U) : ((1U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__bin))
                                           ? 1U : 0U)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8 
                = ((0x13fU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8)) 
                   | ((IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__do_grey__16__Vfuncout) 
                      << 6U));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8 
                = ((0xffU & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8)) 
                   | (0x100U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__bin_8)));
            __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__Vfuncout 
                = (7U & (IData)(__Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__grey_8));
            vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_rd_ptr 
                = __Vfunc_async_wb__DOT__u_cmd_if__DOT__bin2grey__12__Vfuncout;
        }
    } else {
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__grey_rd_ptr = 0U;
    }
    if (vlTOPp->wbs_rst_n) {
        if (vlTOPp->async_wb__DOT__s_resp_wr_en) {
            vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr 
                = vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr_inc;
        }
    } else {
        vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr = 0U;
    }
    if (vlTOPp->wbs_rst_n) {
        if (vlTOPp->wbs_ack_i) {
            vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr 
                = vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr_inc;
        }
    } else {
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr = 0U;
    }
    vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr_inc 
        = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr)));
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_rd_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__Vfuncout 
        = (3U & (((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr) 
                  >= (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr))
                  ? ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr) 
                     - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr))
                  : (- ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr) 
                        - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr)))));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_cnt = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__Vfuncout;
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr_inc 
        = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__Vfuncout 
        = (7U & (((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr) 
                  >= (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr))
                  ? ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr) 
                     - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr))
                  : (- ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr) 
                        - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr)))));
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__Vfuncout;
    vlTOPp->wbs_cyc_o = ((~ (IData)(vlTOPp->async_wb__DOT__wbs_ack_f)) 
                         & (0U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt)));
    vlTOPp->wbs_stb_o = ((~ (IData)(vlTOPp->async_wb__DOT__wbs_ack_f)) 
                         & (0U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt)));
}

VL_INLINE_OPT void Vycr1_async_wbb::_multiclk__TOP__7(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_multiclk__TOP__7\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__mem
        [(1U & (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr))];
    vlTOPp->wbm_dat_o = (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c);
    vlTOPp->wbm_lack_o = (1U & (IData)((vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
                                        >> 0x20U)));
    vlTOPp->wbm_err_o = (1U & (IData)((vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
                                       >> 0x21U)));
}

VL_INLINE_OPT void Vycr1_async_wbb::_sequent__TOP__8(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_sequent__TOP__8\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__sync_wr_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__Vfuncout 
        = (3U & (((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr) 
                  >= (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr))
                  ? ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr) 
                     - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr))
                  : (- ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr) 
                        - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr)))));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt = vlTOPp->__Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__Vfuncout;
    if (vlTOPp->wbm_rst_n) {
        if (vlTOPp->async_wb__DOT__m_cmd_wr_en) {
            vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr 
                = vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr_inc;
        }
    } else {
        vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr = 0U;
    }
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr_inc 
        = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr)));
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr;
    vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__Vfuncout 
        = (7U & (((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr) 
                  >= (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr))
                  ? ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr) 
                     - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr))
                  : (- ((IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr) 
                        - (IData)(vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr)))));
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt = vlTOPp->__Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__Vfuncout;
}

VL_INLINE_OPT void Vycr1_async_wbb::_multiclk__TOP__9(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_multiclk__TOP__9\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[0U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][0U];
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][1U];
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[2U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][2U];
    vlTOPp->wbs_adr_o = ((((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                            ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[2U]) 
                          << 0x11U) | (((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                         ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U]) 
                                       >> 0xfU));
    vlTOPp->wbs_dat_o = ((((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                            ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U]) 
                          << 0x12U) | (((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                         ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[0U]) 
                                       >> 0xeU));
    vlTOPp->wbs_sel_o = (0xfU & ((((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                    ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U]) 
                                  << 0x16U) | (((0U 
                                                 == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                                 ? 0U
                                                 : 
                                                vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[0U]) 
                                               >> 0xaU)));
    vlTOPp->wbs_bl_o = ((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                         ? 0U : (0x3ffU & vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[0U]));
    vlTOPp->wbs_we_o = (1U & (((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U]) 
                              >> 0xeU));
}

VL_INLINE_OPT void Vycr1_async_wbb::_combo__TOP__10(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_combo__TOP__10\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->async_wb__DOT__m_cmd_wr_en = ((((~ (IData)(vlTOPp->async_wb__DOT__PendingRd)) 
                                            & (IData)(vlTOPp->wbm_stb_i)) 
                                           & (4U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt))) 
                                          & (3U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt)));
    vlTOPp->async_wb__DOT__s_resp_wr_en = ((((IData)(vlTOPp->wbs_stb_o) 
                                             & (~ (IData)(vlTOPp->wbs_we_o))) 
                                            & (IData)(vlTOPp->wbs_ack_i)) 
                                           & (2U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_cnt)));
    vlTOPp->wbm_ack_o = (((IData)(vlTOPp->wbm_stb_i) 
                          & (IData)(vlTOPp->wbm_we_i))
                          ? (IData)(vlTOPp->async_wb__DOT__m_cmd_wr_en)
                          : (((IData)(vlTOPp->wbm_stb_i) 
                              & (~ (IData)(vlTOPp->wbm_we_i))) 
                             & (0U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt))));
}

void Vycr1_async_wbb::_eval(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_eval\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->wbs_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbs_clk_i))) 
         | ((~ (IData)(vlTOPp->wbs_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbs_rst_n)))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    if ((((IData)(vlTOPp->wbm_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbm_clk_i))) 
         | ((~ (IData)(vlTOPp->wbm_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbm_rst_n)))) {
        vlTOPp->_sequent__TOP__2(vlSymsp);
    }
    if (((IData)(vlTOPp->wbs_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbs_clk_i)))) {
        vlTOPp->_sequent__TOP__3(vlSymsp);
    }
    if (((IData)(vlTOPp->wbm_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbm_clk_i)))) {
        vlTOPp->_sequent__TOP__4(vlSymsp);
    }
    if ((((IData)(vlTOPp->wbs_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbs_clk_i))) 
         | ((~ (IData)(vlTOPp->wbs_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbs_rst_n)))) {
        vlTOPp->_sequent__TOP__6(vlSymsp);
    }
    if (((((IData)(vlTOPp->wbm_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbm_clk_i))) 
          | ((~ (IData)(vlTOPp->wbm_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbm_rst_n))) 
         | ((IData)(vlTOPp->wbs_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbs_clk_i))))) {
        vlTOPp->_multiclk__TOP__7(vlSymsp);
    }
    if ((((IData)(vlTOPp->wbm_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbm_clk_i))) 
         | ((~ (IData)(vlTOPp->wbm_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbm_rst_n)))) {
        vlTOPp->_sequent__TOP__8(vlSymsp);
    }
    if (((((IData)(vlTOPp->wbm_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbm_clk_i))) 
          | ((IData)(vlTOPp->wbs_clk_i) & (~ (IData)(vlTOPp->__Vclklast__TOP__wbs_clk_i)))) 
         | ((~ (IData)(vlTOPp->wbs_rst_n)) & (IData)(vlTOPp->__Vclklast__TOP__wbs_rst_n)))) {
        vlTOPp->_multiclk__TOP__9(vlSymsp);
    }
    vlTOPp->_combo__TOP__10(vlSymsp);
    // Final
    vlTOPp->__Vclklast__TOP__wbs_clk_i = vlTOPp->wbs_clk_i;
    vlTOPp->__Vclklast__TOP__wbs_rst_n = vlTOPp->wbs_rst_n;
    vlTOPp->__Vclklast__TOP__wbm_clk_i = vlTOPp->wbm_clk_i;
    vlTOPp->__Vclklast__TOP__wbm_rst_n = vlTOPp->wbm_rst_n;
}

VL_INLINE_OPT QData Vycr1_async_wbb::_change_request(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_change_request\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData Vycr1_async_wbb::_change_request_1(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_change_request_1\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void Vycr1_async_wbb::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((wbm_rst_n & 0xfeU))) {
        Verilated::overWidthError("wbm_rst_n");}
    if (VL_UNLIKELY((wbm_clk_i & 0xfeU))) {
        Verilated::overWidthError("wbm_clk_i");}
    if (VL_UNLIKELY((wbm_cyc_i & 0xfeU))) {
        Verilated::overWidthError("wbm_cyc_i");}
    if (VL_UNLIKELY((wbm_stb_i & 0xfeU))) {
        Verilated::overWidthError("wbm_stb_i");}
    if (VL_UNLIKELY((wbm_we_i & 0xfeU))) {
        Verilated::overWidthError("wbm_we_i");}
    if (VL_UNLIKELY((wbm_sel_i & 0xf0U))) {
        Verilated::overWidthError("wbm_sel_i");}
    if (VL_UNLIKELY((wbm_bl_i & 0xfc00U))) {
        Verilated::overWidthError("wbm_bl_i");}
    if (VL_UNLIKELY((wbs_rst_n & 0xfeU))) {
        Verilated::overWidthError("wbs_rst_n");}
    if (VL_UNLIKELY((wbs_clk_i & 0xfeU))) {
        Verilated::overWidthError("wbs_clk_i");}
    if (VL_UNLIKELY((wbs_ack_i & 0xfeU))) {
        Verilated::overWidthError("wbs_ack_i");}
    if (VL_UNLIKELY((wbs_lack_i & 0xfeU))) {
        Verilated::overWidthError("wbs_lack_i");}
    if (VL_UNLIKELY((wbs_err_i & 0xfeU))) {
        Verilated::overWidthError("wbs_err_i");}
}
#endif  // VL_DEBUG
