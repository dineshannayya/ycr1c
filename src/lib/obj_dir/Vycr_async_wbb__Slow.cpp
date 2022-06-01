// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vycr1_async_wbb.h for the primary calling header

#include "Vycr1_async_wbb.h"
#include "Vycr1_async_wbb__Syms.h"

//==========

Vycr1_async_wbb::Vycr1_async_wbb(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModule{_vcname__}
 {
    Vycr1_async_wbb__Syms* __restrict vlSymsp = __VlSymsp = new Vycr1_async_wbb__Syms(_vcontextp__, this, name());
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void Vycr1_async_wbb::__Vconfigure(Vycr1_async_wbb__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    vlSymsp->_vm_contextp__->timeunit(-12);
    vlSymsp->_vm_contextp__->timeprecision(-12);
}

Vycr1_async_wbb::~Vycr1_async_wbb() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = nullptr);
}

void Vycr1_async_wbb::_settle__TOP__5(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_settle__TOP__5\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
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
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr_inc 
        = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_ptr)));
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr_inc 
        = (7U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr)));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr_inc 
        = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_ptr)));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr_inc 
        = (3U & ((IData)(1U) + (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr)));
    vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
        = vlTOPp->async_wb__DOT__u_resp_if__DOT__mem
        [(1U & (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_ptr))];
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[0U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][0U];
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][1U];
    vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[2U] 
        = vlTOPp->async_wb__DOT__u_cmd_if__DOT__mem
        [(3U & (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_ptr))][2U];
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
    vlTOPp->wbm_dat_o = (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c);
    vlTOPp->wbm_lack_o = (1U & (IData)((vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
                                        >> 0x20U)));
    vlTOPp->wbm_err_o = (1U & (IData)((vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_data_c 
                                       >> 0x21U)));
    vlTOPp->async_wb__DOT__m_cmd_wr_en = ((((~ (IData)(vlTOPp->async_wb__DOT__PendingRd)) 
                                            & (IData)(vlTOPp->wbm_stb_i)) 
                                           & (4U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt))) 
                                          & (3U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__wr_cnt)));
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
    vlTOPp->wbs_cyc_o = ((~ (IData)(vlTOPp->async_wb__DOT__wbs_ack_f)) 
                         & (0U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt)));
    vlTOPp->wbs_we_o = (1U & (((0U == (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt))
                                ? 0U : vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_data_c[1U]) 
                              >> 0xeU));
    vlTOPp->wbs_stb_o = ((~ (IData)(vlTOPp->async_wb__DOT__wbs_ack_f)) 
                         & (0U != (IData)(vlTOPp->async_wb__DOT__u_cmd_if__DOT__rd_cnt)));
    vlTOPp->wbm_ack_o = (((IData)(vlTOPp->wbm_stb_i) 
                          & (IData)(vlTOPp->wbm_we_i))
                          ? (IData)(vlTOPp->async_wb__DOT__m_cmd_wr_en)
                          : (((IData)(vlTOPp->wbm_stb_i) 
                              & (~ (IData)(vlTOPp->wbm_we_i))) 
                             & (0U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__rd_cnt))));
    vlTOPp->async_wb__DOT__s_resp_wr_en = ((((IData)(vlTOPp->wbs_stb_o) 
                                             & (~ (IData)(vlTOPp->wbs_we_o))) 
                                            & (IData)(vlTOPp->wbs_ack_i)) 
                                           & (2U != (IData)(vlTOPp->async_wb__DOT__u_resp_if__DOT__wr_cnt)));
}

void Vycr1_async_wbb::_eval_initial(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_eval_initial\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__wbs_clk_i = vlTOPp->wbs_clk_i;
    vlTOPp->__Vclklast__TOP__wbs_rst_n = vlTOPp->wbs_rst_n;
    vlTOPp->__Vclklast__TOP__wbm_clk_i = vlTOPp->wbm_clk_i;
    vlTOPp->__Vclklast__TOP__wbm_rst_n = vlTOPp->wbm_rst_n;
}

void Vycr1_async_wbb::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::final\n"); );
    // Variables
    Vycr1_async_wbb__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vycr1_async_wbb::_eval_settle(Vycr1_async_wbb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_eval_settle\n"); );
    Vycr1_async_wbb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__5(vlSymsp);
}

void Vycr1_async_wbb::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vycr1_async_wbb::_ctor_var_reset\n"); );
    // Body
    wbm_rst_n = VL_RAND_RESET_I(1);
    wbm_clk_i = VL_RAND_RESET_I(1);
    wbm_cyc_i = VL_RAND_RESET_I(1);
    wbm_stb_i = VL_RAND_RESET_I(1);
    wbm_adr_i = VL_RAND_RESET_I(32);
    wbm_we_i = VL_RAND_RESET_I(1);
    wbm_dat_i = VL_RAND_RESET_I(32);
    wbm_sel_i = VL_RAND_RESET_I(4);
    wbm_bl_i = VL_RAND_RESET_I(10);
    wbm_dat_o = VL_RAND_RESET_I(32);
    wbm_ack_o = VL_RAND_RESET_I(1);
    wbm_lack_o = VL_RAND_RESET_I(1);
    wbm_err_o = VL_RAND_RESET_I(1);
    wbs_rst_n = VL_RAND_RESET_I(1);
    wbs_clk_i = VL_RAND_RESET_I(1);
    wbs_cyc_o = VL_RAND_RESET_I(1);
    wbs_stb_o = VL_RAND_RESET_I(1);
    wbs_adr_o = VL_RAND_RESET_I(32);
    wbs_we_o = VL_RAND_RESET_I(1);
    wbs_dat_o = VL_RAND_RESET_I(32);
    wbs_sel_o = VL_RAND_RESET_I(4);
    wbs_bl_o = VL_RAND_RESET_I(10);
    wbs_dat_i = VL_RAND_RESET_I(32);
    wbs_ack_i = VL_RAND_RESET_I(1);
    wbs_lack_i = VL_RAND_RESET_I(1);
    wbs_err_i = VL_RAND_RESET_I(1);
    async_wb__DOT__PendingRd = VL_RAND_RESET_I(1);
    async_wb__DOT__m_cmd_wr_en = VL_RAND_RESET_I(1);
    async_wb__DOT__s_resp_wr_en = VL_RAND_RESET_I(1);
    async_wb__DOT__wbs_ack_f = VL_RAND_RESET_I(1);
    for (int __Vi0=0; __Vi0<4; ++__Vi0) {
        VL_RAND_RESET_W(79, async_wb__DOT__u_cmd_if__DOT__mem[__Vi0]);
    }
    async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_0 = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr_1 = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__sync_rd_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__wr_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__grey_wr_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__grey_rd_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__wr_ptr_inc = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__wr_cnt = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_0 = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr_1 = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__sync_wr_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__rd_ptr = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__rd_ptr_inc = VL_RAND_RESET_I(3);
    async_wb__DOT__u_cmd_if__DOT__rd_cnt = VL_RAND_RESET_I(3);
    VL_RAND_RESET_W(79, async_wb__DOT__u_cmd_if__DOT__rd_data_c);
    for (int __Vi0=0; __Vi0<2; ++__Vi0) {
        async_wb__DOT__u_resp_if__DOT__mem[__Vi0] = VL_RAND_RESET_Q(34);
    }
    async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_0 = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__sync_rd_ptr_1 = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__sync_rd_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__wr_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__grey_wr_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__grey_rd_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__wr_ptr_inc = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__wr_cnt = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_0 = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__sync_wr_ptr_1 = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__sync_wr_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__rd_ptr = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__rd_ptr_inc = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__rd_cnt = VL_RAND_RESET_I(2);
    async_wb__DOT__u_resp_if__DOT__rd_data_c = VL_RAND_RESET_Q(34);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__Vfuncout = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__wr_ptr = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__0__rd_ptr = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__Vfuncout = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__grey_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__6__bin_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__7__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__8__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__9__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__10__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__Vfuncout = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__wr_ptr = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__get_cnt__11__rd_ptr = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__Vfuncout = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__grey_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__grey2bin__17__bin_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__18__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__19__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__20__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_cmd_if__DOT__do_bin__21__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__wr_ptr = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__22__rd_ptr = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__grey_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__28__bin_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__29__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__30__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__31__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__32__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__wr_ptr = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__get_cnt__33__rd_ptr = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__grey_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__grey2bin__39__bin_8 = VL_RAND_RESET_I(9);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__40__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__41__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__42__grey = VL_RAND_RESET_I(3);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__Vfuncout = VL_RAND_RESET_I(2);
    __Vfunc_async_wb__DOT__u_resp_if__DOT__do_bin__43__grey = VL_RAND_RESET_I(3);
}
