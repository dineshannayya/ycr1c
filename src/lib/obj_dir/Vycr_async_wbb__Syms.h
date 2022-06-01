// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VYCR1_ASYNC_WBB__SYMS_H_
#define VERILATED_VYCR1_ASYNC_WBB__SYMS_H_  // guard

#include "verilated_heavy.h"

// INCLUDE MODULE CLASSES
#include "Vycr1_async_wbb.h"

// SYMS CLASS
class Vycr1_async_wbb__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    Vycr1_async_wbb*               TOPp;
    
    // SCOPE NAMES
    VerilatedScope __Vscope_async_wb__u_cmd_if;
    VerilatedScope __Vscope_async_wb__u_resp_if;
    
    // CREATORS
    Vycr1_async_wbb__Syms(VerilatedContext* contextp, Vycr1_async_wbb* topp, const char* namep);
    ~Vycr1_async_wbb__Syms();
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
