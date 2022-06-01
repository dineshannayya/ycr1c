// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "Vycr1_async_wbb__Syms.h"
#include "Vycr1_async_wbb.h"



// FUNCTIONS
Vycr1_async_wbb__Syms::~Vycr1_async_wbb__Syms()
{
}

Vycr1_async_wbb__Syms::Vycr1_async_wbb__Syms(VerilatedContext* contextp, Vycr1_async_wbb* topp, const char* namep)
    // Setup locals
    : VerilatedSyms{contextp}
    , __Vm_namep(namep)
    , __Vm_didInit(false)
    // Setup submodule names
{
    // Pointer to top level
    TOPp = topp;
    // Setup each module's pointers to their submodules
    // Setup each module's pointer back to symbol table (for public functions)
    TOPp->__Vconfigure(this, true);
    // Setup scopes
    __Vscope_async_wb__u_cmd_if.configure(this, name(), "async_wb.u_cmd_if", "u_cmd_if", -12, VerilatedScope::SCOPE_OTHER);
    __Vscope_async_wb__u_resp_if.configure(this, name(), "async_wb.u_resp_if", "u_resp_if", -12, VerilatedScope::SCOPE_OTHER);
}
