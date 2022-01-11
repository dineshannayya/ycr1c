# src_dir := $(dir $(lastword $(MAKEFILE_LIST)))
rtl_src_dir := $(root_dir)/src/
rtl_core_files ?= core.files
rtl_top_files ?= ahb_top.files
rtl_tb_files ?= ahb_tb.files
rtl_inc_dir ?= $(root_dir)/src/includes
rtl_inc_tb_dir ?= $(root_dir)/tb/
top_module ?= ycr1_top_tb_ahb

rtl_core_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_core_files)))
rtl_top_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_top_files)))
rtl_tb_list := $(addprefix $(rtl_inc_tb_dir),$(shell cat $(rtl_inc_tb_dir)$(rtl_tb_files)))
model_list := $(addprefix $(rtl_inc_tb_dir),$(shell cat $(rtl_inc_tb_dir)$(rtl_tb_files)))
sv_list := $(rtl_core_list) $(rtl_top_list) $(rtl_tb_list)

ifeq ($(MAKECMDGOALS), $(filter $(MAKECMDGOALS),build_verilator build_verilator_wf))
ifeq ($(BUS),AHB)
export ycr1_wrapper  := $(root_dir)/sim/verilator_wrap/ycr1_ahb_wrapper.c
endif
ifeq ($(BUS),AXI)
export ycr1_wrapper  := $(root_dir)/sim/verilator_wrap/ycr1_axi_wrapper.c
endif
ifeq ($(BUS),WB)
export ycr1_wrapper  := $(root_dir)/sim/verilator_wrap/ycr1_wb_wrapper.c
endif
export verilator_ver ?= $(shell  expr `verilator --version | cut -f2 -d' '`)
endif

.PHONY: build_iverilog build_modelsim build_modelsim_wlf build_vcs build_ncsim build_verilator build_verilator_wf build_iverilog_wf

default: build_modelsim

build_iverilog: $(sv_list)
	cd $(bld_dir); \
	iverilog -g2012 \
	-I $(rtl_inc_dir) \
	-I $(rtl_inc_tb_dir) \
	-D $(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-o $(top_module).vvp

build_iverilog_wf: $(sv_list)
	cd $(bld_dir); \
	iverilog -g2012 \
	-I $(rtl_inc_dir) \
	-I $(rtl_inc_tb_dir) \
	-D $(SIM_CFG_DEF) \
	-D WFDUMP         \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-o $(top_module).vvp

build_modelsim: $(sv_list)
	cd $(bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O1 -mfcu -sv \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+nowarnSVCHK  \
	+define+YCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_modelsim_wlf: $(sv_list)
	cd $(bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O1 -mfcu -sv \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+nowarnSVCHK  \
	+define+YCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	+define+WFDUMP \
	$(SIM_BUILD_OPTS) \
	$(sv_list)
build_vcs: $(sv_list)
	cd $(bld_dir); \
	vcs \
	-full64 \
	-lca \
	-sverilog \
	-notice \
	+lint=all,noVCDE,noSVA-DIU,noSVA-CE,noSVA-NSVU \
	-timescale=1ns/1ps \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+define+YCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	-nc \
	-debug_all \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_ncsim: $(sv_list)
	cd $(bld_dir); \
	irun \
	-elaborate \
	-64bit \
	-disable_sem2009 \
	-verbose \
	-timescale 1ns/1ps \
	-incdir $(rtl_inc_dir) \
	-incdir $(rtl_inc_tb_dir) \
	-debug \
	+define+YCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-top $(top_module)

build_verilator: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	+1800-2017ext+sv \
	-Wno-fatal \
	--top-module $(top_module) \
	-DYCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	--clk clk \
	--exe $(ycr1_wrapper) \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;

build_verilator_wf: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	+1800-2017ext+sv \
	-Wno-fatal \
	--top-module $(top_module) \
	-DYCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	-CFLAGS -DVCD_TRACE -CFLAGS -DTRACE_LVLV=20 \
	-CFLAGS -DVCD_FNAME=simx.vcd \
	--clk clk \
	--exe $(ycr1_wrapper) \
	--trace \
	--trace-params \
    --trace-structs \
    --trace-underscore \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;


