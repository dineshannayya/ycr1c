# SPDX-FileCopyrightText: 2020 Efabless Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# SPDX-License-Identifier: Apache-2.0

set script_dir [file dirname [file normalize [info script]]]

set ::env(ROUTING_CORES) "6"

set ::env(DESIGN_NAME) ycr_intf
set ::env(DESIGN_IS_CORE) "0"
set ::env(FP_PDN_CORE_RING) "0"

# Timing configuration
set ::env(CLOCK_PERIOD) "10"
set ::env(CLOCK_PORT) "wb_clk core_clk rtc_clk"

set ::env(SYNTH_MAX_FANOUT) 4

## CTS BUFFER
set ::env(CTS_CLK_BUFFER_LIST) "sky130_fd_sc_hd__clkbuf_4 sky130_fd_sc_hd__clkbuf_8"
set ::env(CTS_SINK_CLUSTERING_SIZE) "16"
set ::env(CLOCK_BUFFER_FANOUT) "8"
set ::env(LEC_ENABLE) 0

set ::env(VERILOG_FILES) "\
        $script_dir/../../src/lib/clk_skew_adjust.gv                   \
	$script_dir/../../src/top/ycr_dmem_router.sv                  \
	$script_dir/../../src/top/ycr_imem_router.sv                  \
	$script_dir/../../src/top/ycr_icache_router.sv                \
	$script_dir/../../src/top/ycr_dcache_router.sv                \
	$script_dir/../../src/top/ycr_tcm.sv                          \
	$script_dir/../../src/top/ycr_timer.sv                        \
	$script_dir/../../src/top/ycr_top_wb.sv                       \
	$script_dir/../../src/top/ycr_dmem_wb.sv                      \
	$script_dir/../../src/top/ycr_imem_wb.sv                      \
	$script_dir/../../src/top/ycr_intf.sv                         \
        $script_dir/../../src/cache/src/core/icache_top.sv             \
        $script_dir/../../src/cache/src/core/icache_app_fsm.sv         \
        $script_dir/../../src/cache/src/core/icache_tag_fifo.sv        \
        $script_dir/../../src/cache/src/core/dcache_tag_fifo.sv        \
        $script_dir/../../src/cache/src/core/dcache_top.sv             \
        $script_dir/../../src/lib/ycr_async_wbb.sv                    \
        $script_dir/../../src/lib/ycr_arb.sv                          \
        $script_dir/../../src/lib/sync_fifo.sv                         \
        $script_dir/../../src/lib/async_fifo.sv                        \
        $script_dir/../../src/lib/ctech_cells.sv                       \
	$script_dir/../../src/core/primitives/ycr_reset_cells.sv      \
	"
set ::env(VERILOG_INCLUDE_DIRS) [glob $script_dir/../../src/includes ]


set ::env(SDC_FILE) "$script_dir/base.sdc"
set ::env(BASE_SDC_FILE) "$script_dir/base.sdc"

set ::env(LEC_ENABLE) 0

set ::env(VDD_PIN) [list {vccd1}]
set ::env(GND_PIN) [list {vssd1}]

## Floorplan
set ::env(FP_PIN_ORDER_CFG) $script_dir/pin_order.cfg
set ::env(FP_SIZING) absolute
set ::env(DIE_AREA) "0 0 825 700 "

set ::env(MACRO_PLACEMENT_CFG) $script_dir/macro_placement.cfg
set ::env(PL_TARGET_DENSITY) 0.36


set ::env(GLB_RT_MAXLAYER) 5
set ::env(GLB_RT_MAX_DIODE_INS_ITERS) 10
set ::env(DIODE_INSERTION_STRATEGY) 4


set ::env(QUIT_ON_TIMING_VIOLATIONS) "0"
set ::env(QUIT_ON_MAGIC_DRC) "1"
set ::env(QUIT_ON_LVS_ERROR) "0"
set ::env(QUIT_ON_SLEW_VIOLATIONS) "0"

#Need to cross-check why global timing opimization creating setup vio with hugh hold fix
set ::env(GLB_RESIZER_TIMING_OPTIMIZATIONS) "0"

