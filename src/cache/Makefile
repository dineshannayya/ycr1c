# //////////////////////////////////////////////////////////////////////////////
# // SPDX-FileCopyrightText: 2021, Dinesh Annayya
# // 
# // Licensed under the Apache License, Version 2.0 (the "License");
# // you may not use this file except in compliance with the License.
# // You may obtain a copy of the License at
# //
# //      http://www.apache.org/licenses/LICENSE-2.0
# //
# // Unless required by applicable law or agreed to in writing, software
# // distributed under the License is distributed on an "AS IS" BASIS,
# // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# // See the License for the specific language governing permissions and
# // limitations under the License.
# // SPDX-License-Identifier: Apache-2.0
# // SPDX-FileContributor: Dinesh Annayya <dinesha@opencores.org>
# // //////////////////////////////////////////////////////////////////////////
#------------------------------------------------------------------------------
# Makefile for Simulation and Synthesis
#------------------------------------------------------------------------------

# Paths
export ROOT_DIR := $(shell pwd)

## Simulation mode: RTL/GL
SIM?=RTL
DUMP?=OFF

# Targets
.PHONY: clean dcache icache synth help

PATTERNS = dcache icache 

default: icache

$(PATTERNS): 
	cd tb && export SIM=${SIM} DUMP=${DUMP} && $(MAKE) $@

synth:
	cd ./synth && $(MAKE) synth

help:
	@echo "To run RTL  simulation: make dcache SIM=RTL"
	@echo "To run RTL  simulation: make icache SIM=RTL"
	@echo "To run RTL  simulation: make dcache SIM=RTL DUMP=ON"
	@echo "To run RTL  simulation: make icache SIM=RTL DUMP=ON"
	@echo "To run RTL  simulation: make dcache SIM=GL"
	@echo "To run RTL  simulation: make icache SIM=GL"
	@echo "To run synthesis: make synth"
	@echo "Note: Before running gate sim make sure that you have completed synthesis"




clean:
	cd tb && $(MAKE) clean && cd ../synth && $(MAKE) clean 
