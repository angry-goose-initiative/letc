# generate_ip.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# TCL script to generate IP
#

####################################################################################################
# Setup
####################################################################################################

set IP      [lindex $argv 0]
set IP_PATH [lindex $argv 1]
set OUTPUT_DIR ./
file mkdir $OUTPUT_DIR

####################################################################################################
# TODO
####################################################################################################

create_project -in_memory -part xc7z007sclg400-1
set_property BOARD_PART digilentinc.com:cora-z7-07s:part0:1.1 [current_project]
read_ip $IP_PATH
generate_target all [get_ips $IP]
