# Thanks https://itsembedded.com/dhd/vivado_sim_1/
# https://support.xilinx.com/s/article/53351?language=en_US
open_vcd xsim_waves.vcd
log_vcd -level 999 [get_object *]
log_wave -recursive *
run all
close_vcd
exit
