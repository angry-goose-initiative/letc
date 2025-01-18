#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#open_vcd xsim_waves.vcd
#log_vcd -level 0 *
log_wave -recursive *
run all
#flush_vcd
#close_vcd
exit
