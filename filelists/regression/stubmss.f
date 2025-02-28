/* vi: set filetype=c: */
#pragma once

///////////////////////////////////////////////////////////////////////////////////////////////////
// Assembly Test Programs
///////////////////////////////////////////////////////////////////////////////////////////////////

//JZJCoreSoftware test programs
build/software/rvsw/src/single_file/asm/jzjcoresoftware/adding2.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/auipctest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/bneandsubtest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/callrettest.vhex8
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/fenceecalltest.vhex8//Not yet supported
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/fibbonaccijal.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/fibbonaccijalr.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/lbutest.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/lhtest.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/lhutest.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/loadbytetest.vhex8//Infinite loop
build/software/rvsw/src/single_file/asm/jzjcoresoftware/luitest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/memoryreadtest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/memorywritetest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/nop.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/sbtest.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/sbtest2.vhex8
build/software/rvsw/src/single_file/asm/jzjcoresoftware/shtest.vhex8
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/sllisrliblttest.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/sllsrlblttest.vhex8//Infinite loop
build/software/rvsw/src/single_file/asm/jzjcoresoftware/testingfunctions.vhex8
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/uncondjumptest.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/uncondjumptest2.vhex8//Infinite loop
//build/software/rvsw/src/single_file/asm/jzjcoresoftware/xoritoggle.vhex8//Infinite loop

//letc_base_spec test programs
build/software/rvsw/src/single_file/asm/letc_base_spec/first_loads.vhex8
build/software/rvsw/src/single_file/asm/letc_base_spec/lb.vhex8
build/software/rvsw/src/single_file/asm/letc_base_spec/lw.vhex8
build/software/rvsw/src/single_file/asm/letc_base_spec/lh.vhex8

//letc_pre_hazard test programs
build/software/rvsw/src/single_file/asm/letc_pre_hazard/all_loads.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/all_loads_and_stores.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/c_deadlock.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/c_deadlock_simplified.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/dependency_problem_0.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/first_branch_test.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/forwarding_sweep.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/increment.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/jumping_around.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/store_address_mismatch.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/store_to_load.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/store_to_load_aftermath.vhex8
build/software/rvsw/src/single_file/asm/letc_pre_hazard/use_after_load.vhex8

//Misc ASM test programs
//build/software/rvsw/src/single_file/asm/atomics.vhex8//Not yet supported
//build/software/rvsw/src/single_file/asm/privilege_levels.vhex8//Not yet supported
build/software/rvsw/src/single_file/asm/rv32esim.vhex8
//build/software/rvsw/src/single_file/asm/user_and_back_in_time_for_dinner.vhex8//Not yet supported

///////////////////////////////////////////////////////////////////////////////////////////////////
// C Test Programs
///////////////////////////////////////////////////////////////////////////////////////////////////

//build/software/rvsw/src/single_file/c/hello_exceptions.vhex8//Not yet supported
build/software/rvsw/src/single_file/c/hello_world.vhex8
//build/software/rvsw/src/single_file/c/illegal_instruction_experiments.vhex8//Not yet supported
//build/software/rvsw/src/single_file/c/irve_csr_bringup.vhex8//Not yet supported
build/software/rvsw/src/single_file/c/irve_debugging_puts_weirdness.vhex8
//build/software/rvsw/src/single_file/c/irve_exception_bringup.vhex8//Not yet supported
build/software/rvsw/src/single_file/c/irve_stress_test.vhex8
//build/software/rvsw/src/single_file/c/nommulinux.vhex8//Does not fit into the regression well since it depends on a kernel
//build/software/rvsw/src/single_file/c/nouveau_stress_test.vhex8//WAY too slow
//build/software/rvsw/src/single_file/c/poll_timer.vhex8//Not yet supported
//build/software/rvsw/src/single_file/c/poll_timer_interrupt_mmode.vhex8//Not yet supported
//build/software/rvsw/src/single_file/c/poll_timer_interrupt_smode.vhex8//Not yet supported
build/software/rvsw/src/single_file/c/rv32esim.vhex8
build/software/rvsw/src/single_file/c/rv32im_sanity.vhex8
//build/software/rvsw/src/single_file/c/software_floating_point_fun.vhex8//WAY too slow
//build/software/rvsw/src/single_file/c/timer_interrupt_mmode.vhex8
//build/software/rvsw/src/single_file/c/timer_interrupt_smode.vhex8

///////////////////////////////////////////////////////////////////////////////////////////////////
// C Test Programs
///////////////////////////////////////////////////////////////////////////////////////////////////

//TODO
