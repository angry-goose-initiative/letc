/**
 * @file    unit_verilator_wrapper.cpp
 * @brief   Wrapper around unit-test testbenches to run with Verilator
 *
 * Partially based on the modifications that I made in my URA:
 * 
 * Copyright:
 *  Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
 *  Copyright (C) 2024 Nachiket Kapre
 *  Copyright (C) 2024 John Jekel
 * See the README.md file at the root of the repo for licensing info.
 *
 * Allows writing normal testbenches with Verilator 5's support for pound delays!
 *
 * Based on the old verif/nonuvm/verilator_wrapper.cpp from https://github.com/angry-goose-initiative/letc/tree/main
 *
 * The history of this file came full circle I guess!
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Includes and Defines
 * --------------------------------------------------------------------------------------------- */

#include <iostream>
#include <memory>

#include "verilated.h"
#include "verilated_fst_c.h"

#ifndef SV_TBENCH_NAME
#error "When compiling unit_verilator_wrapper.cpp, SV_TBENCH_NAME must be defined"
#endif

//String concatenation of header names within C++ itself doesn't quite work sadly,
//so we'll take care of it in the Verilator invocation instead.
//For consistency we'll do other string concatenation this way too.
#ifndef VERILATED_HEADER
#error "When compiling unit_verilator_wrapper.cpp, VERILATED_HEADER must be defined"
#endif
#define STRINGIZE_AUX(a) #a
#define STRINGIZE(a) STRINGIZE_AUX(a)
#include STRINGIZE(VERILATED_HEADER)

#ifndef VERILATED_CLASS
#error "When compiling unit_verilator_wrapper.cpp, SV_TBENCH_NAME must be defined"
#endif

/* ------------------------------------------------------------------------------------------------
 * Static Variables
 * --------------------------------------------------------------------------------------------- */

static double simulation_time = 0.0;//Used to keep track of simulation time for dumping a wave file

/* ------------------------------------------------------------------------------------------------
 * Function Declarations
 * --------------------------------------------------------------------------------------------- */

double sc_time_stamp();//Used by Verilator to keep track of simulation time dumping a wave file

/* ------------------------------------------------------------------------------------------------
 * Function Implementations
 * --------------------------------------------------------------------------------------------- */

int main(int argc, char** argv) {
    std::cout << "\x1b[1mSimulator binary for the \x1b[94m" << STRINGIZE(SV_TBENCH_NAME) <<
        "\x1b[0m\x1b[1m testbench has started...\x1b[0m" << std::endl;

#ifdef WAVES_OUTPUT_PATH
    std::cout << "\x1b[1mDumping waves to \x1b[94m" << STRINGIZE(WAVES_OUTPUT_PATH) << "\x1b[0m" << std::endl;
#endif

    //Interpret command line arguments for Verilator
    Verilated::commandArgs(argc, argv);

    //Instantiate the testbench for simulation
    std::unique_ptr<VERILATED_CLASS> testbench(new VERILATED_CLASS);

    //Needed to support dumping waves
#ifdef WAVES_OUTPUT_PATH
    Verilated::traceEverOn(true);
    std::unique_ptr<VerilatedFstC> tfp(new VerilatedFstC);
    testbench->trace(tfp.get(), 999);//Trace 999 levels of hierarchy
    tfp->open(STRINGIZE(WAVES_OUTPUT_PATH));
#endif

    //Simulation loop (until $finish)
    while (!Verilated::gotFinish()) {
        testbench->eval();//Update simulation
#ifdef WAVES_OUTPUT_PATH
        tfp->dump(simulation_time);//Dump wave file
#endif
        simulation_time += 1.0;//Increment time counter
    }

    std::cout << "\x1b[1mSimulator binary for the \x1b[94m" << STRINGIZE(SV_TBENCH_NAME) <<
        "\x1b[0m\x1b[1m testbench has finished...\x1b[0m" << std::endl;

    return 0;
}

double sc_time_stamp() {//Callback used by Verilator for dumping (it expects this symbol)
    return simulation_time;
}
