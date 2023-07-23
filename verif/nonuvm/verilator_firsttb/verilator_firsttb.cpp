/**
 * @file    verilator_firstb.cpp
 * @brief   TODO
 * 
 * @copyright Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO longer description
 *
 * Based on the one from vgacpu
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Includes
 * --------------------------------------------------------------------------------------------- */

#include <cstdint>
#include <memory>
#include "verilated.h"

//The header that will be generated by verilator
#include "Vverilator_firsttb.h"

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

/* Function Implementations */

int main(int argc, char** argv) {
    //Initialization for verilator
    Verilated::commandArgs(argc, argv);//Interpret command line arguments for Verilator
    std::unique_ptr<Vverilator_firsttb> testbench(new Vverilator_firsttb);//Instantiate the verilator_firsttb module for simulation
    Verilated::traceEverOn(true);//Needed to support dumping

    //Simulation loop (until $finish)
    while (!Verilated::gotFinish()) {
        testbench->eval();//Update simulation
        simulation_time += 1.0;//Increment time counter
    }

    return 0;
}

double sc_time_stamp() {//Callback used by Verilator for dumping (it expects this symbol)
    return simulation_time;
}
