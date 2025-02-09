# LETC

The Little Engine That Could (Run Linux) :)

[![LETC Lint](https://github.com/angry-goose-initiative/letc/actions/workflows/lint.yml/badge.svg)](https://github.com/angry-goose-initiative/letc/actions/workflows/lint.yml)
[![LETC Unit Regression](https://github.com/angry-goose-initiative/letc/actions/workflows/unit.yml/badge.svg)](https://github.com/angry-goose-initiative/letc/actions/workflows/unit.yml)
[![LETC Synth Regression](https://github.com/angry-goose-initiative/letc/actions/workflows/synth.yml/badge.svg)](https://github.com/angry-goose-initiative/letc/actions/workflows/synth.yml)
[![LETC stubmss Regression](https://github.com/angry-goose-initiative/letc/actions/workflows/stubmss.yml/badge.svg)](https://github.com/angry-goose-initiative/letc/actions/workflows/stubmss.yml)

## Lore

LETC is the last step on our journey within the Angry Goose Initiative.

It is a 7-stage in-order pipelined RISC-V soft-core design, targeting the Cora Z7 devboard containing a Zync 7000 FPGA.

It will have TLBs, caches, a hardware page table walker, and will accesses peripherals and memory over an AXI interconnect of our own making!

If you're reading this, as of writing we're in a transition period between wrapping up IRVE, our C++ reference implementation, and beginning LETC. Exciting stuff!

**For more details, and an overarching view of LETC's Architecture, [visit this page](https://github.com/angry-goose-initiative/wiki/wiki/LETC-Architecture-Overview)**.

EEI information (ie. the standards LETC implements) can be found [here](https://github.com/angry-goose-initiative/wiki/wiki/General-EEI-Info).

LETC is in part based on [IRVE](https://github.com/angry-goose-initiative/irve), [JZJCoreF](https://git.jekel.ca/JZJ/jzjcoref), and [JZJPipelinedCoreC](https://git.jekel.ca/JZJ/jzjpipelinedcorec).

## Okay enough backstory, I want to try this out!

Awesome!

If you want to simulate LETC, check out [this wiki page](https://github.com/angry-goose-initiative/wiki/wiki/Simulating-LETC).

If you want to synthesize LETC, or program it onto your own devboard, [this is the page for you](https://github.com/angry-goose-initiative/wiki/wiki/Synthesizing-LETC)!

Want to run Linux on the thing? Check [this out](https://github.com/angry-goose-initiative/wiki/wiki/Linux-shenanigans).

[Need help navigating the directory structure](https://github.com/angry-goose-initiative/wiki/wiki/Directory-Structure#letc)?
