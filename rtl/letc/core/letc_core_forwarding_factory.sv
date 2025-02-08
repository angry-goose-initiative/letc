/*
 * File:    letc_core_forwarding_factory.sv
 * Brief:   Combinational logic for forwarding data
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module letc_core_forwarding_factory
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    letc_core_forwardee_if.fwd_factory  e_forwardee_rs1,
    letc_core_forwardee_if.fwd_factory  e_forwardee_rs2,
    letc_core_forwardee_if.fwd_factory m1_forwardee_rs2,
    letc_core_forwardee_if.fwd_factory m2_forwardee_rs2,

    letc_core_forwarder_if.fwd_factory m1_forwarder,
    letc_core_forwarder_if.fwd_factory m2_forwarder,
    letc_core_forwarder_if.fwd_factory  w_forwarder,

    output logic  e_unforwardable_hazard,
    output logic m1_unforwardable_hazard,
    output logic m2_unforwardable_hazard
);

`define may_fwd(forwardee, forwarder)                                         \
    (forwardee.reg_idx == forwarder.rd_idx && forwarder.instr_produces_rd)

`define is_hazard(forwardee, forwarder)                                       \
    (!forwarder.rd_val_avail && forwardee.stage_uses_reg)

`define close_fwd(unforwardable_hazard, forwardee, forwarder)                 \
    if (`may_fwd(forwardee, forwarder)) begin                                 \
        forwardee.use_fwd = 1'b1;                                             \
        forwardee.fwd_val = forwarder.rd_val;                                 \
        unforwardable_hazard = `is_hazard(forwardee, forwarder);              \
    end

`define later_fwd(unforwardable_hazard, forwardee, forwarder)                 \
    else if (`may_fwd(forwardee, forwarder)) begin                            \
        forwardee.use_fwd = 1'b1;                                             \
        forwardee.fwd_val = forwarder.rd_val;                                 \
        unforwardable_hazard = `is_hazard(forwardee, forwarder);              \
    end

`define concl_fwd(unforwardable_hazard, forwardee)                            \
    else begin                                                                \
        forwardee.use_fwd = 1'b0;                                             \
        forwardee.fwd_val = 32'hDEADBEEF;                                     \
        unforwardable_hazard = 1'b0;                                          \
    end

logic e_unforwardable_hazard_rs1;
logic e_unforwardable_hazard_rs2;

always_comb begin
    // Execute forwardee
    `close_fwd(e_unforwardable_hazard_rs1, e_forwardee_rs1, m1_forwarder)
    `later_fwd(e_unforwardable_hazard_rs1, e_forwardee_rs1, m2_forwarder)
    `later_fwd(e_unforwardable_hazard_rs1, e_forwardee_rs1, w_forwarder)
    `concl_fwd(e_unforwardable_hazard_rs1, e_forwardee_rs1)

    `close_fwd(e_unforwardable_hazard_rs2, e_forwardee_rs2, m1_forwarder)
    `later_fwd(e_unforwardable_hazard_rs2, e_forwardee_rs2, m2_forwarder)
    `later_fwd(e_unforwardable_hazard_rs2, e_forwardee_rs2, w_forwarder)
    `concl_fwd(e_unforwardable_hazard_rs2, e_forwardee_rs2)

    e_unforwardable_hazard = e_unforwardable_hazard_rs1
                             || e_unforwardable_hazard_rs2;

    // Memory 1 forwardee
    `close_fwd(m1_unforwardable_hazard, m1_forwardee_rs2, m2_forwarder)
    `later_fwd(m1_unforwardable_hazard, m1_forwardee_rs2, w_forwarder)
    `concl_fwd(m1_unforwardable_hazard, m1_forwardee_rs2)

    // Memory 2 forwardee
    `close_fwd(m2_unforwardable_hazard, m2_forwardee_rs2, w_forwarder)
    `concl_fwd(m2_unforwardable_hazard, m2_forwardee_rs2)
end

endmodule : letc_core_forwarding_factory
