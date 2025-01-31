/* vi: set filetype=c: */
#pragma once
#include "rtl/common/axi/axi_if.f"
#include "rtl/common/riscv_pkg.f"
#include "rtl/letc/letc_pkg.f"
#include "rtl/letc/core/letc_core_pkg.f"
#include "rtl/letc/core/letc_core_adhesive.f"
#include "rtl/letc/core/letc_core_csrf.f"
#ifndef STUB_MSS
#include "rtl/letc/core/letc_core_dmss.f"
#else
#include "verif/stubmss/letc_core_dmss.f"
#endif
#include "rtl/letc/core/letc_core_dmss_if.f"
#include "rtl/letc/core/letc_core_forwardee_if.f"
#include "rtl/letc/core/letc_core_forwarder_if.f"
#ifndef STUB_MSS
#include "rtl/letc/core/letc_core_imss.f"
#else
#include "verif/stubmss/letc_core_imss.f"
#endif
#include "rtl/letc/core/letc_core_imss_if.f"
#include "rtl/letc/core/letc_core_rf.f"
#include "rtl/letc/core/letc_core_stage_fetch1.f"
#include "rtl/letc/core/letc_core_stage_fetch2.f"
#include "rtl/letc/core/letc_core_stage_decode.f"
#include "rtl/letc/core/letc_core_stage_execute.f"
#include "rtl/letc/core/letc_core_stage_memory.f"
//#include "rtl/letc/core/letc_core_stage_writeback.f"
rtl/letc/core/letc_core_top.sv
