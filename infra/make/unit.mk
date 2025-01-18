.PHONY: unit_iverilog
unit_iverilog: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/unit_iverilog.sh ${TARGET} ${WAVES}

.PHONY: unit_verilator
unit_verilator: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/unit_verilator.sh ${TARGET} ${WAVES} 

.PHONY: unit_sv2v_verilator
unit_sv2v_verilator: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/unit_verilator.sh ${TARGET} ${WAVES} 1

.PHONY: unit_xsim
unit_xsim: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/unit_xsim.sh ${TARGET} ${WAVES}
