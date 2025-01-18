.PHONY: synth_vivado_ooc
synth_vivado_ooc: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/synth_vivado_ooc.sh ${TARGET}

.PHONY: synth_yosys
synth_yosys: ${TARGET} ${FILELIST}
	${BASH} ${INFRA_DIR}/scripts/synth_yosys.sh ${TARGET}
