.PHONY: regression
regression:
	${BASH} ${INFRA_DIR}/scripts/regression.sh

.PHONY: regression_parallel
regression_parallel:
	${BASH} ${INFRA_DIR}/scripts/regression.sh 1
