.PHONY: unit_regression
unit_regression:
	${BASH} ${INFRA_DIR}/scripts/unit_regression.sh

.PHONY: unit_regression_par
unit_regression_par:
	${BASH} ${INFRA_DIR}/scripts/unit_regression.sh 1

.PHONY: synth_regression
synth_regression:
	${BASH} ${INFRA_DIR}/scripts/synth_regression.sh

.PHONY: synth_regression_par
synth_regression_par:
	${BASH} ${INFRA_DIR}/scripts/synth_regression.sh 1

.PHONY: stubmss_regression
stubmss_regression:
	${BASH} ${INFRA_DIR}/scripts/stubmss_regression.sh

.PHONY: stubmss_regression_par
stubmss_regression_par:
	${BASH} ${INFRA_DIR}/scripts/stubmss_regression.sh 1

#TODO others in the future
