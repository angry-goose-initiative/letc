.PHONY: stubmss_build
stubmss_build:
	${BASH} ${INFRA_DIR}/scripts/stubmss_build.sh

.PHONY: stubmss_run
stubmss_run:
	${BASH} ${INFRA_DIR}/scripts/stubmss_run.sh ${PROGRAM} ${WAVES} 

.PHONY: stubmss_check
stubmss_check:
	${BASH} ${INFRA_DIR}/scripts/stubmss_check.sh ${PROGRAM} ${WAVES} 
