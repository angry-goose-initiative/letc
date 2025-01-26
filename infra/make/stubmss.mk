.PHONY: stubmss_build
stubmss_build:
	${BASH} ${INFRA_DIR}/scripts/stubmss_build.sh

.PHONY: stubmss_run
stubmss_run:
	${BASH} ${INFRA_DIR}/scripts/stubmss_run.sh ${PROGRAM} ${WAVES} 

