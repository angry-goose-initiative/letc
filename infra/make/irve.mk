.PHONY: irve
irve:
	rm -rf ${REPO_ROOT}/build/irve
	mkdir -p ${REPO_ROOT}/build/irve
	cd ${REPO_ROOT}/build/irve && cmake -DCMAKE_BUILD_TYPE=Release ${REPO_ROOT}/verif/reference/irve
	${MAKE} -C ${REPO_ROOT}/build/irve irve
