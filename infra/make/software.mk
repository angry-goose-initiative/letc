.PHONY: software
software:
	rm -rf ${REPO_ROOT}/build/software
	mkdir -p ${REPO_ROOT}/build/software
	cd ${REPO_ROOT}/build/software && cmake ${REPO_ROOT}/verif/software
	${MAKE} -C ${REPO_ROOT}/build/software

.PHONY: optimized_software
optimized_software:
	rm -rf ${REPO_ROOT}/build/optimized_software
	mkdir -p ${REPO_ROOT}/build/optimized_software
	cd ${REPO_ROOT}/build/optimized_software && cmake -DCMAKE_BUILD_TYPE=Release ${REPO_ROOT}/verif/software
	${MAKE} -C ${REPO_ROOT}/build/optimized_software
