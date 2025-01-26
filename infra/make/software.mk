.PHONY: software
software:
	rm -rf ${REPO_ROOT}/build/software
	mkdir -p ${REPO_ROOT}/build/software
	cd ${REPO_ROOT}/build/software && cmake ${REPO_ROOT}/verif/software
	${MAKE} -C ${REPO_ROOT}/build/software
