.PHONY: svlint
svlint:
	${BASH} ${INFRA_DIR}/scripts/svlint.sh

.PHONY: verible
verible:
	${BASH} ${INFRA_DIR}/scripts/verible.sh
