.PHONY: clean
clean:
	rm -rf build

.PHONY: ctags
ctags:
	${BASH} ${INFRA_DIR}/scripts/ctags.sh
