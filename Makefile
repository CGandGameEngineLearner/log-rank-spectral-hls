.PHONY: all paper arxiv verify-python verify-lean clean-status

all: verify-python verify-lean paper

paper:
	bash scripts/build_paper.sh

arxiv: paper
	@echo "arXiv source: output/arxiv/log-rank-spectral-hls-arxiv.tar.gz"

verify-python:
	bash scripts/run_verifiers.sh

verify-lean:
	cd formal && lake build

clean-status:
	git status --short
