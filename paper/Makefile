.PHONY: all paper
all: paper
paper:
	latexmk -pdf -outdir=build -interaction=nonstopmode -halt-on-error main.tex
	cp build/main.pdf main.pdf
