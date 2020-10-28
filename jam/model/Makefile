B=build
_=$(shell mkdir -p $(B))

all : formal.pdf

$(B)/trace-language.pdf $(B)/trace-judgment.pdf $(B)/trace-exprim.pdf : trace.rkt
	raco test --submodule render ++arg $(B) trace.rkt

%-crop.pdf : %.pdf
	pdfcrop $< $@

$B/formal.pdf : formal.tex $(B)/trace-language-crop.pdf $(B)/trace-judgment-crop.pdf $(B)/trace-exprim-crop.pdf
# run pdflatex from $(B) instead of using pdflatex -output-dir=$(B),
# which appears to mess up includegraphics path search
	cd $(B) && pdflatex ../formal.tex

formal.pdf : $B/formal.pdf
	cp $< $@

