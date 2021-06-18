.SUFFIXES: .tex .pdf
.PHONY: celan
OUT=bat_vkr
REFERENCES=references.bib
BUILD=_build
XELATEX=xelatex -shell-escape -interaction=nonstopmode #-output-directory=$(BUILD)
MKDIR ?= mkdir
CP ?= cp 

#.PHONY: $(OUT).pdf
all: $(OUT).pdf #$(BUILD) $(BUILD)/$(REFERENCES) $(OUT).pdf

#$(BUILD):
#	$(MKDIR) $(BUILD)

#$(BUILD)/$(REFERENCES): $(REFERENCES)
#	$(CP) $(REFERENCES) $@

define WRAP
INPUT_$(1)=$(wildcard $(1)*.tex)
#.PHONY: $(1).pdf

#$(1).pdf: $$(INPUT_$(1):%.tex=%.pdf)
$$(INPUT_$(1):%.tex=%.pdf): $$(INPUT_$(1)) heading.tex
	$$(XELATEX) $$<
	#TEXMFOUTPUT="./_build:" bibtex $(1)
	#cp $(REFERENCES) _build/ && cd _build && bibtex $(1)
	#bibtex $(1)
	$$(XELATEX) $$<
endef

LECTURES=pipeline $(OUT)

$(foreach i,$(LECTURES),$(eval $(call WRAP,$(i)) ) )

$(OUT).pdf: pipeline.pdf 02selectives.tex 03conversion.tex 05impl.tex graph.pdf

graph.pdf: graph.tex 
	xelatex $< -o 

graph.tex: test.dot 
	 dot2tex --prog=neato -ftikz test.dot > graph.tex

celan: clean
clean:
	@$(RM) -r _minted* $(BUILD) pipeline.pdf
	@$(RM) *.aux *.log *.nav *.out *.snm *.toc *.vrb *.synctex.gz *.bbl *.blg

