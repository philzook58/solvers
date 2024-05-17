BUILD=_build
TARG=bin/NaTT
TARG_OPT=bin/NaTT.exe
PACKS=unix,str,re,ocamlgraph,xml-light
OCAMLC=ocamlfind ocamlc -package $(PACKS) -linkpkg -I $(BUILD) -g -w -8
OCAMLOPT=ocamlfind ocamlopt -package $(PACKS) -linkpkg -I $(BUILD) -g -w -8
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc -html -d htdocs -t "Termination Tool" -I $(BUILD)

# The list of ocaml source files
OCAML_SRCS=\
	io.ml \
	util.ml \
	txtr.ml \
	myXML.ml \
	matrix.ml \
	proc.ml \
	smt.ml \
	strategy.ml \
	preorder.ml \
	mset.ml \
	abbrev.ml \
	sym.ml \
	term.ml \
	params.ml \
	subst.ml \
	trs.ml \
	estimator.ml \
	dp.ml \
	freezing.ml \
	weight.ml \
	wpo_info.ml \
	wpo_printer.ml \
	wpo.ml \
	nonterm.ml \
	main.ml

OCAML_MLS=$(OCAML_SRCS)

OCAML_CMOS=$(OCAML_MLS:%.ml=$(BUILD)/%.cmo)

OCAML_CMXS=$(OCAML_MLS:%.ml=$(BUILD)/%.cmx)

## If you need a statically linked binary
#OCAMLFLAGS= -cclib '-static'

#OCAMLFLAGS+= -g

all: $(TARG_OPT)

install: all
	cp -f $(TARG_OPT) xtc2tpdb.xml /usr/local/bin/

$(BUILD):
	mkdir $(BUILD)

$(TARG_OPT): $(OCAML_CMXS)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) $^

$(TARG): $(OCAML_CMOS)
	$(OCAMLC) -o $@ $(OCAMLFLAGS) $^

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

$(BUILD)/%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -o $@ -c $<

$(BUILD)/%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -o $@ -c $<

$(BUILD)/%.cmx: %.ml $(BUILD)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ -c $<

# Clean up
clean:
	rm -f $(TARG) $(TARG_OPT) $(BUILD) .depend

# Consistency test
test: $(TARG_OPT)
	TOOL="$(PWD)/bin/NaTT.sh -V"; \
	BENCH="$(PWD)/tpdb_info/nonterm.list"; \
	cd ../TPDB/TRS_Standard; \
	if [ -e tmp_result ]; then rm tmp_result; fi; \
	while read f; do \
		$$TOOL $$f | tee -a tmp_result; \
		if grep -q YES tmp_result; then echo WRONG!; exit 1; fi;\
	done < $$BENCH; \
	grep -c NO tmp_result; \
	rm tmp_result



# Dependencies
.depend: $(OCAML_MLS)
	$(OCAMLDEP) *.mli *.ml | sed -E 's~(^[ \t]*)([A-Za-z])~\1$(BUILD)/\2~' > .depend

-include .depend
