CXXFLAGS= -O3 -I minisat -fPIC -fpermissive -Wno-literal-suffix -Wno-unused-result -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS #-pg

OFLAGS= #-inline 0 -p
OCAMLOPT=ocamlopt
OCAMLC=ocamlc
OINCL=-I bin -I bin/extra -I bin/pfterm -I bin/coqparser -I bin/parser -I +nums

OFILES:=extra/StringE log preterm term syntax atom config foform eproverstate error extra/OptionE flags minisatinterface refut minisat models ontology priorityqueue searchoption termP unsatcore state coqparser/coqparser coqparser/coqlexer fomapping lfthform lfthmapping match patternclause search eprover extra/FileE extra/ListE parser/formula parser/tptp_config parser/tptp_parser parser/tptp_lexer pfterm/flag pfterm/refutation pfterm/branch pfterm/coq pfterm/latex pfterm/litcount pfterm/norm pfterm/step pfterm/suche pfterm/translation pfterm/proofterm sine version satallaxmain satallax
CFILES:=Ointerface.o SimpSolver.o Solver.o

BINFILES=$(addprefix bin/,$(addsuffix .cmx,$(OFILES)) $(CFILES))

satallax: bin $(BINFILES)
	$(OCAMLOPT) -cc g++ $(OFLAGS) $(OINCL) nums.cmxa str.cmxa unix.cmxa $(BINFILES) -o $@

bin/%.cmx: src/%.ml Makefile
	$(OCAMLOPT) $(OFLAGS) $(OINCL) -o $@ -c $<

bin/%.cmo: src/%.ml Makefile
	$(OCAMLC) $(OINCL) -o $@ -c $<

bin/%.cmi: src/%.mli Makefile
	$(OCAMLC) $(OINCL) -o $@ -c $<

%.ml: %.mly
	ocamlyacc $<
	rm $(<:y=i)

%lexer.ml: %lexer.mll %parser.ml
	ocamllex $<

bin/%.o: src/minisat-interface/%.cc Makefile
	g++ $(CXXFLAGS) -c $<
	@mv *.o bin

bin:
	@mkdir -p bin/extra bin/parser bin/pfterm bin/coqparser

.depend: src/*mli src/*ml src/extra/*ml src/pfterm/*mli src/pfterm/*ml src/parser/*mli src/parser/*ml src/coqparser/coqparser.ml src/coqparser/coqlexer.ml src/parser/*mli src/parser/*ml src/parser/tptp_parser.ml src/parser/tptp_lexer.ml
	ocamldep -I src -I src/extra -I src/pfterm -I src/pfterm -I src/coqparser -I src/parser $^ | sed "s/src\//bin\//g" > .depend

clean:
	rm -rf bin *.o *.cmx *.cmi *.cma *.cmo *.cmxa *.a *.so *~ *annot gmon.out ocamlprof.dump .depend satallax

.INTERMEDIATE: src/coqparser/coqparser.ml src/coqparser/coqlexer.ml src/parser/tptp_parser.ml src/parser/tptp_lexer.ml

include .depend
