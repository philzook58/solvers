CFLAGS=-O3 -I minisat -fPIC -DCACHE_SUBST #-pg
# -coverage -fprofile-generate # GCC
# -fprofile-instr-generate -fcoverage-mapping # CLANG
# -fprofile-use
CXXFLAGS=$(CFLAGS) -fpermissive -Wno-literal-suffix -Wno-unused-result -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS
#OFLAGS= -inline 0 -p
LFLAGS= -ccopt -static
#LLIBS=/usr/lib/gcc/x86_64-linux-gnu/11/libgcov.a
CC=gcc #clang-13
CPP=g++ #clang-13++
OCAMLOPT=ocamlopt
OCAMLC=ocamlc
OINCL=-I bin -I bin/extra -I bin/pfterm -I bin/coqparser -I bin/parser

OFILES:=extra/StringE log preterm ftm vector term syntax atom config error extra/OptionE flags minisatinterface refut minisat ontology searchoption termP unsatcore state coqparser/coqparser coqparser/coqlexer search extra/FileE extra/ListE parser/formula parser/tptp_config parser/tptp_parser parser/tptp_lexer pfterm/flag pfterm/refutation pfterm/branch pfterm/coq pfterm/latex pfterm/litcount pfterm/norm pfterm/step pfterm/suche pfterm/translation pfterm/proofterm sine version lashmain lash
CFILES:=minisat_stub.o Solver.o ftm_stub.o prioqueue_stub.o

BINFILES=$(addprefix bin/,$(addsuffix .cmx,$(OFILES)) $(CFILES))

lash: bin $(BINFILES)
	$(OCAMLOPT) -cc g++ $(LFLAGS) $(OFLAGS) $(OINCL) str.cmxa unix.cmxa $(BINFILES) $(LLIBS) -o $@

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

bin/%.o: src/c/%.cc Makefile
	g++ $(CXXFLAGS) -c $<
	@mv *.o bin

bin/%.o: src/c/%.c Makefile
	gcc $(CFLAGS) -c $<
	@mv *.o bin

bin:
	@mkdir -p bin/extra bin/parser bin/pfterm bin/coqparser

.depend: src/*mli src/*ml src/extra/*ml src/pfterm/*mli src/pfterm/*ml src/parser/*mli src/parser/*ml src/coqparser/coqparser.ml src/coqparser/coqlexer.ml src/parser/*mli src/parser/*ml src/parser/tptp_parser.ml src/parser/tptp_lexer.ml
	ocamldep -I src -I src/extra -I src/pfterm -I src/pfterm -I src/coqparser -I src/parser $^ | sed "s/src\//bin\//g" > .depend

clean:
	rm -rf bin .depend lash
	rm -rf *.o *.cmx *.cmi *.cma *.cmo *.cmxa *.a *.so *annot *.gcda *.gcno gmon.out ocamlprof.dump default.profdata default.profraw
	find . -name \*~  | xargs rm -f

.INTERMEDIATE: src/coqparser/coqparser.ml src/coqparser/coqlexer.ml src/parser/tptp_parser.ml src/parser/tptp_lexer.ml

include .depend
