Nagoya Termination Tool (NaTT)
=============================================

This is NaTT ver.2.3.

## Compilation ##

Please install OPAM (https://opam.ocaml.org/). Then please install required packages by
```
opam install ocamlfind ocamlgraph re
opam install xml-light
```
Then please just `make`.

## Usage ##

The command line of NaTT is in the following syntax:
```
./bin/NaTT.exe [file] [option]...
```
The TRS whose termination should be verified is read from either the specified file or the standard input.
The TRS format should follow the [XTC format](https://github.com/TermCOMP/TPDB/blob/master/xml/xtc.xsd) or [an original XML format](format.html), for the moment.

To execute NaTT, an [SMT-LIB 2.0](http://smtlib.org) compliant solver must be installed. One can choose one by the following options:
* `--z3`: [Z3](https://github.com/Z3Prover/z3) version 4.0 or later (default).
* `--cvc4`: [CVC4](https://cvc4.github.io/).

## Contact ##
In case you find bugs, comments, or suggestions, please contact [the author](https://akihisayamada.github.io/).
