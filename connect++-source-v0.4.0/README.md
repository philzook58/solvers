**Connect++**
=============

**Connect++** is a fast, readable, C++ implementation of a 
connection prover for first order logic. It is designed 
somewhat in the spirit of *MiniSAT*, with the aim of providing 
a reference implementation that is easily modifiable by 
others. In particular, it aims to provide a basis for 
experiments on improving automated theorem provers using 
machine learning.

**Connect++** is licensed under GNU General Public License 
(GPL) Version 3.

You can download the source from:

<https://www.cl.cam.ac.uk/~sbh11/connect++.html>

The version currently available is V0.4.0.

Contact
-------

Sean Holden is the author of **Connect++** and can be contacted 
at <sbh11@cl.cam.ac.uk>.

Home page: <https://www.cl.cam.ac.uk/~sbh11>.

How to build and use **Connect++**
==================================

Note to M$ Windows users. Sorry, but so far the distribution 
is very much designed for Linux/OS X. I intend at some point 
to extend the `cmake` infrastructure to build for Windows, but 
don't expect this to happen any time soon. Go on! Install 
Linux! (You know you want to...)

Having said that, you may of course find that `cmake` can generate 
a project file for Visual Studio or similar. I haven't tried this. 
If you try it, please let me know how you get on.

Install the *Boost* C++ libraries
---------------------------------

**Connect++** uses *Boost* libraries for parsing, for processing 
command-line options, and for computing hash functions. Also, 
for some random number generation. Depending on what's being 
developed there may be other uses involved. Mostly the *Boost* 
libraries are header-only, but command-line processing (at 
least) requires a compiled library.

Your preferred Linux flavour's package manager, along with 
Homebrew and MacPorts on OS X, will probably make it easy to 
install the *Boost* libaries. Alternatively, you can download 
the *Boost* libraries from:

<https://www.boost.org/>

and compile from source.

**Connect++** currently uses Version 1_84_0. Install so that 
the libraries that require compilation are included.

Install *SWI Prolog* (optional)
-------------------------------

Earlier versions of **Connect++** used a short Prolog program to 
verify proofs. This function is now built-in, but the Prolog 
proof verifier is included in the distribution. If you want to 
use it, you need *SWI Prolog*, which is available here:

<https://www.swi-prolog.org/>

or will probably be provided by the various package managers.

Compile **Connect++**
---------------------

If you don't have `cmake`, install it, either via a package 
manager or from:

<https://cmake.org/>

If you have installed the *Boost* libraries and *SWI Prolog* in the 
usual locations then `cmake` should find and use them automatically:

>     tar -xf connect++-source-v0.4.0.tar.gz
>     cd connect++-source-v0.4.0
>     mkdir build
>     cd build
>     cmake ../source
>     make

You should now have the `connect++` executable in the `build` directory.

If `cmake` can not find the *Boost* libraries try:

>     cmake ../source -D BOOST_INCLUDEDIR=/where/is/include -D BOOST_LIBRARYDIR=/where/is/lib

If you don't need the Prolog proof verifier use:

>     cmake ../source -D INCLUDE_PROLOG=OFF

If you do want the Prolog proof verifier, but `cmake` can't find the `swipl` executable, use:

>     cmake ../source -D swipl_PATH=/where/is/swipl

When `make` succeeds, try:

>     ./connect++ --version 
>     ./connect++ --help

and you should see some useful information. 

Run *Doxygen*
-------------

The source is commented in a format allowing *Doxygen* to 
generate documentation. The output can be found on the 
project web site:

<https://www.cl.cam.ac.uk/~sbh11/connect++.html>

If you want to reformat it to your taste then you can 
install *Doxygen* from 

<https://www.doxygen.nl/>

Prove a theorem
---------------

**Connect++** reads problems in the CNF and FOF formats defined 
by the *Thousands of Problems for Theorem Provers (TPTP)* 
collection. It will process `include`s, and if it detects 
the use of equality it will generate the necessary axioms 
(unless you ask it not to). TPTP along with various tools 
and a description of the format can be found here:

<https://tptp.org/>

If you have TPTP installed then you can set the environment 
variable `TPTP` to the relevant path and **Connect++** will use it:

>     export TPTP=where/to/find/TPTP-v8.2.0

Alternatively use the `--tptp` command-line argument. Assuming 
you've set the `TPTP` environment variable and have TPTP 
installed, you should now be able to do, for example:

>     ./connect++ --schedule default Problems/SET/SET002+3.p

The last line of the output should be:

>     % SZS status Theorem for SET002+3

Note that by default **Connect++** implements the TPTP standard 
of treating constants in double quotes as distinct objects. 
So for example:

>     fof(distinct_objects, conjecture, "Sean" != "Tarquin").

will be a theorem, but:

>     fof(distinct_objects, conjecture, Sean != Tarquin).

won't. If you don't want this behaviour use 
the `--no-distinct-objects` command-line option.

Other environment variables
---------------------------

The `CONNECTPP_PATH` environment variable can be used to set the 
destination for Prolog-readable representations of the proof 
and the matrix. These will be produced if you use the `--prolog` 
command-line option.

Visualising proofs
------------------

**Connect++** can produce a LaTeX-formatted visualization of a proof. 
Use the `--latex` command-line option to do this: 

>     ./connect++ --schedule default --latex default Problems/SET/SET002+3.p

Using `--latex default` will produce a file `./latex_proof.tex`. 
When processed you may find you have to zoom in on it as proofs can 
be quite large. If you want a different filename/location then 
specify it instead of `default`.

Verifying proofs
-----------------

**Connect++** can output a proof certificate and verify it. You 
can do this manually, or ask for it to happen automatically. 
Manual verification requires *SWI Prolog*, as mentioned above. 

### Manual verification 

Run for example:

>     ./connect++ --schedule default --prolog Problems/SET/SET002+3.p

**Connect++** places the files `matrix.pl` and `proof.pl` in 
`CONNECTPP_PATH`. These are prolog-readable summaries 
of the matrix and proof.

In the `build` directory you will find `check_proof`. 
(Assuming you included it in the build.) Now place `matrix.pl`
and `proof.pl` in the same directory as `check_proof` and run:

>     ./check_proof

for a (very) short summary output or:

>     ./check_proof v

For a detailed output.

### Automatic verification

To get automatic verification when a result is proved, use the 
`--verify` command-line argument:

>     ./connect++ --schedule default --verify Problems/SET/SET002+3.p

The last line of the output from the prover should now be:

>     % SZS status Theorem for SET002+3 : Verified

If you see `FailedVerification` instead of `Verified` then 
something is wrong! 

If you want a detailed explanation use `--full-verify`. If you want 
to see a proof in a TPTP-friendly format use `--tptp-proof`. 

Release Notes
-------------

Quite a lot has happened since Version V0.3.0:

- The main change is that the scheduling system has been greatly 
  expanded, and the default schedule is now similar to that of 
  **leanCoP** version 2.1, with a greater range of settings than 
  previously. Use `--show-default-schedule` to display the current 
  version.

- Randomized re-ordering of clauses and/or literals within clauses. 
  (This isn't quite the same as **randoCoP**, which re-orders *axioms* 
  rather than *clauses* as **Connect++** currently does.) Previously  
  there was deterministic re-ordering for clauses only.

- The `--random-seed` command-line argument allows you to set the 
  seed for the random number generation if you need repeatability.

- The `--depth-limit-all` command-line option. By default **Connect++** 
  doesn't depth limit on reductions or lemmata. This can now be 
  switched off. 

- Deterministic reordering starts with the original matrix 
  each time it's used.

- Fixed a bug causing deterministic reordering not to 
  happen when using a schedule. 
  
- Assorted other bug fixes.

- Includes the **meanCoP** heuristic. Use the `--extension-backtrack` 
  command-line option.

TODO
----

- At present the parser does not read annotations after 
  formulas. For example, `SYN000-2.p` will not currently 
  parse correctly. 

- The TPTP `$distinct` predicate is not currently 
  implemented.

- Timeout may fail if conversion to clauses is sufficiently 
  lengthy.

Citation
--------

If you find **Connect++** useful, please cite it by way of the 
following publication, which describes the motivation and 
general thinking behind it:

Sean B Holden. CONNECT++: A New Automated Theorem Prover 
Based on the Connection Calculus. In *Proceedings of the First 
International Workshop on Automated Reasoning with Connection 
Calculi  (AReCCa)*, CEUR Workshop Proceedings, 
Volume 3613, pages 95--106, Prague, Czech Republic, 18th 
September 2023.

<https://ceur-ws.org/Vol-3613/>

