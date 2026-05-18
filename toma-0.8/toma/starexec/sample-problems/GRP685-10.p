%------------------------------------------------------------------------------
% File     : GRP685-10 : TPTP v8.1.2. Released v8.1.0.
% Domain   : Group Theory (Quasigroups)
% Problem  : Axioms of rectangular loops - d
% Version  : Especial.
% English  :

% Refs     : [KP05]  Kinyon & Phillips (2005), Rectangular Quasigroups and
%          : [PS08]  Phillips & Stanovsky (2008), Automated Theorem Proving
%          : [Sma21] Smallbone (2021), Email to Geoff Sutcliffe
% Source   : [Sma21]
% Names    : 

% Status   : Unsatisfiable
% Rating   : 0.21 v8.1.0
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   1 RR)
%            Number of literals    :    8 (   8 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :   16 (   0 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : UEQ version, converted from GRP685+1.p
%------------------------------------------------------------------------------
cnf(f01,axiom,
    ld(A,mult(A,A)) = A ).

cnf(f02,axiom,
    rd(mult(A,A),A) = A ).

cnf(f03,axiom,
    mult(A,ld(A,B)) = ld(A,mult(A,B)) ).

cnf(f04,axiom,
    mult(rd(A,B),B) = rd(mult(A,B),B) ).

cnf(f05,axiom,
    ld(ld(A,B),mult(ld(A,B),mult(C,D))) = mult(ld(A,mult(A,C)),D) ).

cnf(f06,axiom,
    rd(mult(mult(A,B),rd(C,D)),rd(C,D)) = mult(A,rd(mult(B,D),D)) ).

cnf(f07,axiom,
    ld(A,mult(A,ld(B,B))) = rd(mult(rd(A,A),B),B) ).

cnf(goal,negated_conjecture,
    rd(mult(x6,ld(x7,x8)),ld(x7,x8)) != rd(mult(x6,x8),x8) ).

%------------------------------------------------------------------------------
