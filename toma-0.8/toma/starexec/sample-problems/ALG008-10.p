%------------------------------------------------------------------------------
% File     : ALG008-10 : TPTP v9.0.0. Released v7.3.0.
% Domain   : Puzzles
% Problem  : TC + right identity does not give RC.
% Version  : Especial.
% English  :

% Refs     : [CS18]  Claessen & Smallbone (2018), Efficient Encodings of Fi
%          : [Sma18] Smallbone (2018), Email to Geoff Sutcliffe
% Source   : [Sma18]
% Names    :

% Status   : Satisfiable
% Rating   : 0.57 v9.0.0, 0.33 v8.2.0, 0.00 v8.1.0, 0.25 v7.5.0, 0.00 v7.4.0, 0.25 v7.3.0
% Syntax   : Number of clauses     :    7 (   7 unt;   0 nHn;   4 RR)
%            Number of literals    :    7 (   7 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    6 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   10 (  10 usr;   8 con; 0-4 aty)
%            Number of variables   :   12 (   1 sgn)
% SPC      : CNF_SAT_RFO_PEQ_UEQ

% Comments : Converted from ALG008-1 to UEQ using [CS18].
%------------------------------------------------------------------------------
cnf(ifeq_axiom,axiom,
    ifeq(A,A,B,C) = B ).

cnf(thomsen_closure,axiom,
    ifeq(multiply(V7,V),V6,ifeq(multiply(X,W),V6,ifeq(multiply(U,V),Z,ifeq(multiply(X,Y),Z,multiply(U,W),multiply(V7,Y)),multiply(V7,Y)),multiply(V7,Y)),multiply(V7,Y)) = multiply(V7,Y) ).

cnf(right_identity,axiom,
    multiply(X,identity) = X ).

cnf(prove_reidimeister1,negated_conjecture,
    multiply(c4,a) = multiply(c3,b) ).

cnf(prove_reidimeister2,negated_conjecture,
    multiply(c2,a) = multiply(c1,b) ).

cnf(prove_reidimeister3,negated_conjecture,
    multiply(c4,f) = multiply(c3,identity) ).

cnf(prove_reidimeister4,negated_conjecture,
    multiply(c2,f) != multiply(c1,identity) ).

%------------------------------------------------------------------------------
