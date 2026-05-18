%------------------------------------------------------------------------------
% File     : NUN133-1 : TPTP v9.0.0. Released v8.1.0.
% Domain   : Number Theory
% Problem  : Nicomachus' theorem - proof by induction, step case
% Version  : Especial.
% English  :

% Refs     : [Sma21] Smallbone (2021), Email to Geoff Sutcliffe
% Source   : [Sma21]
% Names    : nicomachus.p [Sma21]

% Status   : Unsatisfiable
% Rating   : 0.68 v8.2.0, 0.75 v8.1.0
% Syntax   : Number of clauses     :   18 (  18 unt;   0 nHn;   4 RR)
%            Number of literals    :   18 (  18 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-2 aty)
%            Number of variables   :   26 (   1 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : 
%------------------------------------------------------------------------------
cnf(plus_comm,axiom,
    '+'(X,Y) = '+'(Y,X) ).

cnf(plus_assoc,axiom,
    '+'(X,'+'(Y,Z)) = '+'('+'(X,Y),Z) ).

cnf(times_comm,axiom,
    '*'(X,Y) = '*'(Y,X) ).

cnf(times_assoc,axiom,
    '*'(X,'*'(Y,Z)) = '*'('*'(X,Y),Z) ).

cnf(plus_zero,axiom,
    '+'(X,'0') = X ).

cnf(times_zero,axiom,
    '*'(X,'0') = '0' ).

cnf(times_one,axiom,
    '*'(X,'1') = X ).

cnf(distr,axiom,
    '*'(X,'+'(Y,Z)) = '+'('*'(X,Y),'*'(X,Z)) ).

cnf(distr_001,axiom,
    '*'('+'(X,Y),Z) = '+'('*'(X,Z),'*'(Y,Z)) ).

cnf(plus_s,axiom,
    '+'(s(X),Y) = s('+'(X,Y)) ).

cnf(times_s,axiom,
    '*'(s(X),Y) = '+'(Y,'*'(X,Y)) ).

cnf(sum_zero,axiom,
    sum('0') = '0' ).

cnf(sum_s,axiom,
    sum(s(N)) = '+'(s(N),sum(N)) ).

cnf(cubes_zero,axiom,
    cubes('0') = '0' ).

cnf(cubes_s,axiom,
    cubes(s(N)) = '+'('*'(s(N),'*'(s(N),s(N))),cubes(N)) ).

cnf(plus_sum,axiom,
    '+'(sum(N),sum(N)) = '*'(N,s(N)) ).

cnf(induction_hypothesis,axiom,
    '*'(sum(a),sum(a)) = cubes(a) ).

cnf(goal,negated_conjecture,
    '*'(sum(s(a)),sum(s(a))) != cubes(s(a)) ).

%------------------------------------------------------------------------------
