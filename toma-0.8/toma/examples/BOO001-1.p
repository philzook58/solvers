%--------------------------------------------------------------------------
% File     : BOO001-1 : TPTP v9.0.0. Released v1.0.0.
% Domain   : Boolean Algebra (Ternary)
% Problem  : In B3 algebra, inverse is an involution
% Version  : [OTTER] (equality) axioms.
% English  :

% Refs     :
% Source   : [OTTER]
% Names    : tba_gg.in [OTTER]

% Status   : Unsatisfiable
% Rating   : 0.09 v8.2.0, 0.08 v8.1.0, 0.10 v7.5.0, 0.08 v7.4.0, 0.13 v7.3.0, 0.11 v7.1.0, 0.06 v7.0.0, 0.05 v6.3.0, 0.06 v6.2.0, 0.07 v6.1.0, 0.06 v6.0.0, 0.19 v5.5.0, 0.21 v5.4.0, 0.07 v5.3.0, 0.00 v5.2.0, 0.07 v5.1.0, 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.25 v2.0.0
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   1 RR)
%            Number of literals    :    6 (   6 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-3 aty)
%            Number of variables   :   13 (   2 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Include ternary Boolean algebra axioms
% include('Axioms/BOO001-0.ax').
cnf(associativity,axiom,
    multiply(multiply(V,W,X),Y,multiply(V,W,Z)) = multiply(V,W,multiply(X,Y,Z)) ).

cnf(ternary_multiply_1,axiom,
    multiply(Y,X,X) = X ).

cnf(ternary_multiply_2,axiom,
    multiply(X,X,Y) = X ).

cnf(left_inverse,axiom,
    multiply(inverse(Y),Y,X) = X ).

cnf(right_inverse,axiom,
    multiply(X,Y,inverse(Y)) = X ).
%--------------------------------------------------------------------------
cnf(prove_inverse_is_self_cancelling,negated_conjecture,
    inverse(inverse(a)) != a ).

%--------------------------------------------------------------------------
