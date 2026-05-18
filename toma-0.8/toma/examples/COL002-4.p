%--------------------------------------------------------------------------
% File     : COL002-4 : TPTP v9.0.0. Bugfixed v3.1.0.
% Domain   : Combinatory Logic
% Problem  : Weak fixed point for S, B, C, and I
% Version  : [WM88] (equality) axioms.
%            Theorem formulation : The fixed point is provided and checked.
% English  : The weak fixed point property holds for the set P consisting
%            of the combinators S, B, C, and I, where ((Sx)y)z = (xz)(yz),
%            ((Bx)y)z = x(yz), ((Cx)y)z = (xz)y, and Ix = x.

% Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.2.0, 0.08 v8.1.0, 0.25 v7.5.0, 0.21 v7.4.0, 0.17 v7.3.0, 0.16 v7.1.0, 0.11 v6.4.0, 0.21 v6.3.0, 0.18 v6.2.0, 0.14 v6.1.0, 0.19 v6.0.0, 0.24 v5.5.0, 0.21 v5.4.0, 0.20 v5.3.0, 0.17 v5.2.0, 0.14 v5.1.0, 0.27 v5.0.0, 0.36 v4.1.0, 0.18 v4.0.1, 0.21 v4.0.0, 0.23 v3.7.0, 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0
% Syntax   : Number of clauses     :    6 (   6 unt;   0 nHn;   1 RR)
%            Number of literals    :    6 (   6 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   7 usr;   5 con; 0-2 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : This is the one found in proofs 1 and 2 of C1.1 in [WM88].
% Bugfixes : Fixed clauses weak_fixed_point and prove_weak_fixed_point.
%--------------------------------------------------------------------------
cnf(s_definition,axiom,
    '@'('@'('@'(s,X),Y),Z) = '@'('@'(X,Z),'@'(Y,Z)) ).

cnf(b_definition,axiom,
    '@'('@'('@'(b,X),Y),Z) = '@'(X,'@'(Y,Z)) ).

cnf(c_definition,axiom,
    '@'('@'('@'(c,X),Y),Z) = '@'('@'(X,Z),Y) ).

cnf(i_definition,axiom,
    '@'(i,X) = X ).

cnf(weak_fixed_point,axiom,
    weak_fixed_point(X) = '@'('@'('@'(s,'@'(b,X)),i),'@'('@'(s,'@'(b,X)),i)) ).

cnf(prove_weak_fixed_point,negated_conjecture,
    weak_fixed_point(fixed_pt) != '@'(fixed_pt,weak_fixed_point(fixed_pt)) ).

%--------------------------------------------------------------------------
