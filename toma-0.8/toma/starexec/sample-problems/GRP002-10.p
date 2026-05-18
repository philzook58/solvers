%------------------------------------------------------------------------------
% File     : GRP002-10 : TPTP v9.0.0. Released v7.3.0.
% Domain   : Puzzles
% Problem  : Commutator equals identity in groups of order 3
% Version  : Especial.
% English  :

% Refs     : [CS18]  Claessen & Smallbone (2018), Efficient Encodings of Fi
%          : [Sma18] Smallbone (2018), Email to Geoff Sutcliffe
% Source   : [Sma18]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.36 v8.2.0, 0.42 v8.1.0, 0.35 v7.5.0, 0.46 v7.4.0, 0.39 v7.3.0
% Syntax   : Number of clauses     :   18 (  18 unt;   0 nHn;   6 RR)
%            Number of literals    :   18 (  18 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   14 (  14 usr;   9 con; 0-4 aty)
%            Number of variables   :   32 (   2 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : Converted from GRP002-1 to UEQ using [CS18].
%------------------------------------------------------------------------------
cnf(ifeq_axiom,axiom,
    ifeq2(A,A,B,C) = B ).

cnf(ifeq_axiom_001,axiom,
    ifeq(A,A,B,C) = B ).

cnf(left_identity,axiom,
    product(identity,X,X) = true ).

cnf(right_identity,axiom,
    product(X,identity,X) = true ).

cnf(left_inverse,axiom,
    product(inverse(X),X,identity) = true ).

cnf(right_inverse,axiom,
    product(X,inverse(X),identity) = true ).

cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) = true ).

cnf(total_function2,axiom,
    ifeq2(product(X,Y,W),true,ifeq2(product(X,Y,Z),true,Z,W),W) = W ).

cnf(associativity1,axiom,
    ifeq(product(U,Z,W),true,ifeq(product(Y,Z,V),true,ifeq(product(X,Y,U),true,product(X,V,W),true),true),true) = true ).

cnf(associativity2,axiom,
    ifeq(product(Y,Z,V),true,ifeq(product(X,V,W),true,ifeq(product(X,Y,U),true,product(U,Z,W),true),true),true) = true ).

cnf(x_cubed_is_identity_1,hypothesis,
    ifeq(product(X,X,Y),true,product(X,Y,identity),true) = true ).

cnf(x_cubed_is_identity_2,hypothesis,
    ifeq(product(X,X,Y),true,product(Y,X,identity),true) = true ).

cnf(a_times_b_is_c,negated_conjecture,
    product(a,b,c) = true ).

cnf(c_times_inverse_a_is_d,negated_conjecture,
    product(c,inverse(a),d) = true ).

cnf(d_times_inverse_b_is_h,negated_conjecture,
    product(d,inverse(b),h) = true ).

cnf(h_times_b_is_j,negated_conjecture,
    product(h,b,j) = true ).

cnf(j_times_inverse_h_is_k,negated_conjecture,
    product(j,inverse(h),k) = true ).

cnf(prove_k_times_inverse_b_is_e,negated_conjecture,
    product(k,inverse(b),identity) != true ).

%------------------------------------------------------------------------------
