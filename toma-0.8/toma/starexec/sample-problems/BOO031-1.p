%--------------------------------------------------------------------------
% File     : BOO031-1 : TPTP v9.0.0. Released v2.2.0.
% Domain   : Boolean Algebra
% Problem  : Dual BA 3-basis, proof of distributivity.
% Version  : [MP96] (equality) axioms : Especial.
% English  : This is part of a proof of the existence of a self-dual
%            3-basis for Boolean algebra by majority reduction.

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    : DUAL-BA-8-a [MP96]

% Status   : Unsatisfiable
% Rating   : 0.23 v8.2.0, 0.29 v8.1.0, 0.35 v7.5.0, 0.29 v7.4.0, 0.39 v7.3.0, 0.37 v7.1.0, 0.28 v7.0.0, 0.26 v6.4.0, 0.37 v6.3.0, 0.35 v6.2.0, 0.43 v6.1.0, 0.56 v6.0.0, 0.67 v5.5.0, 0.63 v5.4.0, 0.53 v5.3.0, 0.50 v5.1.0, 0.40 v5.0.0, 0.36 v4.1.0, 0.27 v4.0.1, 0.36 v4.0.0, 0.38 v3.7.0, 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.2.0, 0.21 v3.1.0, 0.22 v2.7.0, 0.09 v2.6.0, 0.17 v2.5.0, 0.00 v2.4.0, 0.00 v2.2.1
% Syntax   : Number of clauses     :   12 (  12 unt;   0 nHn;   1 RR)
%            Number of literals    :   12 (  12 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   5 con; 0-2 aty)
%            Number of variables   :   27 (   8 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Self-dual distributivity:
cnf(distributivity,axiom,
    add(multiply(X,Y),add(multiply(Y,Z),multiply(Z,X))) = multiply(add(X,Y),multiply(add(Y,Z),add(Z,X))) ).

%----3 properties of Boolean algebra and the corresponding duals.
cnf(l1,axiom,
    add(X,multiply(Y,multiply(X,Z))) = X ).

cnf(l3,axiom,
    add(add(multiply(X,Y),multiply(Y,Z)),Y) = Y ).

cnf(property3,axiom,
    multiply(add(X,inverse(X)),Y) = Y ).

cnf(l2,axiom,
    multiply(X,add(Y,add(X,Z))) = X ).

cnf(l4,axiom,
    multiply(multiply(add(X,Y),add(Y,Z)),Y) = Y ).

cnf(property3_dual,axiom,
    add(multiply(X,inverse(X)),Y) = Y ).

%----Existence of 0 and 1.
cnf(additive_inverse,axiom,
    add(X,inverse(X)) = n1 ).

cnf(multiplicative_inverse,axiom,
    multiply(X,inverse(X)) = n0 ).

%----Associativity of the 2 operations.
cnf(associativity_of_add,axiom,
    add(add(X,Y),Z) = add(X,add(Y,Z)) ).

cnf(associativity_of_multiply,axiom,
    multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z)) ).

%----Denial of conclusion:
cnf(prove_multiply_add_property,negated_conjecture,
    multiply(a,add(b,c)) != add(multiply(b,a),multiply(c,a)) ).

%--------------------------------------------------------------------------
