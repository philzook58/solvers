%--------------------------------------------------------------------------
% File     : BOO023-1 : TPTP v9.0.0. Released v2.2.0.
% Domain   : Boolean Algebra
% Problem  : Half of Padmanabhan's 6-basis with Pixley, part 1.
% Version  : [MP96] (equality) axioms : Especial.
% English  : Part 1 (of 3) of the proof that half of Padmanaban's self-dual
%            independent 6-basis for Boolean Algebra, together with a Pixley
%            polynomial, is a basis for Boolean algebra.

% Refs     : [McC98] McCune (1998), Email to G. Sutcliffe
%          : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq
% Source   : [McC98]
% Names    : DUAL-BA-2-a [MP96]

% Status   : Unsatisfiable
% Rating   : 0.32 v8.2.0, 0.46 v8.1.0, 0.45 v7.5.0, 0.50 v7.4.0, 0.52 v7.3.0, 0.47 v7.1.0, 0.39 v7.0.0, 0.37 v6.4.0, 0.42 v6.3.0, 0.47 v6.2.0, 0.50 v6.1.0, 0.62 v6.0.0, 0.71 v5.5.0, 0.63 v5.4.0, 0.53 v5.3.0, 0.50 v5.1.0, 0.60 v5.0.0, 0.57 v4.1.0, 0.45 v4.0.1, 0.43 v4.0.0, 0.38 v3.7.0, 0.44 v3.4.0, 0.50 v3.1.0, 0.33 v2.7.0, 0.36 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1
% Syntax   : Number of clauses     :    8 (   8 unt;   0 nHn;   1 RR)
%            Number of literals    :    8 (   8 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    8 (   8 usr;   4 con; 0-3 aty)
%            Number of variables   :   15 (   2 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%--------------------------------------------------------------------------
%----Half of Padmanabhan's self-dual independent 6-basis for Boolean Algebra:
cnf(multiply_add,axiom,
    multiply(add(X,Y),Y) = Y ).

cnf(multiply_add_property,axiom,
    multiply(X,add(Y,Z)) = add(multiply(Y,X),multiply(Z,X)) ).

cnf(additive_inverse,axiom,
    add(X,inverse(X)) = n1 ).

%----pixley(X,Y,Z) is a Pixley polynomial:
cnf(pixley_defn,axiom,
    pixley(X,Y,Z) = add(multiply(X,inverse(Y)),add(multiply(X,Z),multiply(inverse(Y),Z))) ).

cnf(pixley1,axiom,
    pixley(X,X,Y) = Y ).

cnf(pixley2,axiom,
    pixley(X,Y,Y) = X ).

cnf(pixley3,axiom,
    pixley(X,Y,X) = X ).

%----Denial of conclusion:
cnf(prove_add_multiply_property,negated_conjecture,
    add(a,multiply(b,c)) != multiply(add(a,b),add(a,c)) ).

%--------------------------------------------------------------------------
