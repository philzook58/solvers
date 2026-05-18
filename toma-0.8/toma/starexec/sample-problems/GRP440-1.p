%--------------------------------------------------------------------------
% File     : GRP440-1 : TPTP v7.5.0. Released v2.6.0.
% Domain   : Group Theory
% Problem  : Axiom for group theory, in product & inverse, part 2
% Version  : [McC93] (equality) axioms.
% English  :

% Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.30 v7.5.0, 0.29 v7.4.0, 0.43 v7.3.0, 0.37 v7.1.0, 0.28 v7.0.0, 0.26 v6.4.0, 0.37 v6.3.0, 0.35 v6.2.0, 0.36 v6.1.0, 0.50 v6.0.0, 0.57 v5.5.0, 0.58 v5.4.0, 0.47 v5.3.0, 0.42 v5.2.0, 0.43 v5.1.0, 0.33 v5.0.0, 0.29 v4.1.0, 0.18 v4.0.1, 0.21 v4.0.0, 0.23 v3.7.0, 0.11 v3.4.0, 0.12 v3.3.0, 0.21 v3.2.0, 0.14 v3.1.0, 0.11 v2.7.0, 0.09 v2.6.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR)
%            Number of atoms       :    2 (   2 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   2 constant; 0-2 arity)
%            Number of variables   :    4 (   0 singleton)
%            Maximal term depth    :    8 (   4 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : A UEQ part of GRP061-1
%--------------------------------------------------------------------------
cnf(single_axiom,axiom,
    ( inverse(multiply(A,multiply(B,multiply(multiply(inverse(B),C),inverse(multiply(D,multiply(A,C))))))) = D )).

cnf(prove_these_axioms_2,negated_conjecture,
    (  multiply(multiply(inverse(b2),b2),a2) != a2 )).

%--------------------------------------------------------------------------
