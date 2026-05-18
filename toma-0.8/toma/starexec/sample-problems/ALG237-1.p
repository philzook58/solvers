%------------------------------------------------------------------------------
% File     : ALG237-1 : TPTP v9.0.0. Released v4.0.0.
% Domain   : Algebra (Non-associative)
% Problem  : Selfdistributive groupoids are symmetric-by-medial - part 1
% Version  : Especial.
% English  :

% Refs     : [PS08]  Phillips & Stanovsky (2008), Using Automated Theorem P
%          : [Sta08a] Stanovsky (2008), Distributive Groupoids are Symmetri
%          : [Sta08b] Stanovsky (2008), Email to G. Sutcliffe
%          : [Sta08c] Stanovsky (2008), Distributive Groupoids are Symmetric
% Source   : [Sta08b]
% Names    : S08_1 [Sta08b]

% Status   : Unsatisfiable
% Rating   : 1.00 v4.0.0
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   1 RR)
%            Number of literals    :    3 (   3 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   4 con; 0-2 aty)
%            Number of variables   :    6 (   0 sgn)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%------------------------------------------------------------------------------
cnf(c01,axiom,
    mult(A,mult(B,C)) = mult(mult(A,B),mult(A,C)) ).

cnf(c02,axiom,
    mult(mult(A,B),C) = mult(mult(A,C),mult(B,C)) ).

cnf(goals,negated_conjecture,
    mult(mult(mult(a,b),mult(c,d)),mult(mult(a,c),mult(b,d))) != mult(mult(mult(a,c),mult(b,d)),mult(mult(a,b),mult(c,d))) ).

%------------------------------------------------------------------------------
