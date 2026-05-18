%------------------------------------------------------------------------------
% File     : ALG299-1 : TPTP v9.0.0. Released v4.1.0.
% Domain   : General Algebra
% Problem  : An equational theory with no nontrivial finite models
% Version  : Especial.
% English  : A classical example of an equational theory with no nontrivial 
%            finite models (found idependently by Tarski, Jonsson, Skornyakov 
%            and others).

% Refs     : [Sta09] Stanovsky (2009), Email to Geoff Sutcliffe
% Source   : [Sta09]
% Names    : austin1 [Sta09]

% Status   : Satisfiable
% Rating   : 0.43 v9.0.0, 0.44 v8.2.0, 0.60 v8.1.0, 0.50 v7.5.0, 0.75 v7.1.0, 0.67 v6.4.0, 0.75 v6.3.0, 0.67 v6.2.0, 0.83 v6.1.0, 0.80 v5.4.0, 0.75 v5.3.0, 0.67 v4.1.0
% Syntax   : Number of clauses     :    3 (   3 unt;   0 nHn;   1 RR)
%            Number of literals    :    3 (   3 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :    4 (   2 sgn)
% SPC      : CNF_SAT_RFO_PEQ_UEQ

% Comments : No finite models.
%------------------------------------------------------------------------------
cnf(sos01,axiom,
    f(product(A,B)) = A ).

cnf(sos02,axiom,
    g(product(A,B)) = B ).

cnf(sos03,axiom,
    tptp1 != tptp0 ).

%------------------------------------------------------------------------------
