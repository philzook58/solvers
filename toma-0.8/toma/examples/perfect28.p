%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Number theory
% Problem  : Find a perfect number X >= 7. The smallest is X = 28.
% Version  : <If this is a different form of an existing problem, why it is 
%             different>
% English  : <A full description of the problem>

% Refs     : <Relevant references>
% Source   : <The Ref where the formulae originate from>
% Names    : <The name(s) of this problem in the literature>

% Status   : <A value from the SZS ontology>
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : <Don't worry about this one - we'll do it automatically>
% SPC      : <Don't worry about this one - we'll do it automatically>

% Comments : The rules are of HirokawaMiddeldorp_04_t003 from TPDB.
%------------------------------------------------------------------------------
% find a perfect number X >= 7. the smallest is 28.
cnf(rule1, axiom, '-'(X, '0') = X ).
cnf(rule2, axiom, '-'(s(X), s(Y)) = '-'(X, Y) ).
cnf(rule3, axiom, '<='('0', Y) = true ).
cnf(rule4, axiom, '<='(s(X), '0') = false ).
cnf(rule5, axiom, '<='(s(X), s(Y)) = '<='(X, Y) ).
cnf(rule6, axiom, if(true, X, Y) = X ).
cnf(rule7, axiom, if(false, X, Y) = Y ).
cnf(rule8, axiom, perfectp('0') = false ).
cnf(rule9, axiom, perfectp(s(X)) = f(X, s('0'), s(X), s(X)) ).
cnf(rule10, axiom, f('0', Y, '0', U) = true ).
cnf(rule11, axiom, f('0', Y, s(Z), U) = false ).
cnf(rule12, axiom, f(s(X), '0', Z, U) = f(X, U, '-'(Z, s(X)), U) ).
cnf(rule13, axiom, f(s(X), s(Y), Z, U) = if('<='(X, Y), f(s(X), '-'(Y, X), Z, U), f(X, U, Z, U)) ).
cnf(goal, negated_conjecture, perfectp(s(s(s(s(s(s(s(X)))))))) != true).
%------------------------------------------------------------------------------
