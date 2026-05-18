%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Arithmetic
% Problem  : Find X such that X / 4 = 4.
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

% Comments : The rules are of Rubio_04_division in TPDB.
%------------------------------------------------------------------------------
cnf(rule1, axiom, le('0', Y) = true ).
cnf(rule2, axiom, le(s(X), '0') = false ).
cnf(rule3, axiom, le(s(X), s(Y)) = le(X, Y) ).
cnf(rule4, axiom, minus('0', Y) = '0' ).
cnf(rule5, axiom, minus(s(X), Y) = ifMinus(le(s(X), Y), s(X), Y) ).
cnf(rule6, axiom, ifMinus(true, s(X), Y) = '0' ).
cnf(rule7, axiom, ifMinus(false, s(X), Y) = s(minus(X, Y)) ).
cnf(rule8, axiom, quot('0', s(Y)) = '0' ).
cnf(rule9, axiom, quot(s(X), s(Y)) = s(quot(minus(X, Y), s(Y))) ).
cnf(goal, negated_conjecture, quot(X, s(s(s(s('0'))))) != s(s(s(s('0')))) ).
%------------------------------------------------------------------------------
