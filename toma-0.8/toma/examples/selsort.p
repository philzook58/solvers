%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Puzzles
% Problem  : selsort(3 : [1, 2, 4, 0]) = [0, 1, 2, 3, 4].
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

% Comments : The rules are of Rubio_04_selsort from TPDB.
%------------------------------------------------------------------------------
cnf(rule1, axiom, eq('0', '0') = true ).
cnf(rule2, axiom, eq('0', s(Y)) = false ).
cnf(rule3, axiom, eq(s(X), '0') = false ).
cnf(rule4, axiom, eq(s(X), s(Y)) = eq(X, Y) ).
cnf(rule5, axiom, le('0', Y) = true ).
cnf(rule6, axiom, le(s(X), '0') = false ).
cnf(rule7, axiom, le(s(X), s(Y)) = le(X, Y) ).
cnf(rule8, axiom, min(cons('0', nil)) = '0' ).
cnf(rule9, axiom, min(cons(s(N), nil)) = s(N) ).
cnf(rule10, axiom, min(cons(N, cons(M, L))) = ifmin(le(N, M), cons(N, cons(M, L))) ).
cnf(rule11, axiom, ifmin(true, cons(N, cons(M, L))) = min(cons(N, L)) ).
cnf(rule12, axiom, ifmin(false, cons(N, cons(M, L))) = min(cons(M, L)) ).
cnf(rule13, axiom, replace(N, M, nil) = nil ).
cnf(rule14, axiom, replace(N, M, cons(K, L)) = ifrepl(eq(N, K), N, M, cons(K, L)) ).
cnf(rule15, axiom, ifrepl(true, N, M, cons(K, L)) = cons(M, L) ).
cnf(rule16, axiom, ifrepl(false, N, M, cons(K, L)) = cons(K, replace(N, M, L)) ).
cnf(rule17, axiom, selsort(nil) = nil ).
cnf(rule18, axiom, selsort(cons(N, L)) = ifselsort(eq(N, min(cons(N, L))), cons(N, L)) ).
cnf(rule19, axiom, ifselsort(true, cons(N, L)) = cons(N, selsort(L)) ).
cnf(rule20, axiom, ifselsort(false, cons(N, L)) = cons(min(cons(N, L)), selsort(replace(min(cons(N, L)), N, L))) ).
cnf(goal, negated_conjecture,
  selsort(cons(s(s(s('0'))), cons(s('0'), cons(s(s('0')), cons(s(s(s(s('0')))), cons('0', nil)))))) !=
  cons('0', cons(s('0'), cons(s(s('0')), cons(s(s(s('0'))), cons(s(s(s(s('0')))), nil))))) ).
%------------------------------------------------------------------------------
