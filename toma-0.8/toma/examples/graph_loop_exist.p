%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Puzzles
% Problem  : Find a loop in the DAG 0 -> 1 -> 2 -> 3 -> 0.
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

% Comments : The rules are of AG01_#3.13 from TPDB.
%            The predicate reach(X, Y, G, empty) is true if there is a path from X to Y in the directed graph G.
%------------------------------------------------------------------------------
cnf(rule1, axiom, eq('0', '0') = true ).
cnf(rule2, axiom, eq('0', s(X)) = false ).
cnf(rule3, axiom, eq(s(X), '0') = false ).
cnf(rule4, axiom, eq(s(X), s(Y)) = eq(X, Y) ).
cnf(rule5, axiom, or(true, Y) = true ).
cnf(rule6, axiom, or(false, Y) = Y ).
cnf(rule7, axiom, union(empty, H) = H ).
cnf(rule8, axiom, union(edge(X, Y, I), H) = edge(X, Y, union(I, H)) ).
cnf(rule9, axiom, reach(X, Y, empty, H) = false ).
cnf(rule10, axiom, reach(X, Y, edge(U, V, I), H) = if_reach_1(eq(X, U), X, Y, edge(U, V, I), H) ).
cnf(rule11, axiom, if_reach_1(true, X, Y, edge(U, V, I), H) = if_reach_2(eq(Y, V), X, Y, edge(U, V, I), H) ).
cnf(rule12, axiom, if_reach_2(true, X, Y, edge(U, V, I), H) = true ).
cnf(rule13, axiom, if_reach_2(false, X, Y, edge(U, V, I), H) = or(reach(X, Y, I, H), reach(V, Y, union(I, H), empty)) ).
cnf(rule14, axiom, if_reach_1(false, X, Y, edge(U, V, I), H) = reach(X, Y, I, edge(U, V, H)) ).
% Twee easily proves if g is unfolded
cnf(graph, axiom, g = edge('0', s('0'), edge(s('0'), s(s('0')), edge(s(s('0')), s(s(s('0'))), edge(s(s(s('0'))), '0', empty)))) ).
cnf(goal, negated_conjecture, reach(X, X, g, empty) != true ).
%------------------------------------------------------------------------------
