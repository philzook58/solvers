%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Rings
% Problem  : Brahmagupta identity
% Version  : <If this is a different form of an existing problem, why it is 
%             different>
% English  :  

% Refs     : <Relevant references>
% Source   : <The Ref where the formulae originate from>
% Names    : <The name(s) of this problem in the literature>

% Status   : <A value from the SZS ontology>
% Rating   : <Don't worry about this one - we'll do it automatically>
% Syntax   : <Don't worry about this one - we'll do it automatically>
% SPC      : <Don't worry about this one - we'll do it automatically>

% Comments : The distributive laws should be used in the distributing way.
%------------------------------------------------------------------------------
cnf(plus_comm, axiom, plus(X, Y) = plus(Y, X) ).
cnf(plus_assoc, axiom, plus(X, plus(Y, Z)) = plus(plus(X, Y), Z) ).
cnf(plus_zero, axiom, plus('0', X) = X ).
cnf(plus_inv, axiom, plus(X, '-'(X)) = '0' ).
cnf(times_assoc, axiom, times(X, times(Y, Z)) = times(times(X, Y), Z) ).
cnf(times_com, axiom, times(X, Y) = times(Y, X) ).
cnf(square, axiom, sq(X) = times(X, X) ).
cnf(distrib1, axiom, times(X, plus(Y, Z)) = plus(times(X, Y), times(X, Z)) ).
cnf(distrib2, axiom, times(plus(X, Y), Z) = plus(times(X, Z), times(Y, Z)) ).
cnf(goals,negated_conjecture,
    ( times(plus(sq(a), times(n, sq(b))), plus(sq(c), times(n, sq(d)))) !=
      plus(sq(plus(times(a, c), times('-'(n), times(b, d)))), times(n, sq(plus(times(a, d), times(b, c))))) ) ).
%------------------------------------------------------------------------------
