%------------------------------------------------------------------------------
% File     : <For TPTP use only>
% Domain   : Rings
% Problem  : Euler's four-square identity
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
% distributivities should be used in the distributing way
cnf(plus_comm, axiom, plus(X, Y) = plus(Y, X) ).
cnf(plus_assoc, axiom, plus(X, plus(Y, Z)) = plus(plus(X, Y), Z) ).
cnf(plus_zero, axiom, plus('0', X) = X ).
cnf(plus_inv, axiom, plus(X, '-'(X)) = '0' ).
cnf(times_assoc, axiom, times(X, times(Y, Z)) = times(times(X, Y), Z) ).
cnf(times_com, axiom, times(X, Y) = times(Y, X) ).
cnf(square, axiom, sq(X) = times(X, X) ).
cnf(distrib, axiom, times(X, plus(Y, Z)) = plus(times(X, Y), times(X, Z)) ).
cnf(distrib, axiom, times(plus(X, Y), Z) = plus(times(X, Z), times(Y, Z)) ).
cnf(sum4, axiom, sum4(X, Y, Z, W) = plus(X, plus(Y, plus(Z, W))) ).
cnf(goals,negated_conjecture,
    ( times(sum4(sq(a1), sq(a2), sq(a3), sq(a4)), sum4(sq(a1), sq(a2), sq(a3), sq(a4))) !=
      sum4(sq(sum4(times(a1, b1), times('-'(a2), b2), times('-'(a3), b3), times('-'(a4), b4))),
           sq(sum4(times(a1, b2), times(a2, b1), times(a3, b4), times('-'(a4), b3))),
           sq(sum4(times(a1, b3), times('-'(a2), b4), times('-'(a3), b1), times(a4, b2))),
           sq(sum4(times(a1, b4), times(a2, b3), times('-'(a3), b2), times('-'(a4), b1))))
    ) ).
%------------------------------------------------------------------------------
