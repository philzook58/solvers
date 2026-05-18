% AG01_#3.1 from TPDB
% find X such that  X / 10 = 10
cnf(minus1, axiom, minus(X, '0') = X ).
cnf(minus2, axiom, minus(s(X), s(Y)) = minus(X, Y) ).
cnf(quot1, axiom, quot('0', s(Y)) = '0' ).
cnf(quot2, axiom, quot(s(X), s(Y)) = s(quot(minus(X, Y), s(Y))) ).
cnf(goal, negated_conjecture, quot(X, s(s(s(s(s(s(s(s(s(s('0'))))))))))) != s(s(s(s(s(s(s(s(s(s('0')))))))))) ).
