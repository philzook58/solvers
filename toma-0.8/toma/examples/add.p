cnf(add1, axiom, add('0', Y) = Y ).
cnf(add2, axiom, add(s(X), Y) = s(add(X, Y)) ).
cnf(goal, negated_conjecture, add(X, '0') != s('0') ).
