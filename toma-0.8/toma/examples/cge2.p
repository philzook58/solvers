cnf(unit, axiom, '+'('0', Y) = Y ).
cnf(assoc, axiom, '+'(X, '+'(Y, Z)) = '+'('+'(X, Y), Z) ).
cnf(inv, axiom, '+'('-'(X), X) = '0' ).
cnf(com, axiom, '+'(f(X), g(Y)) = '+'(g(Y), f(X)) ). 
cnf(goal, negated_conjecture, '+'(x, y) != '+'(y, x) ).
