cnf(associativity, axiom, multiply(multiply(V,W,X),Y,multiply(V,W,Z)) = multiply(V,W,multiply(X,Y,Z)) ).

cnf(ternary_multiply_1, axiom, multiply(Y,X,X) = X ).

cnf(ternary_multiply_2, axiom, multiply(X,X,Y) = X ).

cnf(left_inverse, axiom, multiply(inverse(Y),Y,X) = X ).

cnf(right_inverse, axiom, multiply(X,Y,inverse(Y)) = X ).

cnf(prove_inverse_is_self_cancelling, negated_conjecture, inverse(inverse(a)) != a ).
