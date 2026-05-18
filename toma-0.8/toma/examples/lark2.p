% from Sprenger and Wymann-Boni (1993)
cnf(lark, axiom, '@'('@'(l, X), Y) = '@'(X, '@'(Y, Y)) ).
cnf(lark3, axiom, l3 = '@'('@'(l, l), l) ).
% R10 (n = 1)
cnf(goal, negated_conjecture, '@'('@'(l, '@'('@'(l, l), '@'(l, l3))), l3) != '@'('@'('@'(l, l), '@'(l, l3)), l3) ).
