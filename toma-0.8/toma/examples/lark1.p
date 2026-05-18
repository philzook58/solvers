% from Sprenger and Wymann-Boni (1993)
cnf(lark, axiom, '@'('@'(l, X), Y) = '@'(X, '@'(Y, Y)) ).
cnf(lark3, axiom, l3 = '@'('@'(l, l), l) ).
% L^k L3 = L3 for all k (case k = 3)
cnf(goal, negated_conjecture, '@'('@'(l, '@'(l, '@'(l, l3))), l3) != '@'(l3, l3) ).
