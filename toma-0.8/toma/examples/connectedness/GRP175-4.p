% for testing connectedness
%----Include equality group theory axioms
%include('Axioms/GRP004-0.ax').
cnf(left_identity,axiom,
    '+'('0',X) = X ).
cnf(left_inverse,axiom,
    '+'('-'(X),X) = '0' ).
cnf(associativity,axiom,
    '+'('+'(X,Y),Z) = '+'(X,'+'(Y,Z)) ).
%----Include Lattice ordered group (equality) axioms
%include('Axioms/GRP004-2.ax').
cnf(symmetry_of_glb,axiom,
    '∧'(X,Y) = '∧'(Y,X) ).

cnf(symmetry_of_lub,axiom,
    '∨'(X,Y) = '∨'(Y,X) ).

cnf(associativity_of_glb,axiom,
    '∧'(X,'∧'(Y,Z)) = '∧'('∧'(X,Y),Z) ).

cnf(associativity_of_lub,axiom,
    '∨'(X,'∨'(Y,Z)) = '∨'('∨'(X,Y),Z) ).

cnf(idempotence_of_lub,axiom,
    '∨'(X,X) = X ).

cnf(idempotence_of_gld,axiom,
    '∧'(X,X) = X ).

cnf(lub_absorbtion,axiom,
    '∨'(X,'∧'(X,Y)) = X ).

cnf(glb_absorbtion,axiom,
    '∧'(X,'∨'(X,Y)) = X ).

%----Monotony of '+'
cnf(monotony_lub1,axiom,
    '+'(X,'∨'(Y,Z)) = '∨'('+'(X,Y),'+'(X,Z)) ).

cnf(monotony_glb1,axiom,
    '+'(X,'∧'(Y,Z)) = '∧'('+'(X,Y),'+'(X,Z)) ).

cnf(monotony_lub2,axiom,
    '+'('∨'(Y,Z),X) = '∨'('+'(Y,X),'+'(Z,X)) ).

cnf(monotony_glb2,axiom,
    '+'('∧'(Y,Z),X) = '∧'('+'(Y,X),'+'(Z,X)) ).
%--------------------------------------------------------------------------
cnf(p06c_1,hypothesis,
    '∧'('0',b) = '0' ).

cnf(prove_p06b,negated_conjecture,
    '∨'('0','+'('-'(a),'+'(b,a))) != '+'('-'(a),'+'(b,a)) ).

%--------------------------------------------------------------------------
