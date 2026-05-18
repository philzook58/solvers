%------------------------------------------------------------------------------
% File     : NLP002-10 : TPTP v9.0.0. Released v7.5.0.
% Domain   : Puzzles
% Problem  : "The old dirty white Chevy" problem 2
% Version  : Especial.
% English  :

% Refs     : [CS18]  Claessen & Smallbone (2018), Efficient Encodings of Fi
%          : [Sma18] Smallbone (2018), Email to Geoff Sutcliffe
% Source   : [Sma18]
% Names    :

% Status   : Satisfiable
% Rating   : 0.14 v9.0.0, 0.11 v8.2.0, 0.00 v7.5.0
% Syntax   : Number of clauses     :   56 (  56 unt;   0 nHn;  15 RR)
%            Number of literals    :   56 (  56 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   0 usr;   0 prp; 2-2 aty)
%            Number of functors    :   48 (  48 usr;   7 con; 0-4 aty)
%            Number of variables   :   62 (  11 sgn)
% SPC      : CNF_SAT_RFO_PEQ_UEQ

% Comments : Converted from NLP002-1 to UEQ using [CS18].
%------------------------------------------------------------------------------
cnf(ifeq_axiom,axiom,
    ifeq3(A,A,B,C) = B ).

cnf(ifeq_axiom_001,axiom,
    ifeq2(A,A,B,C) = B ).

cnf(ifeq_axiom_002,axiom,
    ifeq(A,A,B,C) = B ).

cnf(clause1,axiom,
    event(skf1(U,V)) = true ).

cnf(clause2,axiom,
    ifeq2(nonhuman(U),true,entity(U),true) = true ).

cnf(clause3,axiom,
    ifeq2(drs(U),true,proposition(U),true) = true ).

cnf(clause4,axiom,
    ifeq2(proposition(U),true,drs(U),true) = true ).

cnf(clause5,axiom,
    ifeq2(woman(U),true,female(U),true) = true ).

cnf(clause6,axiom,
    ifeq2(female(U),true,human(U),true) = true ).

cnf(clause7,axiom,
    ifeq2(male(U),true,human(U),true) = true ).

cnf(clause8,axiom,
    ifeq2(man(U),true,male(U),true) = true ).

cnf(clause9,axiom,
    ifeq2(object(U),true,entity(U),true) = true ).

cnf(clause10,axiom,
    ifeq2(location(U),true,object(U),true) = true ).

cnf(clause11,axiom,
    ifeq2(city(U),true,location(U),true) = true ).

cnf(clause12,axiom,
    ifeq2(hollywood(U),true,city(U),true) = true ).

cnf(clause13,axiom,
    ifeq2(event(U),true,eventuality(U),true) = true ).

cnf(clause14,axiom,
    ifeq2(artifact(U),true,object(U),true) = true ).

cnf(clause15,axiom,
    ifeq2(way(U),true,artifact(U),true) = true ).

cnf(clause16,axiom,
    ifeq2(street(U),true,way(U),true) = true ).

cnf(clause17,axiom,
    ifeq2(instrumentality(U),true,artifact(U),true) = true ).

cnf(clause18,axiom,
    ifeq2(transport(U),true,instrumentality(U),true) = true ).

cnf(clause19,axiom,
    ifeq2(vehicle(U),true,transport(U),true) = true ).

cnf(clause20,axiom,
    ifeq2(car(U),true,vehicle(U),true) = true ).

cnf(clause21,axiom,
    ifeq2(chevy(U),true,car(U),true) = true ).

cnf(clause31,axiom,
    ifeq2(of(U,V),true,ifeq2(owner(U),true,human(U),true),true) = true ).

cnf(clause32,axiom,
    ifeq2(of(U,V),true,have(skf1(U,V),V,U),true) = true ).

cnf(clause33,axiom,
    ifeq2(have(V,U,W),true,ifeq2(human(U),true,owner(U),true),true) = true ).

cnf(clause34,axiom,
    ifeq3(partof(U,W),true,ifeq3(partof(U,V),true,W,V),V) = V ).

cnf(clause35,axiom,
    ifeq2(have(U,V,W),true,ifeq2(event(U),true,of(V,W),true),true) = true ).

cnf(clause36,axiom,
    ifeq2(have(V,U,W),true,ifeq2(human(U),true,of(U,W),true),true) = true ).

cnf(clause37,axiom,
    ifeq2(of(U,V),true,ifeq2(owner(U),true,have(W,U,V),true),true) = true ).

cnf(clause38,axiom,
    ifeq2(have(W,V,U),true,ifeq2(nonhuman(V),true,ifeq2(nonhuman(U),true,partof(U,V),true),true),true) = true ).

cnf(clause39,negated_conjecture,
    hollywood(skc7) = true ).

cnf(clause40,negated_conjecture,
    city(skc7) = true ).

cnf(clause41,negated_conjecture,
    event(skc6) = true ).

cnf(clause42,negated_conjecture,
    street(skc5) = true ).

cnf(clause43,negated_conjecture,
    way(skc5) = true ).

cnf(clause44,negated_conjecture,
    lonely(skc5) = true ).

cnf(clause45,negated_conjecture,
    old(skc4) = true ).

cnf(clause46,negated_conjecture,
    dirty(skc4) = true ).

cnf(clause47,negated_conjecture,
    white(skc4) = true ).

cnf(clause48,negated_conjecture,
    car(skc4) = true ).

cnf(clause49,negated_conjecture,
    chevy(skc4) = true ).

cnf(clause50,negated_conjecture,
    in(skc6,skc7) = true ).

cnf(clause51,negated_conjecture,
    down(skc6,skc5) = true ).

cnf(clause52,negated_conjecture,
    barrel(skc6,skc4) = true ).

cnf(clause22,axiom,
    ifeq(tuple(nonhuman(U),human(U)),tuple(true,true),a,b) = b ).

cnf(clause23,axiom,
    ifeq(tuple(woman(U),man(U)),tuple(true,true),a,b) = b ).

cnf(clause24,axiom,
    ifeq(tuple(female(U),male(U)),tuple(true,true),a,b) = b ).

cnf(clause25,axiom,
    ifeq(tuple(eventuality(U),abstraction(U)),tuple(true,true),a,b) = b ).

cnf(clause26,axiom,
    ifeq(tuple(entity(U),abstraction(U)),tuple(true,true),a,b) = b ).

cnf(clause27,axiom,
    ifeq(tuple(entity(U),eventuality(U)),tuple(true,true),a,b) = b ).

cnf(clause28,axiom,
    ifeq(tuple(old(U),new(U)),tuple(true,true),a,b) = b ).

cnf(clause29,axiom,
    ifeq(tuple(location(U),artifact(U)),tuple(true,true),a,b) = b ).

cnf(clause30,axiom,
    ifeq(tuple(way(U),instrumentality(U)),tuple(true,true),a,b) = b ).

cnf(goal,negated_conjecture,
    a != b ).

%------------------------------------------------------------------------------
