%% File: nanocopi_proof.pl  -  Version: 1.0  -  Date: 1 May 2021
%%
%% Purpose: Presentation of connection proof found by nanoCoP-i
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop-i/
%%
%% Usage:   nanocopi_proof(M,P). % where M is a non-clausal matrix,
%%                               %  P is the (non-clausal) connection
%%                               %  proof found by nanoCoP-i
%%
%% Copyright: (c) 2021 by Jens Otten
%% License:   GNU General Public License


:- assert(proof(leantptp)). % compact, connect, leantptp, readable


%%% output of nanoCoP proof

nanocopi_proof(Mat,Proof) :-
    proof(compact) -> nanocop_compact_proof(Proof) ;
    proof(connect) -> nanocop_connect_proof(Mat,Proof) ;
    proof(readable) -> nanocop_readable_proof(Mat,Proof) ;
    nanocop_leantptp_proof(Mat,Proof).

%%% print compact proof

nanocop_compact_proof(Proof) :-
    print('------------------------------------------------------'),
    nl,
    print('Compact Proof:'), nl,
    print('--------------'), nl,
    print(Proof), nl,
    print('------------------------------------------------------'),
    nl.

%%% print connection proof

nanocop_connect_proof(Mat,Proof) :-
    print('------------------------------------------------------'),
    nl,
    print('Proof for the following non-clausal matrix:'), nl,
    calc_proof(Proof,Mat,Proof1),
    print_matrix(Mat),
    print('Connection Proof:'), nl,
    print('-----------------'), nl,
    print_connect_proof(Proof1),
    print('------------------------------------------------------'),
    nl.

%%% print lean TPTP proof

nanocop_leantptp_proof(Mat,Proof) :-
    print('%-----------------------------------------------------'),
    nl,
    calc_proof(Proof,Mat,Proof1),
    print_matrix_tptp(Mat),
    print_leantptp_proof(Proof1),
    print('%-----------------------------------------------------'),
    nl.

%%% print readable proof

nanocop_readable_proof(Mat,Proof) :-
    print('------------------------------------------------------'),
    nl,
    print_explanations,
    print('Proof:'), nl,
    print('------'), nl,
    print('Translation into a non-clausal matrix:'), nl,
    print_matrix(Mat),
    print_introduction,
    calc_proof(Proof,Mat,Proof1),
    print_readable_proof(Proof1), nl,
    print_ending,
    print('------------------------------------------------------'),
    nl.

%%% calculate nanoCoP proof

% calc_proof(Proof,Mat,Proof1) - calculates non-clausal proof Proof1
% of the form [ (Cla,Num,Sub) | [ Proof1, Proof2, ..., ProofN ] ] of
% matrix Mat from compact nanoCoP output Proof

calc_proof([(I^K)^V:Cla],Mat,[(ClaF,I^K,Sub)|Proof]) :-
    member_mat(I,Mat,0:[],(I^_)^W:Cla2),
    calc_cla(Cla,Cla2,Mat,[],[],Cla1,[VL,VS],Proof),
    flatten_cla(Cla1,0,ClaF),
    append(W,VL,VL1), append(V,VS,VS1), Sub=[VL1,VS1].

% calc_clause(Cla,ClaM,M,Path,Lem,Cla1,Sub,Proof) - returns Cla1
% of proof clause literals in Cla, collect variables from original
% clause ClaM, return Proof of subproofs and substition Sub; M is
% the original matrix, Path is the active path, Lem the lemmata

calc_cla([],_,_,_,_,[],[[],[]],[]).

calc_cla([J^_:(I^_)^V:Cla|ClaT],ClaM,M,Path,Lem,Cla1,Sub,Proof) :-
    !, member(J^_:Mat,ClaM), member((I^_)^W^_:ClaM1,Mat),
    calc_cla(Cla,ClaM1,M,Path,Lem,Cla2,[VL2,VS2],Proof2),
    calc_cla(ClaT,ClaM,M,Path,Lem,Cla3,[VL3,VS3],Proof3),
    ( Cla2=[] -> Cla1=Cla3 ; Cla1=[I:Cla2|Cla3] ),
    append(VL2,VL3,VL4), append(W,VL4,VL1),
    append(VS2,VS3,VS4), append(V,VS4,VS1),
    Sub=[VL1,VS1], append(Proof2,Proof3,Proof).

calc_cla([Lit,ClaPr|ClaT],ClaM,M,Path,Lem,[Lit|Cla1],Sub,Proof) :-
    length([_|Path],IP),  %(Lem=[I:J:_|_] -> J1 is J+1 ; J1=1),
    calc_cla(ClaT,ClaM,M,Path,[IP:Lit|Lem],Cla1,Sub,Proof2),
    ClaPr=IK^V:[NegLit|Cla],
    ( IK=r -> member(I:NegL,Path), NegL==NegLit, Num=r:I, W=[] ;
      IK=l -> member(I:LitL,Lem), LitL==Lit, Num=1:I, W=[] ;
      IK=I^_, Num=IK,  member_mat(I,M,0:[],(I^_)^W:Cla2) ),
    calc_cla(Cla,Cla2,M,[IP:Lit|Path],Lem,Cla3,[VL,VS],Proof3),
    append(W,VL,VL1), append(V,VS,VS1), Sub3=[VL1,VS1],
    flatten_cla(Cla3,0,ClaF), ClaNS=([NegLit|ClaF],Num,Sub3), 
    Proof1=[[ClaNS|Proof3]], append(Proof1,Proof2,Proof).

% member_mat(I,Mat,Cla,Cla1) returns clause Cla1 number I in Mat

member_mat(I,[],J:Cla,Cla1) :- !, J\=0, member_mat(I,Cla,0:[],Cla1).
member_mat(I,Mat,_,(I^K)^V:Cla1) :- member((I^K)^V^_:Cla1,Mat), !.

member_mat(I,[X|M],I2:Cla2,Cla1) :-
    ( ( X=(J^_)^_:Cla ; X=J^_:Cla,atomic(J) ),I>J,J>I2 )
    -> member_mat(I,M,J:Cla,Cla1) ; member_mat(I,M,I2:Cla2,Cla1).

% flatten_cla(Cla,I,Cla1) returns flattend clause Cla1 of Cla

flatten_cla([],_,[]).
flatten_cla([I:C|T],_,C1) :- number(I), !, flatten_cla([C|T],I,C1).
flatten_cla([[X|C]|T],I,C1) :- !, flatten_cla([X|C],I,D),
                               flatten_cla(T,I,E), append(D,E,C1).
flatten_cla([Lit|T],0,[Lit|C1]) :- !, flatten_cla(T,0,C1).
flatten_cla([Lit|T],I,[I:Lit|C1]) :- flatten_cla(T,I,C1).

%%% print lean TPTP nanoCoP proof

print_leantptp_proof([(Cla,Num,Sub)|Proof]) :-
    print_leantptp_proof_step([],Cla,Num,Sub),
    print_leantptp_proof(Proof,[1]).

print_leantptp_proof([],_).

print_leantptp_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    print_leantptp_proof_step([I|J],Cla,Num,Sub),
    print_leantptp_proof(Proof,[1,I|J]), I1 is I+1,
    print_leantptp_proof(Proof2,[I1|J]).

print_leantptp_proof_step(I,Cla,Num,Sub) :-
    print('ncf(\''), append(I,[1],I1), print_step(I1),
    print('\',plain,'), writeq(Cla),
    ( Num=(R:N) -> append(_,[H|T],I1), N1 is N+1, length([H|T],N1),
      ( R=r -> print(',reduction(\''), print_step(T), print('\'') ;
               print(',lemmata(\''), print_lstep(T), print('\'') ) ;
      ( I=[] -> print(',start(') ; print(',extension(') ),
      print(Num)
    ),
    ( Sub=[[],_] -> print(')).') ;
                    print(',bind('), print(Sub), print('))).') ),
    nl.

%%% print connection nanoCoP proof

print_connect_proof([(Cla,Num,Sub)|Proof]) :-
    print_connect_proof_step([],Cla,Num,Sub),
    print_connect_proof(Proof,[1]).

print_connect_proof([],_).

print_connect_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    print_connect_proof_step([I|J],Cla,Num,Sub),
    print_connect_proof(Proof,[1,I|J]), I1 is I+1,
    print_connect_proof(Proof2,[I1|J]).

print_connect_proof_step(I,Cla,Num,Sub) :-
    append(I,[1],I1), print_step(I1), print('  '), print(Cla),
    ( Num=(R:N) -> append(_,[H|T],I1), N1 is N+1, length([H|T],N1),
      ( R=r -> print('   (reduction:'), print_step(T) ;
               print('   (lemmata:'), print_lstep(T) ) ;
      print('   ('), print(Num) ), print(')  '),
    ( Sub=[[],_] -> true ; print('substitution:'), print(Sub) ), nl.

%%% print readable nanoCoP proof

print_readable_proof([(Cla,Num,Sub)|Proof]) :-
    print_clause([],Cla,Num,Sub),
    print_readable_proof(Proof,[1]).

print_readable_proof([],_).

print_readable_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    print_proof_step([I|J],Cla,Num,Sub),
    print_readable_proof(Proof,[1,I|J]), I1 is I+1,
    print_readable_proof(Proof2,[I1|J]).

%%% print nanoCoP proof step

print_proof_step(I,[Lit|Cla],Num,Sub) :-
    print_assume(I,Lit),
    ( Num=(R:N) -> append(_,[H|T],I), length([H|T],N),
      (R=r -> print_redu(I,[H|T]) ; print_fact(I,[R|T])) ;
      print_clause(I,Cla,Num,Sub) ).

print_assume(I,Lit:Pre) :-
    print_step(I), print(' Assume '),
    (-NegLit:(-PreN)=Lit:Pre ; -Lit:(-Pre)=NegLit:PreN) ->
    print(NegLit:PreN), print(' is '), print('false.'), nl.

print_clause(I,Cla,Num,Sub) :-
    print_sp(I), print(' Then clause ('), print(Num), print(')'),
    ( Sub=[[],[]] -> true ; print(' under the substitution '),
                            print(Sub), nl, print_sp(I) ),
    ( Cla=[] -> print(' is true.') ;
      print(' is false if at least one of the following is false:'),
      nl, print_sp(I), print(' '), print(Cla) ), nl.

print_redu(I,J) :-
    print_sp(I), print(' This is a contradiction to assumption '),
    print_step(J), print('.'), nl.

print_fact(I,J) :-
    print_sp(I), print(' This assumption has been refuted in '),
    print_lstep(J), print('.'), nl.

%%% print matrix, print step number, print spaces

print_matrix(Mat) :- print(Mat), nl, nl.

print_matrix_tptp(Mat) :-
    writeq(ncf(matrix,plain,Mat,input)), print('.'), nl.

print_step([I]) :- print(I).
print_step([I,J|T]) :- print_step([J|T]), print('.'), print(I).

print_lstep([_]) :- !, print('x').
print_lstep([_|T]) :- print_step([T]), print('.x'). %lemma

print_sp([]).
print_sp([I]) :- atom(I), !, print(' ').
print_sp([I]) :- I<1.
print_sp([I]) :- I>=1, print(' '), I1 is I/10, print_sp([I1]).
print_sp([I,J|T]) :- print_sp([J|T]), print(' '), print_sp([I]).

%%% print standard proof explanations, introduction/ending of proof

print_explanations :-
 print('Explanations for the proof presented below:'), nl,
 print('- equality axioms are added if required'), nl,
 print('- terms and variables are represented by Prolog terms'), nl,
 print('  and Prolog variables, negation is represented by -'), nl,
 print('- a prefix Pre is a list of variables and constants'), nl,
 print('  and assigned to each literal Lit, i.e. Pre:Lit'), nl,
 print('- clauses and (sub-)matrices have a unique label I^K:'), nl,
 print('  or I^K^[..]:, where I is a unique number/identifier'), nl,
 print('  and K identifies the instance of clause/matrix I'), nl,
 print('- I:Lit refers to literal Lit in clause number I'), nl,
 print('- in the matrix, I^[t1,..,tn] may represent the atom'), nl,
 print('  P_I(t1,..,tn) or the Skolem term f_I(t1,t2,..,tn)'), nl,
 print('- the substitution [[X1,..,Xn],[t1,..,tn]] represents'), nl,
 print('  the assignments X1:=t1, .., Xn:=tn (for both term' ), nl,
 print('  and prefix variables)' ), nl, nl.

print_introduction :-
 print('We prove that the given matrix is valid, i.e. for'), nl,
 print('a given substitution it evaluates to true for all'), nl,
 print('interpretations. A matrix is true iff at least one'), nl,
 print('of its clauses is true; a clause is true iff all of'), nl,
 print('its elements (literals and submatrices) are true.'), nl,nl,
 print('The proof is by contradiction:'), nl,
 print('Assume there is an interpretation so that the given'), nl,
 print('matrix evaluates to false. Then in each clause there'), nl,
 print('has to be at least one element that is false.'), nl, nl.

print_ending :-
 print('Therefore there is no interpretation that makes the'), nl,
 print('given matrix false. Hence the given matrix is valid.'), nl,
 print('                                              q.e.d.'), nl.
