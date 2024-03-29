% finds a model in [0..99999] assuming infty = 99999
% code can easily be adapted to GnuMultiPres and a formal +infty

% syntax
:- op(1200,xfx,leq).
:- op(1200,xfx,lt).
:- op(1200,xfx,eq).

:- dynamic cb/2, 'eq'/2, 'leq'/2, 'lt'/2, vc/2.

inu(Assoc1,Assoc2,V,W) :- % Assoc1 for state, Assoc2 for search in V
       retractall((_ leq _)), retractall((_ eq _)),retractall((_ lt _)),
       see('u.txt'),
       inu1([],L,[],R),
       seen,
       list_to_assoc([/*'Set'-1,'Prop'-2*/],Assoc1),
       sort(L,W), sort(R,Rset), ord_union(W,Rset,V),
       bagof(Var-(dummy),member(Var,V),Pairs),
       ord_list_to_assoc(Pairs,Assoc2).
       
inu1(Lin,Lout,Rin,Rout) :-
       read(Line),
       (Line=end_of_file -> Lin=Lout, Rin=Rout
       ;
       assert(Line), Line=..[F,X,Y],
       (F=eq -> Lmid=[X,Y|Lin],Rmid=[X,Y|Rin] ; Lmid=[X|Lin],Rmid=[Y|Rin]),
       inu1(Lmid,Lout,Rmid,Rout)
       ).
      
clu :- retractall(cb(_,_)), retractall(vc(_,_)),
       % NB duality needed as only Y can be a max
       forall((X leq Y), assertz(cb(X,[Y]))),
       forall((X eq Y), (assertz(cb(X,[Y])), assertz(cb(Y,[X])))),
       forall(((X lt Y),X\='Set'),  assertz(cb(X,[Y-1]))).
       
chu(A) :- % NB duality
       forall((X leq Y),(get_assoc(X,A,N),get_assoc(Y,A,M), N >= M)),
       forall((X  lt Y),(get_assoc(X,A,N),get_assoc(Y,A,M), N > M)),
       forall((X  eq Y),(get_assoc(X,A,N),get_assoc(Y,A,M), N == M)),
       write('verified, Prop level '),get_assoc('Prop',A,N),write(N),nl. 

dou :- inu(A0,Va,V,Concls),    
       clu,
       forall(member(Var,V),(( %Var='update_shadow.u0',
       put_assoc(progress,A0,0,A01), put_assoc(Var,A01,1,A1),
       %put_assoc('Set',A02,1,A03), put_assoc('Prop',A03,2,A1),       
       catch((thm32(Va,V,Concls,[],A1,Model),uprint(Var,Model)),
       loop(W),print(W))    );true)
             ).

% based_on/2 checks whether X contains all variables occurring in Sup

based_on(V,Sup):- forall(member(T,Sup),
  (T=Var+_ -> a_member(Var,V);
  (T=Var-_ -> a_member(Var,V);
              a_member(T,V)))).

% surplus/4 computes the maximal upward shift of Sup that is true
 
surplus([],AccuS,AccuS,_).
surplus([T|Ts],Sold,Snew,A):- /* may fail is some V undefined */
  (T=V+K -> (get_assoc(V,A,N),Smid is min(Sold,N-K)) ;
  (T=V-K -> (get_assoc(V,A,N),Smid is min(Sold,N+K)) ;
            (get_assoc(T,A,N),Smid is min(Sold,N)))),
  surplus(Ts,Smid,Snew,A).

% try_improve/6 tries to improve Var with Sup=>Var, Sup based on V

try_improve(V,Sup,Var,Imp,A0,A):- 
    (based_on(V,Sup),surplus(Sup,99999,M,A0),
       (get_assoc(Var,A0,N) -> (N<M -> put_assoc(Var,A0,M,A1))
        ;
        put_assoc(Var,A0,M,A1))
    ) ->
     Imp = [Var],
     A1=A
     ;
     A0=A,
     Imp = [].
  
try_improve_list(_,[],_,Imp,Imp,Assoc,Assoc) :- !.

try_improve_list(V,[Sup|Sups],Var,Imp0,Imp,A0,A2):-
   try_improve(V,Sup,Var,I,A0,A1),(member(Var,I)->Imp1=I;Imp1=Imp0),
   try_improve_list(V,Sups,Var,Imp1,Imp,A1,A2).


forward(_,[],I,Isorted,A,A):- !,sort(I,Isorted).

forward(Va,[Var|W],I0,Improved,A0,A):- 
  once((setof(Sup,cb(Var,Sup),Sups);Sups=[])),       %/*test*/ write(Var), nl,
  try_improve_list(Va,Sups,Var,[],I,A0,A1),   %/*test*/ showprogress(A1),
  append(I,I0,I1),                           %/*test*/ write(I1), nl,
  forward(Va,W,I1,Improved,A1,A).

% The arguments V,C define the set of clauses with sups over V, with
% conclusion in C. Always: I subset C subset V with list_of_keys(Va,V).

thm32(Va,V,C,I,A0,A) :- 
  % fix later: the following detects loops, but then stops 
  /*showprogress(A0),*/
  forward(Va,C,[],U,A0,A1),
  (U = [] -> A0 = A 
           ; ord_union(I,U,IU),
             ((length(V,N),length(IU,N)) -> throw(loop(V)),nl
              ; % now we should actually simplify
  % termination of the following line should be proved (Lemma 3.3)
              bagof(Var-0,member(Var,IU),Pairs),
              ord_list_to_assoc(Pairs,IUa),              
              lemma33(Va,IUa,IU,A1,A2),                                   
              ord_subtract(C,IU,CmIU), 
              forward(Va,CmIU,[],R,A2,A3),
              (R = [] -> A=A3 ;
                         ord_union(IU,R,IUR),
                         thm32(Va,V,C,IUR,A3,A))
              )
  ).

lemma33(Va,Wa,W,A0,A) :-
  thm32(Wa,W,W,[],A0,A1),
  forward(Va,W,[],U,A1,A2),
  (U = [] -> A2 = A 
           ; lemma33(Va,Wa,W,A2,A)
  ).
  
  

%%%%%%%avoid reading this block with silly auxiliaries%%%%%%%

% ugly printing

uprint(Var,Assoc) :- assoc_to_list(Assoc,L),include(positive,L,Lpos),
            (length(Lpos,X) -> 
            write(Var),write(' implies: '),write(X),nl,
            assert(vc(Var,Lpos))
            ;
            true).
             
% miscellaneous

positive(Var-N):- Var \= progress, N>(-1).

a_member(Var,V) :- get_assoc(Var,V,_).

addprogress(X,A0,A) :- get_assoc(progress,A0,N),M is N+X,
                       put_assoc(progress,A0,M,A).
showprogress(A) :- get_assoc(progress,A,N),write(N),nl.

ask(M,A,B) :- get_assoc(A,M,X),get_assoc(B,M,Y),write(X-Y),nl.

% not used yet
%ext(F,E,FE):- atom_concat(F,'.',F1),atom_concat(F1,E,FE).
%io(Dest,Mode,Name,DO):-open(Dest,Mode,_,[alias(Name)]),
%       (Mode=write->set_output(Name);set_input(Name)),DO,close(Name).
%out(Fi):-ext(Fi,out,Fo),io(Fo,write,out,test(Fi)).

