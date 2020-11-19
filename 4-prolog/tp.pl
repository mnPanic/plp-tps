% Unidades
% Este predicado indica cuáles son las unidades militares disponibles.
unidad(lancero).
unidad(arquero).
unidad(jinete).
unidad(guerrillero).

% Edificios
% Este predicado indica cuáles son los edificios que se pueden construir.
edificio(cuartel).
edificio(arqueria).
edificio(establo).

% Entrenamiento
% Este predicado indica en qué edificio se entrena cada unidad.
entrena(lancero,      cuartel).
entrena(arquero,      arqueria).
entrena(guerrillero,  arqueria).
entrena(jinete,       establo).

% Costos
% Este predicado indica el costo de cada unidad y de cada edificio.
costo(lancero,      80).
costo(arquero,      90).
costo(guerrillero,  70).
costo(jinete,       120).
costo(cuartel,      300).
costo(arqueria,     330).
costo(establo,      400).

% Ej 1 : costo para listas (tanto de batallones como de edificios)
% costo ( +L , -C )
% Enunciado: Extender el predicado "costo" para que funcione con listas, tanto
% de batallones como de edificios.

costo([], 0).
costo([(U, N)|L], C) :-
    unidad(U), costo(U, CU), costo(L, CL),
    C is N * CU + CL.

costo([E|L], C) :-
    edificio(E), costo(E, CE), costo(L, CL),
    C is CE + CL.

% Ej 2 : instanciar un ejército arbitrario
% ejercito ( -E )

% [(arquero, 1)]

desde(X, X).
desde(X, Y) :- N is X+1, desde(N, Y).

% Consideramos al ejercito como un conjunto.
% ejercito(-E)
ejercito(E) :- desde(1, N), armarEjercitoDeTam(E, N).

armarEjercitoDeTam([], 0).
armarEjercitoDeTam([(U, K)|E], N) :-
    unidad(U), between(1, N, K), N2 is N - K, armarEjercitoDeTam(E, N2).

% b. Reversibilidad:
%  -E: Si no viene instanciado, genera ejercitos para todos los N
%  +E: Si viene instanciado, intenta con todos los N hasta que lo encuentra, y
%      devuelve true. Si no es un ejercito posible, se cuelga.
% Concluimos que no es reversible.
%  Para hacerlo, habria que acotar N por el tamano del ejercito si esta
%  instanciado.

% Ej 3 : instancia una lista de edificios necesarios para el ejército
% edificiosNecesarios ( +Ej , -Ed )
edificiosNecesarios(Ej, Ed) :-
    tieneLosNecesarios(Ej, Ed),
    noTieneDemas(Ej, Ed),
    sinRepetidos(Ed).

tieneLosNecesarios([], _).
tieneLosNecesarios([(U, _)|Ej], Ed) :-
    unidad(U), entrena(U, V),
    member(V, Ed),
    tieneLosNecesarios(Ej, Ed).

sinRepetidos(L) :- is_set(L).

noTieneDemas(_, []).
noTieneDemas(Ej, [E|Ed]) :- 
    unidad(U), entrena(U, E), member((U, _), Ej),
    noTieneDemas(Ej, Ed).

% b. Reversibilidad:
% - Ej es reversible pero no d

% Ej 4 : índice de superioridad para unidades
% ids ( +A , +B , -I )
% Enunciado:
  % Se cuenta con el predicado "ids" que calcula el IdS de una unidad sobre otra
  % instanciando dicho valor en el tercer parámetro.
  % Sin embargo, este sólo funciona en algunos casos particulares.
  % Completar y/o modificar la implementación de este predicado para que:
  % a) funcione cuando los primeros dos argumentos corresponden a la misma unidad.
  % En este caso se debe instanciar el tercer parámetro en 1.
  % b) funcione cuando el par de los primeros dos argumentos se corresponde a
  % uno de los ya contemplados pero en el orden inverso.
  % En este caso se debe instanciar el tercer parámetro con el inverso
  % multiplicativo del caso contemplado.
  % c) no se cuelgue ni genere soluciones repetidas.
ids(jinete,       arquero,      1.5).
ids(jinete,       guerrillero,  0.5).
ids(lancero,      jinete,       2).
ids(lancero,      arquero,      0.6).
ids(guerrillero,  lancero,      1.1).
ids(guerrillero,  arquero,      2).

% Reversibilidad:

% Ej 5
% ids ( +A , +B , -I )
ids((UA,CA),(UB,CB),Ib) :- ids(UA,UB,Iu), Ib is Iu * (CA / CB).

% gana ( +A , +B )
gana(A,B) :- ids(A,B,I), I >= 1.
gana(_,[]) :- !.
gana([A|AS],[B|BS]) :- gana(A,B), gana([A|AS],BS), !.
gana([A|AS],[B|BS]) :- gana(B,A), gana(AS,[B|BS]), !.

% ganaA ( ?A , +B , ?N )
% Recordar que un batallón no puede tener más de 5 unidades y un ejército no
% puede tener más de 5 unidades
% entre todos los batallones que lo componen.

% ¿Usaron "ejercito"? ¿por qué?

% Ej 6 : instancia un pueblo para derrotar a un ejército enemigo
% puebloPara ( +En , ?A , -Ed , -Ej )

% Ej 7 : pueblo óptimo (en cantidad de aldenos necesarios)
% puebloOptimoPara( +En , ?A , -Ed , -Ej )

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% TESTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cantidadTestsCosto(10).
testCosto(1) :- costo([(arquero, 2)], 180).
testCosto(2) :- costo([cuartel], 300).
testCosto(3) :- costo([establo, cuartel], 700).
testCosto(4) :- costo([establo, cuartel, arqueria], 1030).
testCosto(5) :- costo([(lancero, 5), (arquero, 2)], 580).
testCosto(6) :- costo([(guerrillero, 7), (jinete, 1)], 610).
testCosto(7) :- costo([], 0).
testCosto(8) :- costo([cuartel, arqueria], 630).
testCosto(9) :- costo([(lancero, 1), (arquero, 77), (jinete, 2), (arquero, 8)], 7970).
testCosto(10) :- costo([(guerrillero, 2),(lancero, 3), (guerrillero, 4), (jinete, 5)], 1260).

cantidadTestsEjercito(5).
testEjercito(1) :- ejercito([(lancero, 1), (jinete, 3)]), !.
testEjercito(2) :- ejercito([(jinete, 5)]), !.
testEjercito(3) :- ejercito([(guerrillero, 4), (guerrillero, 2)]), !.
testEjercito(4) :- ejercito([(arquero, 1)]), !.
testEjercito(5) :- ejercito([(arquero, 4), (guerrillero, 3), (jinete, 12), (lancero, 5)]), !.

cantidadTestsEdificios(5).
testEdificios(1) :- edificiosNecesarios([(arquero, 2), (guerrillero, 2)], [arqueria]).
testEdificios(2) :- edificiosNecesarios([(arquero, 11)], [arqueria]).
testEdificios(3) :- edificiosNecesarios([(guerrillero, 3), (lancero, 3)], Ed), mismos(Ed,[arqueria, cuartel]).
testEdificios(4) :- edificiosNecesarios([(guerrillero, 3), (lancero, 3)], Ed), mismos(Ed, [cuartel, arqueria]).
testEdificios(5) :- edificiosNecesarios([(lancero, 1), (jinete, 10)], Ed), mismos(Ed, [establo, cuartel]).

% Auxiliar para chequear si tienen los mismos elementos
mismos(A,B) :- inc(A,B), inc(B,A).
inc([],_).
inc([A|As],Bs) :- member(A,Bs), inc(As,Bs).

cantidadTestsIdS(8).
testIdS(1) :- ids(jinete, jinete, X), X=:=1.
testIdS(2) :- ids(jinete, lancero, X), X=:=0.5.
testIdS(3) :- ids(lancero, jinete, X), X=:=2.
testIdS(4) :- ids(guerrillero, guerrillero, X), X=:=1.
testIdS(5) :- ids(lancero, guerrillero, X), X=:=0.9090909090909091.
testIdS(6) :- ids(arquero, lancero, X), X=:=1.6666666666666667.
testIdS(7) :- ids(arquero, guerrillero, X), X=:=0.5.
testIdS(8) :- ids(lancero, lancero, X), X=:=1.

cantidadTestsGanaA(5).
testGanaA(1) :- ganaA(E, (jinete, 3), 3), gana(E, (jinete, 3)), !.
testGanaA(2) :- not(ganaA(_, (guerrillero, 7), 6)).
testGanaA(3) :- ganaA(E, [(arquero, 1), (jinete, 1), (lancero, 1)], 2), gana(E, [(arquero, 1), (jinete, 1), (lancero, 1)]), !.
testGanaA(4) :- not(ganaA((guerrillero, 2),[(arquero, 2), (lancero, 4), (jinete, 6)], 2)).
testGanaA(5) :- not(ganaA([(arquero, 2), (jinete, 2), (guerrillero, 2)], [(lancero, 6)], 6)).

cantidadTestsPueblo(4).
testPueblo(1) :- En=[(jinete, 3)],
  puebloPara(En, A, Ed, Ej),
  costo(Ej, Ced), costo(Ej, Cej), C is Ced+Cej, A*50 >= C,
  edificiosNecesarios(Ej, Ed), gana(Ej, En), !.
testPueblo(2) :- En=[(arquero, 1), (lancero, 4)],
  puebloPara(En, A, Ed, Ej),
  costo(Ej, Ced), costo(Ej, Cej), C is Ced+Cej, A*50 >= C,
  edificiosNecesarios(Ej, Ed), gana(Ej,En), !.
testPueblo(3) :- En=[(guerrillero, 5)],
  puebloPara(En, A, Ed, Ej),
  costo(Ej, Ced), costo(Ej, Cej), C is Ced+Cej, A*50 >= C,
  edificiosNecesarios(Ej, Ed), gana(Ej,En), !.
testPueblo(4) :- En=[(jinete, 1), (lancero, 1), (guerrillero, 2), (arquero, 2)],
  puebloPara(En, A, Ed, Ej),
  costo(Ej, Ced), costo(Ej, Cej), C is Ced+Cej, A*50 >= C,
  edificiosNecesarios(Ej, Ed), gana(Ej,En), !.

cantidadTestsPuebloOptimo(5).
testPuebloOptimo(1) :- En=[(jinete,2)], puebloOptimoPara(En,8,[cuartel],[(lancero,1)]), !.
testPuebloOptimo(2) :- En=[(jinete,2)], puebloOptimoPara(En,8,[arqueria],[(guerrillero,1)]), !.%Si no optimizan recursos.
testPuebloOptimo(3) :- En=[(arquero,2)], puebloOptimoPara(En,8,[arqueria],[(guerrillero,1)]), !.
testPuebloOptimo(4) :- En=[(guerrillero, 2), (arquero, 3)], puebloOptimoPara(En, 10, [arqueria], [(guerrillero, 2)]), !.
testPuebloOptimo(5) :- En=[(arquero,4)], not(puebloOptimoPara(En,5,_,_)).

tests(costo) :- cantidadTestsCosto(M), forall(between(1,M,N), testCosto(N)).
tests(ejercito) :- cantidadTestsEjercito(M), forall(between(1,M,N), testEjercito(N)).
tests(edificios) :- cantidadTestsEdificios(M), forall(between(1,M,N), testEdificios(N)).
tests(ids) :- cantidadTestsIdS(M), forall(between(1,M,N), testIdS(N)).
tests(ganaA) :- cantidadTestsGanaA(M), forall(between(1,M,N), testGanaA(N)).
tests(pueblo) :- cantidadTestsPueblo(M), forall(between(1,M,N), testPueblo(N)).
tests(puebloOptimo) :- cantidadTestsPuebloOptimo(M), forall(between(1,M,N), testPuebloOptimo(N)).

tests(todos) :-
  tests(costo),
  tests(ejercito),
  tests(edificios),
  tests(ids),
  tests(ganaA),
  tests(pueblo),
  tests(puebloOptimo).

tests :- tests(todos).