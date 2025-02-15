%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TP-PL (4) - Grupo 'segfault'
%
% Integrantes:
% - Joaquín Ituarte   (LU: 457/13)
% - Elías Cerdeira    (LU: 692/12)
% - Manuel Panichelli (LU: 72/18)

%
% Coloquio: Dani
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
    costo(U, CU), costo(L, CL),
    C is N * CU + CL.

costo([E|L], C) :-
    costo(E, CE), costo(L, CL),
    C is CE + CL.

% Ej 2 : instanciar un ejército arbitrario
% ejercito ( -E )

% Copiado de la clase
desde(X, X).
desde(X, Y) :- N is X+1, desde(N, Y).

% Consideramos al ejercito como un conjunto.
% ejercito(-E)
ejercito(E) :- desde(1, N), armarEjercitoDeTam(E, N).

% armarEjercitoDeTam(-E, +N)
armarEjercitoDeTam([], 0).
armarEjercitoDeTam([(U, K)|E], N) :-
    unidad(U), between(1, N, K), N2 is N - K, armarEjercitoDeTam(E, N2).

% b. Reversibilidad:
%
%  -E: Si no viene instanciado, genera ejercitos para todos los N
%  +E: Si viene instanciado, intenta con todos los N hasta que lo encuentra, y
%      devuelve true. Pero si se piden mas soluciones, se cuelga.
%      Si no es un ejercito posible, se cuelga.
%
% Concluimos que no es reversible.
%  Para hacerlo, habria que acotar N por el tamano del ejercito si esta
%  instanciado.

% Ej 3 : instancia una lista de edificios necesarios para el ejército
% edificiosNecesarios ( +Ej , -Ed )

edificiosNecesarios([], []).
edificiosNecesarios([(U, _)|Ej], Ed) :- 
    edificiosNecesarios(Ej, Ed),
    entrena(U, E), member(E, Ed).

edificiosNecesarios([(U, _)|Ej], [E|Ed2]) :- 
    edificiosNecesarios(Ej, Ed2),
    entrena(U, E), not(member(E, Ed2)).

% b. Reversibilidad:
% -Ej, -Ed: Se cuelga porque primero itera sobre Ej.
% +Ej, +Ed: Funciona, ya que tiene una cantidad de casos acotada para verificar.

% c. Como no es reversible en Ej, lo redefinimos para instanciar con todos los
% posibles ejercitos.
% El nuevo predicado no es reversible en Ej pues ejército tampoco lo es.
edificiosNecesarios2(Ej, Ed) :- ejercito(Ej), edificiosNecesarios(Ej, Ed).

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

% wrapper para no duplicar
% a.c.
ids(U, V, I) :- ids2(U, V, I), !.

ids2(jinete,       arquero,      1.5).
ids2(jinete,       guerrillero,  0.5).
ids2(lancero,      jinete,       2).
ids2(lancero,      arquero,      0.6).
ids2(guerrillero,  lancero,      1.1).
ids2(guerrillero,  arquero,      2).

% a.a.
ids2(U, U, 1) :- unidad(U).

% a.b.
ids2(U, V, I) :- unidad(U), unidad(V), ids2(V, U, I2), I is 1/I2.

% Reversibilidad:
% No es reversible, porque matchea infinitamente con la ultima clausula.
% Se puede arreglar haciendo lo siguiente
%   ids2(U, V, I) :- unidad(U), unidad(V), ids2(V, U, I2), !, I is 1/I2.

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

% Decisión: Generamos siempre ejércitos y no batallones, al igual que el ejemplo
% del enunciado.

% tamanoEjercito(+E, ?N)
tamanoEjercito([], 0).
tamanoEjercito([(U, K)|E], N) :- unidad(U), tamanoEjercito(E, N2), N is K + N2.

% Workaround para que funcione tanto para batallones como para ejércitos.
ganaA(A, (U, C), N) :- ganaA(A, [(U, C)], N).
ganaA((U, C), B, N) :- ganaA([(U, C)], B, N).

ganaA(A, B, N) :-
  % Si N no viene instanciado, hacemos todos los posibles hasta |B|.
  var(N), tamanoEjercito(B, BN), between(1, BN, N),
  armarEjercitoDeTam(A, N), gana(A, B).

ganaA(A, B, N) :-
  % Si N viene instanciado, generamos un ejercito de exactamente ese tamano.
  nonvar(N), armarEjercitoDeTam(A, N), gana(A, B).

% Nota: Separamos en var y nonvar pues sino estariamos restringiendo a que el
% tamaño del ejército A sea menor o igual al de B
% Podriamos hacer lo siguiente si |A| <= |B| siempre:
%
%   ganaA(A, B, N) :-
%     tamanoEjercito(B, BN), between(1, BN, N),
%     armarEjercitoDeTam(A, N), gana(A, B).
%

% ¿Usaron "ejercito"? ¿por qué?
%
% No, ya que ejercito es un predicado de generacion infinita, que no se puede
% usar para generacion finita.

% Ej 6 : instancia un pueblo para derrotar a un ejército enemigo
% puebloPara ( +En , ?A , -Ed , -Ej )

puebloPara(En, A, Ed, Ej) :- var(A),
  % Al no instanciar N, ganaA limita |Ej| <= |En|
  ganaA(Ej, En, _),
  edificiosNecesarios(Ej, Ed),
  costo(Ed, CEd), costo(Ej, CEj),
  % Cada aldeano provee 50 unidades de recursos.
  A is ceiling( (CEd + CEj) / 50 ).

puebloPara(En, A, Ed, Ej) :- nonvar(A),
  % Al no instanciar N, ganaA limita |Ej| <= |En|
  ganaA(Ej, En, _),
  edificiosNecesarios(Ej, Ed),
  costo(Ed, CEd), costo(Ej, CEj),
  Min is ceiling( (CEd + CEj) / 50 ),
  A >= Min.

% Nota: Dividimos en casos pues sino cuando A estuviera instanciado estaríamos
% restringiendo innecesariamente que sea exactamente el costo necesario, cuando
% podría bien ser mayor.

% Ej 7 : pueblo óptimo (en cantidad de aldenos necesarios)
% puebloOptimoPara( +En , ?A , -Ed , -Ej )

puebloOptimoPara(En, A, Ed, Ej) :-
  puebloPara(En, A, Ed, Ej), not(hayMejorPueblo(En, A)).

hayMejorPueblo(En, A) :- puebloPara(En, A2, _, _), A2 < A.

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