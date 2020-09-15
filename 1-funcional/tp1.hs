import Data.List
import Test.HUnit
import Midi.Midi

type Tono         = Integer
type Duracion     = Integer
type Instante     = Integer

data Melodia = 
     Silencio Duracion |
     Nota Tono Duracion |
     Secuencia Melodia Melodia | 
     Paralelo [Melodia]
  deriving Show

-- Funciones auxiliares dadas

foldNat :: a->(a->a)->Integer->a
foldNat caso0 casoSuc n | n == 0 = caso0
      | n > 0 = casoSuc (foldNat caso0 casoSuc (n-1))
      | otherwise = error "El argumento de foldNat no puede ser negativo."

-- Funciones pedidas

-- Ejercicio 1

-- hace sonar la primera melodia, luego de d hace sonar la segunda en paralelo
superponer :: Melodia -> Duracion -> Melodia -> Melodia
superponer m1 d m2 = Paralelo [m1, Secuencia (Silencio d) m2]

-- Sugerencia: usar foldNat
-- reproduce la melodia m n veces esperando d antes de reproducir cada una
canon :: Duracion -> Integer -> Melodia -> Melodia
canon d n m = foldNat m (superponer m d) (n-1)

-- dada una lista no vacia de melodias las toca en secuencia preservando el
-- orden.
secuenciar :: [Melodia] -> Melodia -- Se asume que la lista no es vacía.
-- secuenciar = foldl1 (\acc x -> (Secuencia acc x))
secuenciar = foldl1 (Secuencia)

-- Ejercicio 2

-- es como canon pero genera una melodia infinita
-- sug foldr
canonInfinito :: Duracion -> Melodia -> Melodia
canonInfinito d m = foldr1 (\x r -> superponer x d r) (repeat m)

-- Ejercicio 3

foldMelodia ::
  (Duracion -> a)             -- silencio
  -> (Tono -> Duracion -> a)  -- nota
  -> (a -> a -> a)            -- secuencia
  -> ([a] -> a)               -- paralelo
  -> Melodia -> a

foldMelodia cSil cNot cSeq cPar m = case m of
  (Silencio d) -> cSil d
  (Nota t d) -> cNot t d
  (Secuencia m1 m2) -> cSeq (rec m1) (rec m2)
    where rec = foldMelodia cSil cNot cSeq cPar
  (Paralelo ms) -> cPar $ map rec ms
    where rec = foldMelodia cSil cNot cSeq cPar

-- Ejercicio 4

-- aplica la funcion a cada nota de la melodia, manteniendo la estructura
mapMelodia :: (Tono -> Tono) -> Melodia -> Melodia
mapMelodia f = foldMelodia (Silencio) cNot (Secuencia) (Paralelo)
  where cNot t d = Nota (f t) d

-- transportar n m es la melodia m transportada n semitonos
-- Equivalente a sumarle el valor de n a cada tono de m
transportar :: Integer -> Melodia -> Melodia
transportar n = mapMelodia (+n)

-- Calcula la duracion (en beats) de una melodia. Asumir que en paralelo de 0
-- melodias dura 0 beats.
duracionTotal :: Melodia->Duracion
duracionTotal = foldMelodia cSil cNot cSeq cPar
  where cSil = id
        cNot t d = d
        cSeq = (+)
        cPar [] = 0
        cPar ds = maximum ds

--Sugerencia: usar round y fromIntegral
cambiarVelocidad :: Float -> Melodia -> Melodia
cambiarVelocidad factor = foldMelodia cSil cNot cSeq cPar
  where escalar d = round ((fromIntegral d) * factor)
        cSil d = Silencio $ escalar d
        cNot t d = Nota t $ escalar d
        cSeq = Secuencia
        cPar = Paralelo

-- invierte una melodia, las notas y silencios se reproducen en el orden inverso
invertir :: Melodia -> Melodia
invertir = foldMelodia cSil cNot cSeq cPar
  where cSil = Silencio
        cNot = Nota
        cSeq m1 m2 = Secuencia m2 m1
        cPar ms = (Paralelo $ reverse ms)


-- Ejercicio 5

-- Indica que notas de la melodia estan sonando en un instante dado.

-- En instantes menores que 0 no suena ninguna nota.
-- Se puede usar recursión explícita.
-- Resaltar las partes del código que hacen que no se ajuste al esquema fold.
notasQueSuenan :: Instante -> Melodia -> [Tono]
--Sugerencia: usar concatMap.
notasQueSuenan i m
  | i < 0 = []
  | otherwise = case m of
      (Silencio d) -> []
      (Nota t d) -> if d >= i then [t] else []
      (Secuencia m1 m2) ->
        if dm1 >= i
        then notasQueSuenan i m1
        else notasQueSuenan (i - dm1) m2
        where dm1 = duracionTotal m1
      (Paralelo ms) -> concatMap (notasQueSuenan i) ms

notasQueSuenan' :: Melodia -> (Instante -> [Tono])
notasQueSuenan' = foldMelodia cSil cNot cSeq cPar
  where cSil d = (\i -> [])
        cNot t d = (\i -> if d >= i then [t] else [])
        -- problema: no hay forma de saber en cual parte de la secuencia buscar
        -- las notas que suenan. No hay forma de obtener cuanto dura cada
        -- melodia.
        cSeq f1 f2 = (\i -> (f1 i) ++ (f2 i))
        cPar fns = (\i -> concatMap ($i) fns)

{-
Cosas que no funcionan

- foldMelodia: No es SOLO recursion estructural, es recursion sobre i y sobre la
  estructura de la melodia.
-}

-- Ejercicio 6

data Evento = On Instante Tono | Off Instante Tono deriving (Show, Eq)

--Sugerencia: usar listas por comprensión. No repetir eventos.
cambios :: Instante->[Tono]->[Tono]->[Evento]
cambios = undefined

--Sugerencia: usar foldl sobre la lista de 0 a la duración.
eventosPorNotas :: (Instante->[Tono])->Duracion->[Evento]
eventosPorNotas = undefined

eventos :: Melodia -> Duracion -> [Evento]
eventos = undefined

-- GENERADOR

unev (On i x)  = (i, Left x)
unev (Off i x) = (i, Right x)

generarMidi :: String -> [Evento] -> IO ()
generarMidi archivo eventos = midiCreateFile archivo midiEvents
  where
    eventos' = let e = map unev eventos in zipWith (\(t0, _) (t1, e) -> (t1 - t0, e)) ((0, error ""):e) e
    midiEvents = case eventos' of
                   [] -> [midiNoteOn 1 0 0 10, midiNoteOn 1 0 0 0]
                   es -> toMidi es

toMidi = map (\(d, ev) -> case ev of
                Left  n -> midiNoteOn d 0 n 127
                Right n -> midiNoteOn d 0 n 0)

--Notas para pruebas.

_sol0 = Nota 55
_si0  = Nota 59
_do = Nota 60
_reb  = Nota 61
_re = Nota 62
_mib  = Nota 63
_mi = Nota 64
_fa = Nota 65
_fas  = Nota 66
_sol = Nota 67
_lab  = Nota 68
_la = Nota 69
_sib  = Nota 70
_si = Nota 71
_do2  = Nota 72
_reb2 = Nota 73
_re2  = Nota 74
_mib2 = Nota 75
_fa2  = Nota 77

-- Melodías para pruebas.

acorde :: Melodia
acorde = Paralelo [_do 10, Secuencia (Silencio 3) (_mi 7), Secuencia (Silencio 6) (_sol 4)]

doremi :: Melodia
doremi = secuenciar [_do 3, _re 1, _mi 3, _do 1, _mi 2, _do 2, _mi 4]

-- Pongan sus propias pruebas y melodías. Pueden definir más notas, la numeración es por semitonos.

-- Canon APL (autor: Pablo Barenbaum)

rhoRhoRhoOfX, alwaysEqualsOne, rhoIsDimensionRhoRhoRank, aplIsFun :: Melodia
rhoRhoRhoOfX = secuenciar $ map (\(d, f)->f d) [(4, _do), (4, _do), (3, _do), (1, _re), (4, _mi)]
alwaysEqualsOne = secuenciar $ map (\(d, f)->f d) [(3, _mi), (1, _re), (3, _mi), (1, _fa), (8, _sol)]
rhoIsDimensionRhoRhoRank = secuenciar $ map (\(d, f)->f d) [(12, _do2), (12, _sol), (12, _mi), (12, _do)]
aplIsFun = secuenciar $ map (\(d, f)->f d) [(3, _sol), (1, _fa), (3, _mi), (1, _re), (8, _do)]

mezcla :: Melodia
mezcla = Paralelo [rhoRhoRhoOfX, Secuencia (Silencio 4) alwaysEqualsOne, Secuencia (Silencio 8) rhoIsDimensionRhoRhoRank, Secuencia (Silencio 12) aplIsFun]

-- Cangrejo (autor: Pablo Barenbaum)

stac :: Tono -> Melodia
stac t = Secuencia (Nota t 9) (Silencio 1)

stacatto :: Melodia -> Melodia
stacatto = foldMelodia Silencio (\t d->stac t) Secuencia Paralelo

cangrejo1 = secuenciar $ 
         [Silencio 4, _do 2, _mib 2]
      ++ [_sol 2, _lab 4, Silencio 2]
      ++ [_si0 4, Silencio 2, _sol 4] 
      ++ [_fas 4, _fa 4]              
      ++ [_mi 2, Silencio 2, _mib 4]  
      ++ [_re 2, _reb 2, _do 2]
      ++ [_si0 2, _sol0 2, _do 2, _fa 2]
      ++ [_mib 2, _re 4, Silencio 2]
      ++ [_do 2, _mi 2, Silencio 4]
cangrejo2 = secuenciar $ (map (\(d, f)->f d)) $
               [(2, _do), (2, _mib), (2, _sol), (2, _do2)]
            ++ [(1, _sib), (1, _do2), (1, _re2), (1, _mib2),
                (1, _fa2), (1, _mib2), (1, _re2), (1, _do2)]
            ++ [(1, _re2), (1, _sol), (1, _re2), (1, _fa2),
                (1, _mib2), (1, _re2), (1, _do2), (1, _si)]
            ++ [(1, _la), (1, _si), (1, _do2), (1, _mib2),
                (1, _re2), (1, _do2), (1, _si), (1, _la)]
            ++ [(1, _sol), (1, _lab), (1, _sib), (1, _reb2),
                (1, _do2), (1, _sib), (1, _lab), (1, _sol)]
            ++ [(1, _fa), (1, _sol), (1, _lab), (1, _sib),
                (1, _lab), (1, _sol), (1, _fa), (1, _mib)]
            ++ [(1, _re), (1, _mib), (1, _fa), (1, _sol),
                (1, _fa), (1, _mib), (1, _re), (1, _lab)]
            ++ [(1, _sol), (1, _fa), (1, _mib), (1, _do2),
                (1, _si), (1, _la), (1, _sol), (1, _fa)]
            ++ [(1, _mi), (1, _re), (1, _mi), (1, _sol),
                (1, _do2), (1, _sol), (1, _fa), (1, _sol)]
                
cangrejo = Secuencia c (invertir c)
  where c = Paralelo [cangrejo1, cangrejo2]

--

genMelodia :: String -> Melodia -> Duracion -> IO ()
genMelodia fn m dur = generarMidi fn (eventos m dur)

main :: IO ()
main = do
   putStr "Generando apl-is-fun.mid...\n"
   genMelodia "apl-is-fun.mid" (stacatto mezcla) 500
   putStr "Generando cangrejo.mid...\n"
   genMelodia "cangrejo.mid" (stacatto cangrejo) 1000

-- Tests
tests :: IO Counts
tests = do runTestTT allTests

allTests = test [
  "ejercicio1" ~: testsEj1,
  "ejercicio2" ~: testsEj2,
  "ejercicio3" ~: testsEj3,
  "ejercicio4" ~: testsEj4,
  "ejercicio5" ~: testsEj5,
  "ejercicio6" ~: testsEj6
  ]

-- Ejemplos sólo para mostrar cómo se escriben los tests. Reemplazar por los tests propios.

testsEj1 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj2 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj3 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj4 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj5 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj6 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
