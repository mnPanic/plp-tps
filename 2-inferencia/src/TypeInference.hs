module TypeInference (TypingJudgment, Result (..), inferType, inferNormal, normalize) where

import Data.List (intersect, nub, sort, union)
import Exp
import Type
import Unification

------------
-- Errors --
------------
data Result a = OK a | Error String

--------------------
-- Type Inference --
--------------------
type TypingJudgment = (Context, AnnotExp, Type)

typeVarsT :: Type -> [Int]
typeVarsT = foldType (: []) [] [] union id

typeVarsE :: Exp Type -> [Int]
typeVarsE = foldExp (const []) [] id id id [] [] (\r1 r2 r3 -> nub (r1 ++ r2 ++ r3)) (const setAdd) union typeVarsT union (\r1 r2 _ _ r3 -> nub (r1 ++ r2 ++ r3))
  where
    setAdd t r = union (typeVarsT t) r

typeVarsC :: Context -> [Int]
typeVarsC c = nub (concatMap (typeVarsT . evalC c) (domainC c))

typeVars :: TypingJudgment -> [Int]
typeVars (c, e, t) = sort $ union (typeVarsC c) (union (typeVarsE e) (typeVarsT t))

normalization :: [Int] -> [Subst]
normalization ns = foldr (\n rec (y : ys) -> extendS n (TVar y) emptySubst : (rec ys)) (const []) ns [0 ..]

normalize :: TypingJudgment -> TypingJudgment
normalize j@(c, e, t) = let ss = normalization $ typeVars j in foldl (\(rc, re, rt) s -> (s <.> rc, s <.> re, s <.> rt)) j ss

inferType :: PlainExp -> Result TypingJudgment
inferType e = case infer' e 0 of
  OK (_, tj) -> OK tj
  Error s -> Error s

inferNormal :: PlainExp -> Result TypingJudgment
inferNormal e = case infer' e 0 of
  OK (_, tj) -> OK $ normalize tj
  Error s -> Error s

infer' :: PlainExp -> Int -> Result (Int, TypingJudgment)
infer' (SuccExp e) n = case infer' e n of
  OK (n', (c', e', t')) ->
    case mgu [(t', TNat)] of
      UOK subst ->
        OK
          ( n',
            ( subst <.> c',
              subst <.> SuccExp e',
              TNat
            )
          )
      UError u1 u2 -> uError u1 u2
  res@(Error _) -> res
-- COMPLETAR DESDE AQUI

infer' ZeroExp n = OK (n, (emptyContext, ZeroExp, TNat))
infer' (VarExp x) n = OK (n + 1, ((extendC emptyContext x (TVar n)), (VarExp x), (TVar n)))
-- Reminder por si pasa mucho tiempo: (AppExp u v) no tiene anotaciones.
infer' (AppExp u v) n = case infer' u n of -- intentamos primero inferir el tipo de u
  res@(Error _) -> res -- no podemos inferir el tipo de u, devolvemos el error
  OK (n', (c', e', t')) ->
    -- pudimos inferir el tipo de u, tenemos que inferir ahora el de v
    case infer' v n' of -- intentamos inferir el tipo de v
      res'@(Error _) -> res' -- no podemos inferir el tipo de v, devolvemos el error
      OK (n'', (c'', e'', t'')) ->
        -- pudimos inferir el tipo de v. Ahora tenemos que unificar
        case mgu $ (t', (TFun t'' (TVar n''))) : goals of -- unificamos (y obtenemos mgu = subst):
        -- t' (tipo de u) con (t'' -> n'') (funcion que va de tipo de v, a tipo fresco n'' dado por infer sobre v)
        -- goals (los contextos de u y v)
        --
          UError u1 u2 -> uError u1 u2 -- Error en unificacion. devolvemos el error que no podemos unificar
          UOK subst ->
            --unificacion exitosa, retornamos resultado:
            OK
              ( n'' + 1, -- n''+1 es el siguiente tipo fresco y el juicio:
                ( joinC [subst <.> c', subst <.> c''], -- Contexto: Sustitucion de c' (contexto de u),
                -- union y c'' (contexto de v)
                  subst <.> (AppExp e' e''), -- Expresion: Sustitucion sobre la aplicacion de las expreciones anotadas de v y u
                  subst <.> (TVar n'') -- Tipo: Sustitucion sobre el tipo nuevo n''
                )
              )
        where
          goals = foldr f [] (domainC c'')
          f = (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x) : r else r))
-- Reminder por si pasa mucho tiempo: (LamExp x _ e) no tiene anotaciones, por eso el "_" en la expresion.
infer' (LamExp x _ e) n = case infer' e n of -- intentamos inferir el tipo de la expresion sin anotaciones "e"
  res@(Error _) -> res -- si no podemos, devolvemos el error
  OK (n', (c', e', t')) ->
    -- si podemos, retornamos el resultado
    OK -- En el where definimos tau
      ( n' + tauN, -- n' + tauN es el siguiente tipo fresco
        ( -- Juicio de tipado:
          (removeC c' x), -- Contexto: es el contexto de la expresion "e" (c'), sin x
          (LamExp x tau e'), -- Expresion: expresion lambda generada que tiene x de tipo tau con subexpresion e'
          (TFun tau t') -- Tipo: funcion que va de tau (definida en where) a t' (tipo inferido de e)
        )
      )
    where
      tau = if elem x (domainC c') then (evalC c' x) else (TVar n') -- Si x ya estaba en el contexto, tau es el tipo de x, si no es un tipo fresco
      tauN = if elem x (domainC c') then 0 else 1 -- si usamos variable nueva, incrementamos en 1 el n a retornar

-- OPCIONALES

-- infer' (PredExp e)            n = undefined
-- infer' (IsZeroExp e)          n = undefined
-- infer' TrueExp                n = undefined
-- infer' FalseExp               n = undefined
-- infer' (IfExp u v w)          n = undefined

-- EXTENSIÓN

-- Empty
infer' (EmptyListExp _) n = OK (n + 1, (emptyContext, EmptyListExp (TVar n), TList (TVar n)))
-- Cons
infer' (ConsExp u v) n = case infer' u n of -- Intentamos inferir el tipo de u
  res@(Error _) -> res -- no podemos inferir el tipo de u, devolvemos el error
  OK (n', (c', e', t')) ->
    -- pudimos inferir el tipo de u. c' == context_u, e' == expresion u con anotaciones, t' == tipo de e'
    case infer' v n' of -- intentamos ahora inferir el tipo de v
      res'@(Error _) -> res' -- no podemos inferir el tipo de u, devolvemos el error
      OK (n'', (c'', e'', t'')) ->
        -- pudimos inferir el tipo de v. c'' == context_v, e'' == expresion v con anotaciones, t'' == tipo de e''
        case mgu $ (t'', (TList t')) : goals of -- unificamos (y obtenemos mgu = subst):
        -- t'' con [t'] (unificar el tipo "lista del tipo de e' " == [t'], con el tipo de e'' == t'')
        -- goals == unificacion de contextos de e' (u) y e'' (v)
        --
          UError u1 u2 -> uError u1 u2 -- No pudimos obtener el mgu, devolver el error
          UOK subst ->
            -- obtubimos el mgu, retornamos:
            OK
              ( n'' + 1, -- siguiente tipo fresco -- TODO porque +1? osea,no cambia en nada pero nos salteamos un valor
                ( -- Juicio de tipado:
                  joinC [subst <.> c', subst <.> c''], -- Contexto: union de los contextos de e' y e'' (u y v con anot), ambos sustituidos
                  subst <.> (ConsExp e' e''), -- Expresion: sustitucion sobre la expresion con anotaciones
                  subst <.> (t'') -- Tipo: t'' == tipo de e'' == tipo inferido de v
                )
              )
        where
          goals = foldr f [] (domainC c'')
          f = (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x) : r else r))
-- ZipWith
infer' (ZipWithExp u v x y w) n = case infer' u n of -- Intenamos inferir el tipo de u
  res@(Error _) -> res -- si no pudimos inferir el tipo, retornamos el error
  OK (n1, (c1, e1, sigma)) ->
    -- pudimos inferir el tipo
    case infer' v n1 of -- Intentamos inferir el tipo de v
      res1@(Error _) -> res1 -- No pudimos inferirlo, retornamos el error
      OK (n2, (c2, e2, tau)) ->
        -- Pudimos inferirlo
        case infer' w n2 of -- Intentamos inferir el tipo de w
          res4@(Error _) -> res4 -- No pudimos inferirlo, retornamos el error
          OK (n3, (c3, e3, rho)) ->
            -- Pudimos inferirlo
            case mgu $ -- Intentamos obtener el mgu
              [ (sigma, (TList tauX)), -- Unificacion de sigma con [tauX]
                (tau, (TList tauY)) -- Unificacion de tau con [tauY]
              ]
                ++ goals of -- Unificacion de contextos
              UError u1 u2 -> uError u1 u2 -- No pudimos obtener el mgu, retornamos el error
              UOK subst ->
                -- Pudimos definir el MGU. Retornamos:
                --
                OK
                  ( n3 + 2, -- salteamos variables si no se usaron las frescas porque no afecta.
                    ( -- Juicio de tipado:
                      joinC [subst <.> c | c <- cs], -- Contexto: Union de la sustitucion de los contextos
                      subst <.> (ZipWithExp e1 e2 x y e3), -- Expresion: expresion con anotaciones
                      subst <.> (TList rho) -- Tipo: [rho], tipo inferido de la expresion sin anotaciones
                    )
                  )
            where
              tauX = if elem x (domainC c3) then evalC c3 x else TVar n3 -- tauX: mismo tipo si ya estaba en c3. Variable fresca si no
              tauY = if elem y (domainC c3) then evalC c3 y else TVar (n3 + 1) -- tauY: mismo tipo si ya estaba en c3. Variable fresca si no
              goals = concat [unificarContexto (cs !! i) (cs !! j) | i <- [0 .. 2], j <- [0 .. 2]] -- Unificacion de los contextos
              unificarContexto c' c'' = foldr (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x) : r else r)) [] (domainC c'')
              --c3' = extendC (extendC c3 x (TVar n3)) y (TVar (n3+1))
              c3' = removeC (removeC c3 x) y -- c3' es el contexto c3 sin x ni y
              cs = [c1, c2, c3'] -- conjunto de contextos con los candidatos a unificar

--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Result (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
