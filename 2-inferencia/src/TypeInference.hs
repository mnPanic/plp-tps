module TypeInference (TypingJudgment, Result(..), inferType, inferNormal, normalize)

where

import Data.List(intersect, union, nub, sort)
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
typeVarsT = foldType (:[]) [] [] union id

typeVarsE :: Exp Type -> [Int]
typeVarsE = foldExp (const []) [] id id id [] [] (\r1 r2 r3 ->nub(r1++r2++r3)) (const setAdd) union typeVarsT union (\r1 r2 _ _ r3->nub(r1++r2++r3))
  where setAdd t r = union (typeVarsT t) r

typeVarsC :: Context -> [Int]
typeVarsC c = nub (concatMap (typeVarsT . evalC c) (domainC c))

typeVars :: TypingJudgment -> [Int]
typeVars (c, e, t) = sort $ union (typeVarsC c) (union (typeVarsE e) (typeVarsT t))

normalization :: [Int] -> [Subst]
normalization ns = foldr (\n rec (y:ys) -> extendS n (TVar  y) emptySubst : (rec ys)) (const []) ns [0..]

normalize :: TypingJudgment -> TypingJudgment
normalize j@(c, e, t) = let ss = normalization $ typeVars j in foldl (\(rc, re, rt) s ->(s <.> rc, s <.> re, s <.> rt)) j ss
  
inferType :: PlainExp -> Result TypingJudgment
inferType e = case infer' e 0 of
    OK (_, tj) -> OK tj
    Error s -> Error s
    
inferNormal :: PlainExp -> Result TypingJudgment
inferNormal e = case infer' e 0 of
    OK (_, tj) -> OK $ normalize tj
    Error s -> Error s


infer' :: PlainExp -> Int -> Result (Int, TypingJudgment)

infer' (SuccExp e)    n = case infer' e n of
                            OK (n', (c', e', t')) ->
                              case mgu [(t', TNat)] of
                                UOK subst -> OK (n',
                                                    (
                                                     subst <.> c',
                                                     subst <.> SuccExp e',
                                                     TNat
                                                    )
                                                )
                                UError u1 u2 -> uError u1 u2
                            res@(Error _) -> res

-- COMPLETAR DESDE AQUI

infer' ZeroExp      n = OK (n, (emptyContext, ZeroExp, TNat))
infer' (VarExp x)   n = OK (n+1, ((extendC emptyContext x (TVar n)), (VarExp x), (TVar n)))
infer' (AppExp u v) n = case infer' u n of
                          res@(Error _) -> res 
                          OK (n', (c', e', t')) ->
                            case infer' v n' of
                              res'@(Error _) -> res'
                              OK (n'', (c'', e'', t'')) -> 
                                case mgu $ (t', (TFun t'' (TVar n''))):goals of
                                  UError u1 u2 -> uError u1 u2
                                  UOK subst -> OK (n''+1,
                                      (
                                        joinC [subst <.> c', subst <.> c''],
                                        subst <.> (AppExp e' e''),
                                        subst <.> (TVar n'')
                                      )
                                    )
                                  where goals = foldr f [] (domainC c'')
                                        f = (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x):r else r)) 
infer' (LamExp x _ e) n = case infer' e n of
                            res@(Error _) -> res
                            OK (n', (c', e', t')) ->
                              OK (n'+tauN, 
                                  (
                                    (removeC c' x), 
                                    (LamExp x tau e'),
                                    (TFun tau t')
                                  )
                                )
                              where tau = if elem x (domainC c') then (evalC c' x) else (TVar n')
                                    tauN = if elem x (domainC c') then 0 else 1

-- OPCIONALES

-- infer' (PredExp e)            n = undefined
-- infer' (IsZeroExp e)          n = undefined
-- infer' TrueExp                n = undefined
-- infer' FalseExp               n = undefined
-- infer' (IfExp u v w)          n = undefined

-- EXTENSIÓN

infer' (EmptyListExp _)       n = OK (n+1, (emptyContext, EmptyListExp (TVar n), TList (TVar n)))
infer' (ConsExp u v)          n = case infer' u n of
                                    res@(Error _) -> res
                                    OK (n', (c', e', t')) ->
                                      case infer' v n' of
                                        res'@(Error _) -> res'
                                        OK (n'', (c'', e'', t'')) -> 
                                          case mgu $ (t'', (TList t')):goals of
                                            UError u1 u2 -> uError u1 u2
                                            UOK subst -> OK (n''+1,
                                                (
                                                  joinC [subst <.> c', subst <.> c''],
                                                  subst <.> (ConsExp e' e''),
                                                  subst <.> (t'')
                                                )
                                              )
                                            where goals = foldr f [] (domainC c'')
                                                  f = (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x):r else r)) 
infer' (ZipWithExp u v x y w) n = case infer' u n of
                                    res@(Error _) -> res
                                    OK (n1, (c1, e1, t1)) ->
                                      case infer' v n1 of
                                        res1@(Error _) -> res1
                                        OK (n2, (c2, e2, t2)) -> 
                                          case infer' w n2 of
                                            res4@(Error _) -> res4
                                            OK (n3, (c3, e3, t3)) -> 
                                              case mgu $ [(t1,(TList (TVar n3))),(t2,(TList (TVar (n3+1))))]++goals of
                                                UError u1 u2 -> uError u1 u2
                                                UOK subst -> OK (n3+2,
                                                    (
                                                      joinC [subst <.> c | c <- cs],
                                                      subst <.> (ZipWithExp e1 e2 x y e3),
                                                      subst <.> (TList t3)
                                                    )
                                                  )
                                                where goals = concat [aux (cs!!i) (cs!!j) | i <- [0..2], j <- [0..2], i /= j]
                                                      aux c' c'' = foldr (\x -> (\r -> if elem x (domainC c') then (evalC c' x, evalC c'' x):r else r)) [] (domainC c'')
                                                      --c3' = extendC (extendC c3 x (TVar n3)) y (TVar (n3+1))
                                                      cs = [c1,c2,c3]

--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Result (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
