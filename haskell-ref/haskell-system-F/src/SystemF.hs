{-# LANGUAGE DeriveDataTypeable, PartialTypeSignatures, ImplicitParams, FlexibleInstances, DeriveGeneric, TupleSections #-}
{-# options_ghc -Wno-missing-methods -Wno-partial-type-signatures #-}
module SystemF ( Type(..)
               , Expr(..)
               , wellFormedType
               , typeOf
               , subst
               , liftType
               , eval
               , eval'
               , peval
               , pstep
               , step
               , isHnf
               , canStep
               , size
               , wellTyped
               , lambdas
               , vars
               ) where

import Debug.Trace

import Control.Monad

import qualified Test.QuickCheck

import Data.List
import Data.Maybe
import Data.Typeable hiding (typeOf)
import Data.Data hiding (typeOf)

import GHC.Generics
import Control.DeepSeq

import Text.Printf

------------------------------------------
-- DEFINITIONS
------------------------------------------

data Type = Base | TBool | Type :-> Type | TVar Int | ForAll Type
  deriving (Eq, Ord, Generic)

data Expr = Con | Var Int | Lam Type Expr | Expr :@: Expr
          | Cond Expr Expr Expr | BTrue | BFalse | TLam Expr | TApp Expr Type
  deriving (Eq, Ord, Generic)

instance NFData Type
instance NFData Expr

------------------------------------------
-- PRINTING
------------------------------------------

data Precedence = Outer | App | Inner
  deriving (Eq, Ord)

instance Show Type where
  show t = showType' Outer t

showType' _ Base        = "()"
showType' _ TBool       = "B"
showType' _ (TVar n)    = show n
showType' p (ForAll t)  = parens p Outer $ "forall " ++ showType' Outer t
showType' p (t1 :-> t2) = parens p App $ showType' Inner t1 ++ "->" ++ showType' App t2

instance Show Expr where
  show e = show' Outer e

show' _ Con             = "#"
show' _ BTrue           = "T"
show' _ BFalse          = "F"
show' _ (Var x)         = show x
show' p (Lam t e)       = parens p Outer $ "lam " ++ show t ++ ". " ++ show' Outer e
show' p (TLam e)        = parens p Outer $ "Lam. " ++ show' Outer e
show' p (e1 :@: e2)     = parens p App $ show' App e1 ++ " " ++ show' Inner e2
show' p (TApp e1 t2)    = parens p App $ show' App e1 ++ " [" ++ showType' Outer t2 ++ "]"
show' p (Cond e1 e2 e3) =
  parens p Inner $ "if " ++ show' Outer e1 ++ " then " ++ show' Outer e2
                   ++ " else " ++ show' Outer e3

parens outer inner s = if outer > inner then "(" ++ s ++ ")" else s

------------------------------------------
-- TYPECHECKING
------------------------------------------

-- | I can't believe we had to write this
nth :: Int -> [a] -> Maybe a
nth _ [] = Nothing
nth 0 (a:as) = Just a
nth n (a:as) = nth (n-1) as

wellFormedType :: Int -> Type -> Bool
wellFormedType ftv Base = True
wellFormedType ftv TBool = True
wellFormedType ftv (TVar n) = n < ftv && n>=0
wellFormedType ftv (t1 :-> t2) = wellFormedType ftv t1 && wellFormedType ftv t2
wellFormedType ftv (ForAll t) = wellFormedType (ftv+1) t

typeOf' :: Int -> [Type] -> Expr -> Maybe Type
typeOf' ftv _ Con         = Just Base
typeOf' ftv _ BTrue       = Just TBool
typeOf' ftv _ BFalse      = Just TBool
typeOf' ftv c (Lam t e)   = guard (wellFormedType ftv t) >>
                       (t :->) <$> typeOf' ftv (t:c) e
typeOf' ftv c (TLam e)    = ForAll <$> typeOf' (ftv+1) (map (liftType 0) c) e
typeOf' ftv c (Var n)     = nth n c
typeOf' ftv c (TApp e t)  = do
  t2 <- typeOf' ftv c e
  guard $ wellFormedType ftv t
  case t2 of
    ForAll t2' -> Just $ substInType 0 t t2'
    _ -> Nothing
typeOf' ftv c (e1 :@: e2) = do
  t12 <- typeOf' ftv c e1
  t1' <- typeOf' ftv c e2
  case t12 of
    t1 :-> t2 -> do
      guard (t1 == t1')
      Just t2
    _ -> Nothing
typeOf' ftv c (Cond e1 e2 e3) = do
  t1 <- typeOf' ftv c e1
  t2 <- typeOf' ftv c e2
  t3 <- typeOf' ftv c e3
  guard (t1 == TBool && t2 == t3)
  Just t2

typeOf :: Expr -> Maybe Type
typeOf = typeOf' 0 []

------------------------------------------
-- SUBSTITUTION
------------------------------------------

subst :: Int -> Expr -> Expr -> Expr
subst n s Con    = Con
subst n s BTrue  = BTrue
subst n s BFalse = BFalse
subst n s (Var x)
  | x == n = s
  | x > n = Var $ x-1
  | otherwise = Var x
subst n s (Lam t e) = Lam t $ subst (n+1) (lift 0 s) e
  where lift n Con = Con
        lift n BTrue = BTrue
        lift n BFalse = BFalse
        lift n (Var x) = Var (if x < n then x else x + 1) 
        lift n (Lam t e) = Lam t $ lift (n+1) e
        lift n (TLam e) = TLam (lift n e)
        lift n (e1:@:e2) = lift n e1 :@: lift n e2
        lift n (TApp e1 t2) = TApp (lift n e1) t2
        lift n (Cond e1 e2 e3) = Cond (lift n e1) (lift n e2) (lift n e3)
subst n s (TLam e)        = TLam $ subst n (liftTypes 0 s) e
subst n s (e1 :@: e2)     = subst n s e1 :@: subst n s e2
subst n s (TApp e1 t2)    = TApp (subst n s e1) t2
subst n s (Cond e1 e2 e3) = Cond (subst n s e1) (subst n s e2) (subst n s e3)

-- Increase type annotations above n
liftTypes n Con = Con
liftTypes n BTrue = BTrue
liftTypes n BFalse = BFalse
liftTypes n (Var x) = Var x
liftTypes n (Lam t e) = Lam (liftType n t) $ liftTypes n e
liftTypes n (TLam e) = TLam $ liftTypes (n+1) e
liftTypes n (e1:@:e2) = liftTypes n e1 :@: liftTypes n e2
liftTypes n (TApp e1 t2) = TApp (liftTypes n e1) (liftType n t2)
liftTypes n (Cond e1 e2 e3) = Cond (liftTypes n e1) (liftTypes n e2) (liftTypes n e3)


-- Increase (by one) all indices above n in t
liftType :: Int -> Type -> Type
liftType n (TVar x)    = TVar $ (if x < n then x else x + 1)
liftType n (ForAll x)  = ForAll $ liftType (n+1) x
liftType n (t1 :-> t2) = liftType n t1 :-> liftType n t2
liftType _ x           = x

substInType :: Int -> Type -> Type -> Type
substInType n s (TVar x)
  | x == n    = s
  | (x > n)   = TVar $ (x-1)
  | otherwise = TVar x
substInType n s (ForAll e)  =
  ForAll $ substInType (n+1) (liftType 0 s) e
substInType n s (t1 :-> t2) = substInType n s t1 :-> substInType n s t2
substInType _ _ x           = x

tSubst :: Int -> Type -> Expr -> Expr
tSubst n s (TLam e)        = TLam $ tSubst (n+1) (liftType 0 s) e
tSubst n s (TApp e t)      = TApp (tSubst n s e) (substInType n s t)
tSubst n s (Lam t e)       = Lam (substInType n s t) (tSubst n s e)
tSubst n s (e1 :@: e2)     = tSubst n s e1 :@: tSubst n s e2
tSubst n s (Cond e1 e2 e3) = Cond (tSubst n s e1) (tSubst n s e2) (tSubst n s e3)
tSubst n t x               = x

------------------------------------------
-- BIG STEP EVALUATION
------------------------------------------

eval :: Expr -> [Expr]
eval (e1 :@: e2) =
  let results = eval e1 in
  case last results of
    Lam t body -> map (:@: e2) results ++ eval (subst 0 e2 body)
    _ -> map (:@: e2) results
eval (TApp e t) =
  let results = eval e in
  case last results of
    TLam body -> map (`TApp` t) results ++ eval (tSubst 0 t body)
    _ -> map (`TApp` t) results
eval (Cond e1 e2 e3) =
  let results = eval e1 in
  let prefix = map (\e -> Cond e e2 e3) results in
  case last results of
    BTrue -> prefix ++ (eval e2)
    BFalse -> prefix ++ eval e3
    _ -> prefix
eval e = [e]

------------------------------------------
-- SINGLE STEP EVALUATION
------------------------------------------

-- | Single step evaluation; returns Nothing if a step can not be taken.
step :: _ => Expr -> Maybe Expr
step (e1 :@: e2) =
  case e1 of
    Lam t body ->
           return $ (subst 0 e2 body)
    _ -> case step e1 of
           Just e1' -> Just (e1' :@: e2)
           Nothing  -> Nothing
step (TApp e1 t) =
  case e1 of
    TLam body -> return $ (tSubst 0 t body) 
    _ -> case step e1 of
           Just e1' -> Just (TApp e1' t)
           Nothing  -> Nothing
step (Cond e1 e2 e3) =
  case e1 of
    BTrue -> return e2
    BFalse -> return e3 
    _ -> do e1' <- step e1; return $ Cond e1' e2 e3
step _ = Nothing

eval' :: _ => Expr -> [Expr]
eval' e =
  case step e of
    Just e' -> e : eval' e'
    Nothing -> [e]

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = fmap fromJust . takeWhile isJust

------------------------------------------
-- PARALLEL REDUCTION
------------------------------------------

pstep :: _ => Expr -> Expr
pstep (Lam t e1) =
  let e1' = pstep e1 in
   Lam t e1'
pstep (e1 :@: e2) =
  let e1' = pstep e1 in
  let e2' = pstep e2 in
  case e1' of
    Lam t body -> subst 0 e2' body
    _ ->  e1' :@: e2'
pstep (TLam e1) =
  let e1' = pstep e1 in
   TLam e1'
pstep (TApp e1 t) =
  let e1' = pstep e1 in
  case e1' of
    TLam body -> (tSubst 0 t body) 
    _ ->  TApp e1' t
pstep (Cond e1 e2 e3) =
  let e1' = pstep e1 in
  let e2' = pstep e2 in
  let e3' = pstep e3 in
  case e1' of
    BTrue -> e2'
    BFalse -> e3'
    _ -> Cond e1' e2' e3'
pstep e = e

peval :: _ => Expr -> Expr
peval e =
  let e' = pstep e
  in if e' == e then e else peval e'

------------------------------------------
-- LAMBDA TERM UTILITIES
------------------------------------------

isHnf :: _ => Expr -> Bool
isHnf (Cond _ _ _) = False   -- mut HnfForgetCond False True
isHnf (_ :@: _) = False
isHnf (TApp _ _) = False     -- mut HnfForgetTApp False True
isHnf _ = True

wellTyped :: Expr -> Bool
wellTyped = isJust . typeOf

canStep :: _ => Expr -> Bool
canStep = isJust . step

size :: Expr -> Int
size Con             = 1
size BTrue           = 1
size BFalse          = 1
size (Var _)         = 1
size (Lam _ e)       = 1 + size e
size (e1 :@: e2)     = 1 + size e1 + size e2
size (Cond e1 e2 e3) = 1 + size e1 + size e2 + size e3
size (TApp e t)      = 1 + size e
size (TLam e)        = 1 + size e

vars :: Expr -> [Int]
vars Con             = []
vars BTrue           = []
vars BFalse          = []
vars (Var x)         = [x]
vars (Lam _ e)       = vars e
vars (e1 :@: e2)     = vars e1 ++ vars e2
vars (Cond e1 e2 e3) = vars e1 ++ vars e2 ++ vars e3
vars (TApp e t) = vars e
vars (TLam e)   = vars e

lambdas :: Expr -> Int
lambdas Con             = 0
lambdas BTrue           = 0
lambdas BFalse          = 0
lambdas (Var x)         = 0
lambdas (Lam _ e)       = lambdas e + 1
lambdas (e1 :@: e2)     = lambdas e1 + lambdas e2
lambdas (Cond e1 e2 e3) = lambdas e1 + lambdas e2 + lambdas e3
lambdas (TApp e t) = lambdas e
lambdas (TLam e)   = lambdas e

tlambdas :: Expr -> Int
tlambdas Con             = 0
tlambdas BTrue           = 0
tlambdas BFalse          = 0
tlambdas (Var x)         = 0
tlambdas (Lam _ e)       = tlambdas e
tlambdas (e1 :@: e2)     = tlambdas e1 + tlambdas e2
tlambdas (Cond e1 e2 e3) = tlambdas e1 + tlambdas e2 + tlambdas e3
tlambdas (TApp e t) = tlambdas e
tlambdas (TLam e)   = tlambdas e + 1

avgVarUses :: Expr -> Double
avgVarUses e = fromIntegral (length $ vars e) / fromIntegral (lambdas e)
