{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-methods -Wno-partial-type-signatures #-}

{-
  Generators and properties for SystemF
-}

module SystemFGen where

import Control.Monad
import Control.Monad.State (StateT, evalStateT, get, liftIO, put, runStateT)
import Data.Data hiding (typeOf)
import Data.IORef (IORef, modifyIORef, newIORef, readIORef, writeIORef)
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ord (comparing)
import qualified Data.Set as S
import System.IO.Unsafe (unsafePerformIO)
import System.Microtimer (formatSeconds, time_)
import System.Timeout (timeout)
import SystemF
import Test.QuickCheck
import Text.Printf

------------------------------------------
-- GENERATION
------------------------------------------

genType :: Int -> Gen Type
genType freeTypeVar = sized (arb freeTypeVar)
  where
    arb ftv 0 = elements $ Base : (TVar <$> [0 .. ftv -1])
    arb ftv n =
      oneof
        [ arb ftv 0,
          (:->) <$> arb ftv (n `div` 6) <*> arb ftv (n `div` 4),
          ForAll <$> arb (ftv + 1) (n -1)
        ]

genExpr :: Gen (Maybe Expr)
genExpr =
  sized $ \n -> do t <- genType 0; arb 0 [] t n
  where
    arb :: Int -> [Type] -> Type -> Int -> Gen (Maybe Expr)
    arb ftv c t 0 =
      oneofMaybe $
        [return $ Just Con | t == Base]
          ++
          -- [ return $ Just BTrue | t == TBool ] ++
          -- [ return $ Just BFalse | t == TBool ] ++
          [return $ Just $ Var i | (i, t') <- zip [0 ..] c, t == t']
          ++ [fmap (Lam t1) <$> arb ftv (t1 : c) t2 0 | (t1 :-> t2) <- [t]]
          ++ [fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t]]
    arb ftv c t n =
      frequency $
        [(6, arb ftv c t 0)]
          ++ [(8, fmap (Lam t1) <$> arb ftv (t1 : c) t2 (n -1)) | (t1 :-> t2) <- [t]]
          ++ [(4, fmap TLam <$> arb (ftv + 1) (map (liftType 0) c) t1 (n -1)) | (ForAll t1) <- [t]]
          ++ [ ( 8,
                 do
                   t2 <- do
                     arbT <- resize 10 $ genType ftv -- for now; should be bigger?
                     elements (nub $ michal c t ++ [arbT])
                   me1 <- arb ftv c (t2 :-> t) (n `div` 2)
                   me2 <- arb ftv c t2 (n `div` 2)
                   return $ (:@:) <$> me1 <*> me2
               )
             ]
          ++ [ ( 4,
                 do
                   t1t2 <- genT1T2 t
                   case t1t2 of
                     Just (t1, t2) -> do
                       me1 <- arb ftv c t1 (n - 1)
                       return $ TApp <$> me1 <*> return t2
                     Nothing -> return Nothing --  ++
                     -- [ (0, do e1 <- arb ftv c TBool (n `div` 3)
                     --          e2 <- arb ftv c t (n `div` 3)
                     --          e3 <- arb ftv c t (n `div` 3)
                     --          return $ Cond <$> e1 <*> e2 <*> e3) ]
               )
             ]

michal :: [Type] -> Type -> [Type]
michal c t =
  [ t' | varType <- c, t' <- aux varType ]
  where
    aux (t1 :-> t2)
      | t == t2 = [t1]
      | t /= t2 = aux t2
    aux _ = []

-- Check if a type has any type variables.
-- TODO: replace with "isClosed"
hasTVars :: Type -> Bool
hasTVars (TVar _) = True
hasTVars (t1 :-> t2) = hasTVars t1 || hasTVars t2
hasTVars (ForAll t) = hasTVars t
hasTVars TBool = False
hasTVars Base = False

isClosed :: Type -> Bool
isClosed = isClosed' 0
  where
    isClosed' :: Int -> Type -> Bool
    isClosed' tc (TVar x) = x < tc
    isClosed' tc (t1 :-> t2) = isClosed' tc t1 && isClosed' tc t2
    isClosed' tc (ForAll t) = isClosed' (tc + 1) t
    isClosed' _ TBool = True
    isClosed' _ Base = True

-- Randomly fetch a subterm of a type
fetchSubType :: Type -> Gen (Maybe Type)
fetchSubType t =
  oneofMaybe $
    [return (Just t) | isClosed t]
      ++ [fetchSubType t1 | (t1 :-> _) <- [t]]
      ++ [fetchSubType t2 | (_ :-> t2) <- [t]]
      ++ [fetchSubType t' | (ForAll t') <- [t]]

oneofMaybe :: [Gen (Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe gs = oneof gs

-- "Replace (some occurrences of) closed type s in type t by (TVar n)"
replaceSubType :: Int -> Type -> Type -> Gen Type
replaceSubType n s t =
  oneof $
    [return t]
      ++ [return $ TVar n | s == t]
      ++ [do t1' <- replaceSubType n s t1;
             t2' <- replaceSubType n s t2;
             return $ t1' :-> t2' | (t1 :-> t2) <- [t]]
      ++ [do t'' <- replaceSubType (n + 1) s t';
             return $ ForAll t'' | (ForAll t') <- [t], t' == s]

-- Generate t1 t2 such that t1{0:=t2} = t
genT1T2 :: Type -> Gen (Maybe (Type, Type))
genT1T2 t = do
  let t' = liftType 0 t
  t2 <- fetchSubType t'
  case t2 of
    Just t2' -> do
      t1 <- replaceSubType 0 t2' t'
      return $ Just (ForAll t1, t2')
    Nothing -> return Nothing

------------------------------------------
-- SHRINKING
------------------------------------------

shrinkType :: Type -> [Type]
shrinkType Base = []
shrinkType TBool = [Base]
shrinkType (t1 :-> t2) =
  Base :
  t1 :
  t2 :
  [t1' :-> t2 | t1' <- shrinkType t1]
    ++ [t1 :-> t2' | t2' <- shrinkType t2]
shrinkType (TVar n) = Base : [TVar n' | n' <- shrink n]
shrinkType (ForAll t) = Base : t : [ForAll t' | t' <- shrinkType t]

shrinkExpr' Con = []
shrinkExpr' (Var n) = Con : [Var n' | n' <- shrink n]
shrinkExpr' (Lam t e) =
  Con :
  e :
  [Lam t' e | t' <- shrinkType t]
    ++ [Lam t e' | e' <- shrinkExpr' e]
shrinkExpr' (e1 :@: e2) = Con : e1 : e2 : [e1' :@: e2 | e1' <- shrinkExpr' e1] ++ [e1 :@: e2' | e2' <- shrinkExpr' e2]
shrinkExpr' (Cond e1 e2 e3) = Con : e1 : e2 : e3 : [Cond e1' e2 e3 | e1' <- shrinkExpr' e1] ++ [Cond e1 e2' e3 | e2' <- shrinkExpr' e2] ++ [Cond e1 e2 e3' | e3' <- shrinkExpr' e3]
shrinkExpr' BTrue = [Con]
shrinkExpr' BFalse = [Con, BTrue]
shrinkExpr' (TLam e) = Con : e : [TLam e' | e' <- shrinkExpr' e]
shrinkExpr' (TApp e t) = Con : e : [TApp e' t | e' <- shrinkExpr' e] ++ [TApp e t' | t' <- shrinkType t]

shrinkExpr :: _ => Expr -> [Expr]
shrinkExpr e =
  [e' | e' <- shrinkExpr' e, wellTyped e']
    ++ [e'' | e' <- shrinkExpr' e, e'' <- shrinkExpr' e', wellTyped e'']
    ++ [e' | Just e' <- [step e], size e' < size e] --, typeOf e' = typeOf e]

------------------------------------------
-- PROPERTIES
------------------------------------------

data PropType
  = PropStrongNormalization
  | PropStrongNormalizationStep
  | PropEvalMakesProgress
  | PropStepMakesProgress
  | PropEvalShort
  | PropBigSmallStep
  | PropHnfNoStep
  | PropEvalNoMoreSteps
  | PropGenWellTyped
  | PropPreservation
  | PropParallelPreservation
  | PropPreservationMulti
  | PropProgress
  | PropEvalSame
  | PropPSame
  | PropEvalStepSame
  | PropTest
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Data, Typeable)

instance Testable (Either String ()) where
  property (Left s) = whenFail (putStrLn s) False
  property (Right _) = property True

propOfPropType :: _ => PropType -> (Expr -> Property)
propOfPropType PropStrongNormalization e = property $ prop_normalform e
propOfPropType PropStrongNormalizationStep e = property $ prop_normalform' e
propOfPropType PropEvalMakesProgress e = property $ prop_evalMakesProgress e
propOfPropType PropStepMakesProgress e = property $ prop_stepMakesProgress e
propOfPropType PropEvalShort e = property $ prop_evalShort e
propOfPropType PropBigSmallStep e = property $ prop_bigSmallStep e
propOfPropType PropHnfNoStep e = property $ prop_hnfNoStep e
propOfPropType PropEvalNoMoreSteps e = property $ prop_evalNoMoreSteps e
propOfPropType PropGenWellTyped e = property $ prop_wellTyped e
propOfPropType PropPreservation e = prop_preservation e
propOfPropType PropParallelPreservation e = prop_ppreservation e
propOfPropType PropPreservationMulti e = prop_preservation_multi 0 20 e
propOfPropType PropProgress e = property $ prop_progress e
propOfPropType PropEvalSame e = property $ prop_evalSame e
propOfPropType PropPSame e = property $ prop_PSame e
propOfPropType PropEvalStepSame e = property $ prop_evalStepSame e
propOfPropType PropTest e = property $ prop_test e

bToE :: (Show a) => a -> Bool -> Either String ()
bToE _ True = Right ()
bToE x False = Left (show x)

prop_normalform e = isHnf . last . eval $ e

prop_normalform' e = isHnf . last . eval' $ e

prop_wellTyped e = wellTyped e

prop_evalMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where
    es = eval e

prop_stepMakesProgress e =
  and (zipWith (/=) es $ drop 1 es)
  where
    es = eval' e

prop_evalShort e =
  length (eval e) < 100

prop_bigSmallStep e =
  let es = eval e
      es' = eval' e
   in last es == last es'

prop_hnfNoStep e =
  (not $ isHnf e) || (isNothing $ step e)

prop_evalNoMoreSteps e =
  isNothing $ step (last $ eval e)

prop_preservation e =
  case step e of
    Just s ->
      whenFail
        ( do
            putStrLn $ "Original:  " ++ show e
            putStrLn $ "With Type: " ++ show (typeOf e)
            putStrLn $ "Steps To:  " ++ show s
            putStrLn $ "With Type: " ++ show (typeOf s)
        )
        (typeOf e == typeOf s)
    Nothing -> discard

prop_ppreservation e =
  let s = pstep e
   in whenFail
        ( do
            putStrLn $ "Original:  " ++ show e
            putStrLn $ "With Type: " ++ show (typeOf e)
            putStrLn $ "Steps To:  " ++ show s
            putStrLn $ "With Type: " ++ show (typeOf s)
        )
        (typeOf e == typeOf s)

prop_preservation_multi n max e =
  if n == max
    then collect n True
    else case step e of
      Just s ->
        whenFail
          ( do
              putStrLn $ "Original:  " ++ show e
              putStrLn $ "With Type: " ++ show (typeOf e)
              putStrLn $ "Steps To:  " ++ show s
              putStrLn $ "With Type: " ++ show (typeOf s)
          )
          $ if typeOf e == typeOf s
            then prop_preservation_multi (n + 1) max s
            else property False
      Nothing -> collect n True

prop_progress e = isHnf e || canStep e

prop_evalSame e =
  take 100 (eval e) == take 100 (eval e)

prop_pevalSame e =
  (peval e) == peval e

prop_PSame e =
  (pstep e) == pstep e

prop_evalStepSame e =
  take 100 (eval' e) == take 100 (eval' e)

prop_test e =
  case e of
    (Lam _ (Lam _ _)) :@: (Lam _ _) -> False
    Lam _ e -> prop_test e
    TLam e -> prop_test e
    e1 :@: e2 -> prop_test e1 && prop_test e2
    TApp e1 _ -> prop_test e1
    Cond e1 e2 e3 -> prop_test e1 && prop_test e2 && prop_test e3
    _ -> True

propTimeout :: Int -> (Expr -> Property) -> Maybe Expr -> Property
propTimeout microseconds p Nothing = discard
propTimeout microseconds p (Just e) =
  unsafePerformIO $ do
    res <- timeout microseconds $ return $! p e
    case res of
      Just x -> return x
      Nothing -> discard

experiments :: IO ()
experiments = do
  quickCheckWith stdArgs{maxSuccess=100000} $
    forAll genExpr $ propTimeout 10000 prop_ppreservation
--  let t = 100
--  let setups = Random : [Setup k f | k <- [2], f <- [30]]
--  let mutants = [SubstInTypeNoDecr]
--  let time = False
--  let sep = ";"
--  let initialCov = M.empty :: M.Map (Description SFC) Int
-- 
--  putStrLn . intercalate sep $ "" : (show <$> setups)
--  forM_ mutants $ \mutant -> do
--    putStr $ show mutant ++ sep
--    means <- forM setups $ \setup ->
--      let ?mutant = mutant
--       in if time
--            then formatSeconds . fst <$> trials t (runSetupTime initialCov setup)
--            else formatMeanCount . fst <$> trials t (runSetupCount initialCov setup)
--    putStrLn $ intercalate sep means
