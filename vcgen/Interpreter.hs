module Main where

import Prelude

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import Data.Map
import qualified Data.Set as Set
import qualified GHC.Integer (leInteger) 
import qualified GHC.Integer (gtInteger)


import Tiny.Abs ( Expr(..), BExpr(..), Stmt(..), Ident(..), Decl(..), Formula (..), Binder(..), Invariant (..) )
import Tiny.Lex   ( Token, mkPosToken )
import Tiny.Par   ( pExpr, pBExpr, pStmt, myLexer )
import Tiny.Print ( Print, printTree )
import Tiny.Skel  ()
import Foreign (free)
import Data.Array.Base (bOOL_INDEX)
import Data.Attoparsec.ByteString.Char8 (isDigit)
import qualified Data.Map as Map

mapGet :: (Ord k) => (Map k v) -> k -> v
mapGet map arg = map ! arg

mapSet :: (Ord k) => (Map k v) -> k -> v -> (Map k v)
mapSet map arg val = insert arg val map


type Loc = Integer
type Var = String

type VEnv = Map Var Loc
type Proc = Integer -> Store -> Store
type PEnv = Map Var Proc
data Store = CStore {currMap :: Map Loc Integer, nextLoc :: Loc} deriving Show
type FEnv = Set.Set Formula

{--
===
  data Store = CStore (Map.Map Loc Integer) Loc
  
  CStore :: (Map Loc Integer) -> Loc -> Store
  currMap :: Store -> (Map.Map Loc Integer)
  nextLoc :: Store -> Loc
--}

newloc:: Store -> (Loc, Store)
newloc (CStore map loc) = (loc, CStore map (loc + 1))

getVar:: VEnv -> Store -> Var -> Integer
getVar rhoV sto var =
  let loc = mapGet rhoV var in
    mapGet (currMap sto) loc

setVar:: VEnv -> Store -> Var -> Integer -> Store
setVar rhoV sto var val =
  let loc = mapGet rhoV var in
  let map = mapSet (currMap sto) loc val in
    CStore map (nextLoc sto)

-- Semantics of expressions
eE :: Expr -> VEnv -> Store -> Integer

eE (EPlus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) + (eE exp1 rhoV sto) 
eE (EMinus exp0 exp1) rhoV sto = (eE exp0 rhoV sto) - (eE exp1 rhoV sto)
eE (EMul  exp0 exp1) rhoV sto = (eE exp0 rhoV sto) * (eE exp1 rhoV sto)
eE (EDiv  exp0 exp1) rhoV sto = div (eE exp0 rhoV sto) (eE exp1 rhoV sto)
eE (ENum n) rhoV sto = n
eE (EVar (Ident x)) rhoV sto = getVar rhoV sto x

-- Semantics of boolean expressions
eB :: BExpr -> VEnv -> Store -> Bool

eB (BAnd bexp0 bexp1) rhoV sto = (eB bexp0 rhoV sto) && (eB bexp1 rhoV sto)

eB (BEq exp0 exp1) rhoV sto = (eE exp0 rhoV sto) == (eE exp1 rhoV sto)
eB (BLeq exp0 exp1) rhoV sto = GHC.Integer.leInteger (eE exp0 rhoV sto) (eE exp1 rhoV sto)
eB (BGt exp0 exp1) rhoV sto = GHC.Integer.gtInteger (eE exp0 rhoV sto) (eE exp1 rhoV sto)
{--
  BNot bexp  -> not $ eB bexp st
  BLeq exp0 exp  -> GHC.Integer.leInteger (eE exp0 st) (eE exp st)
  BTrue  -> True
  BFalse -> False
  --}

-- semantics of declarations
iD :: Decl -> PEnv -> VEnv -> Store -> (PEnv, VEnv, Store)

iD (DVar (Ident var) ex) rhoP rhoV sto =  
  let (loc, sto') = newloc sto in
  let val = eE ex rhoV sto in
  let rhoV' = mapSet rhoV var loc in
  let sto'' = setVar rhoV' sto' var val in
    (rhoP, rhoV', sto'')

iD (DProc (Ident p) (Ident x) i) rhoP rhoV sto = 
 let prc n st = case newloc st of
                 (loc, st') -> let rhoV' = mapSet rhoV x loc
                                   rhoP' = mapSet rhoP p prc
                                   st'' = setVar rhoV' st' x n 
                               in iS i rhoP' rhoV' st''
 in (mapSet rhoP p prc, rhoV, sto) 

iD (DProcS (Ident p) (Ident x) _ i) rhoP rhoV sto = 
 let prc n st = case newloc st of
                 (loc, st') -> let rhoV' = mapSet rhoV x loc
                                   rhoP' = mapSet rhoP p prc
                                   st'' = setVar rhoV' st' x n 
                               in iS i rhoP' rhoV' st''
 in (mapSet rhoP p prc, rhoV, sto) 

iD (DSeq d1 d2) rhoP rhoV sto = 
  let (rhoP', rhoV', sto') = iD d1 rhoP rhoV sto in
    iD d2 rhoP' rhoV' sto'

-- Semantics of statements
iS :: Stmt -> PEnv -> VEnv -> Store -> Store

iS (SAssgn (Ident var) expr) rhoP rhoV sto =
  let loc = mapGet rhoV var in
  let val = eE expr rhoV sto in
    setVar rhoV sto var val

iS (SSkip) rhoP rhoV sto = sto

iS (SIf bex i1 i2) rhoP rhoV sto = if eB bex rhoV sto 
                          then iS i1 rhoP rhoV sto
                          else iS i2 rhoP rhoV sto
                          
  -- x :: Store -> Store
iS (SWhile bex i) rhoP rhoV sto = x sto where
    x st = if eB bex rhoV st then x (iS i rhoP rhoV st) else st    
  -- skip the invariant, do as in the while loop
iS (SWhileInv bex _ i) rhoP rhoV sto = x sto where
    x st = if eB bex rhoV st then x (iS i rhoP rhoV st) else st

iS (SSeq i1 i2) rhoP rhoV sto = iS i2 rhoP rhoV (iS i1 rhoP rhoV sto)

iS (SCall (Ident var) ex) rhoP rhoV sto = 
  let val = eE ex rhoV sto in
  let prc = mapGet rhoP var in
    prc val sto 


iS (SBlock dec i) rhoP rhoV sto = 
  let (rhoP', rhoV', sto') = iD dec rhoP rhoV sto in
    iS i rhoP' rhoV' sto'

freeVars :: Expr -> Set.Set Var 
freeVars (EPlus exp0 exp1) =
  Set.union (freeVars exp0) (freeVars exp1)
freeVars (EMinus exp0 exp1) =
  Set.union (freeVars exp0) (freeVars exp1)
freeVars (EMul exp0 exp1) =
  Set.union (freeVars exp0) (freeVars exp1)
freeVars (EDiv exp0 exp1) =
  Set.union (freeVars exp0) (freeVars exp1)
freeVars (ENum _) = Set.empty
freeVars (EVar (Ident x)) = Set.singleton x

suffixNum :: Var -> Integer
suffixNum var = 
  let sfx = reverse . takeWhile isDigit . reverse $ var in
    read sfx :: Integer

maxSuffixNum :: Set.Set Var -> Integer
maxSuffixNum fVars =
  Set.foldl
    (\maxsfx var -> 
      let num = suffixNum var in
        if num > maxsfx then num else maxsfx)
    0 fVars

freshNames :: Set.Set Var -> Set.Set Var -> Map Var Var
freshNames conflicts fVars = 
  let maxsfx = maxSuffixNum fVars in
  let (fnames, no) = Set.foldl (\(res :: Map Var Var, no) var -> 
                                  let newVar = var ++ (show no) in
                                  (insert var newVar res, no + 1))
                                (empty, maxsfx+1) conflicts in
  fnames
    
renameVars :: Expr -> Map Var Var -> Expr
renameVars (EPlus exp0 exp1) c_fnames =
  EPlus (renameVars exp0 c_fnames) (renameVars exp1 c_fnames)
renameVars (EMinus exp0 exp1) c_fnames =
  EMinus (renameVars exp0 c_fnames) (renameVars exp1 c_fnames)
renameVars (EMul exp0 exp1) c_fnames =
  EMul (renameVars exp0 c_fnames) (renameVars exp1 c_fnames)
renameVars (EDiv exp0 exp1) c_fnames =
  EDiv (renameVars exp0 c_fnames) (renameVars exp1 c_fnames)
renameVars (ENum n) _ = ENum n
renameVars (EVar (Ident x)) c_fnames =
  case Data.Map.lookup x c_fnames of
    Just newVar -> EVar (Ident newVar)
    Nothing     -> EVar (Ident x)

renameBVars :: BExpr -> Map Var Var -> BExpr
renameBVars (BAnd b0 b1) c_fnames =
  BAnd (renameBVars b0 c_fnames) (renameBVars b1 c_fnames)
renameBVars (BEq e0 e1) c_fnames =
  BEq (renameVars e0 c_fnames) (renameVars e1 c_fnames)
renameBVars (BLeq e0 e1) c_fnames =
  BLeq (renameVars e0 c_fnames) (renameVars e1 c_fnames)
renameBVars (BGt e0 e1) c_fnames =
  BGt (renameVars e0 c_fnames) (renameVars e1 c_fnames)
renameBVars (BNot b) c_fnames =
  BNot (renameBVars b c_fnames)
renameBVars BTrue _ = BTrue
renameBVars BFalse _ = BFalse

renameBinders :: [Binder] -> Map Var Var -> [Binder]
renameBinders [] _ = []
renameBinders (ForallB (Ident x):bs) c_fnames =
  let newVar = case Data.Map.lookup x c_fnames of
                 Just newVar -> Ident newVar
                 Nothing     -> Ident x in
  ForallB newVar : renameBinders bs c_fnames
renameBinders (ExistsB (Ident x):bs) c_fnames =
  let newVar = case Data.Map.lookup x c_fnames of
                 Just newVar -> Ident newVar
                 Nothing     -> Ident x in  
  ExistsB newVar : renameBinders bs c_fnames

alphaConv :: Formula -> Set.Set Var -> Formula
alphaConv (FormulaB bex) fVars = FormulaB bex
alphaConv (FormulaQI binders bex1 bex2) fVars =
  let binderset = Set.fromList [b | ForallB (Ident b) <- binders] `Set.union` 
                        Set.fromList [b | ExistsB (Ident b) <- binders] in  
  let conflicts = Set.intersection fVars binderset in
  let c_fnames = freshNames conflicts fVars in
  let bex1' = renameBVars bex1 c_fnames in
  let bex2' = renameBVarsF bex2 c_fnames in
  let binders' = renameBinders binders c_fnames in
    FormulaQI binders' bex1' bex2'
alphaConv (FormulaQS binders bex) fVars =
  let binderset = Set.fromList [b | ForallB (Ident b) <- binders] `Set.union` 
                        Set.fromList [b | ExistsB (Ident b) <- binders] in  
  let conflicts = Set.intersection fVars binderset in
  let c_fnames = freshNames conflicts fVars in
  let bex' = renameBVars bex c_fnames in
  let binders' = renameBinders binders c_fnames in
    FormulaQS binders' bex'
alphaConv (FormulaAnd f1 f2) fVars =
  let f1' = alphaConv f1 fVars in
  let f2' = alphaConv f2 fVars in
    FormulaAnd f1' f2'
alphaConv (FormulaOr f1 f2) fVars =
  let f1' = alphaConv f1 fVars in
  let f2' = alphaConv f2 fVars in
    FormulaOr f1' f2'

renameBVarsF :: Formula -> Map Var Var -> Formula
renameBVarsF (FormulaB bex) c_fnames = FormulaB (renameBVars bex c_fnames)
renameBVarsF (FormulaQI binders bex1 bex2) c_fnames =
  let binderset = Set.fromList [b | ForallB (Ident b) <- binders] `Set.union` 
                        Set.fromList [b | ExistsB (Ident b) <- binders] in
  let conflicts = Set.intersection (Set.fromList (Map.elems c_fnames)) binderset in 
  let c_names = freshNames conflicts (Set.fromList (Map.elems c_fnames)) in
  let bex1' = renameBVars (renameBVars bex1 c_names) c_fnames in
  let bex2' = renameBVarsF (renameBVarsF bex2 c_names) c_fnames in
  let binders' = renameBinders binders c_names in
    FormulaQI binders' bex1' bex2'
renameBVarsF (FormulaQS binders bex) c_fnames =
  let binderset = Set.fromList [b | ForallB (Ident b) <- binders] `Set.union` 
                        Set.fromList [b | ExistsB (Ident b) <- binders] in
  let conflicts = Set.intersection (Set.fromList (Map.elems c_fnames)) binderset in 
  let c_names = freshNames conflicts (Set.fromList (Map.elems c_fnames)) in
  let bex' = renameBVars (renameBVars bex c_names) c_fnames in
  let binders' = renameBinders binders c_names in
    FormulaQS binders' bex'
renameBVarsF (FormulaAnd f1 f2) c_fnames =
  let f1' = renameBVarsF f1 c_fnames in
  let f2' = renameBVarsF f2 c_fnames in
    FormulaAnd f1' f2'
renameBVarsF (FormulaOr f1 f2) c_fnames =
  let f1' = renameBVarsF f1 c_fnames in
  let f2' = renameBVarsF f2 c_fnames in
    FormulaOr f1' f2'


substF :: Formula -> Var -> Expr -> Formula
substF (FormulaB bex) var expr = FormulaB (substB bex var expr)
substF (FormulaQI binders bex1 bex2) var expr =
  let fVars = freeVars expr in
  let nform = alphaConv (FormulaQI binders bex1 bex2) fVars in
  case nform of
    FormulaQI binders' bex1' bex2' -> 
      let bex1'' = substB bex1' var expr in 
      let bex2'' = substF bex2' var expr in 
        FormulaQI binders' bex1'' bex2''
    _ -> error "Unknown formula type in substF"
substF (FormulaQS binders bex) var expr =
  let fVars = freeVars expr in
  let nform = alphaConv (FormulaQS binders bex) fVars in
  case nform of
    FormulaQS binders' bex' -> 
      let bex'' = substB bex' var expr in 
        FormulaQS binders' bex''
    _ -> error "Unknown formula type in substF"
substF (FormulaAnd f1 f2) var expr =
  let f1' = substF f1 var expr in
  let f2' = substF f2 var expr in
    FormulaAnd f1' f2'
substF (FormulaOr f1 f2) var expr =
  let f1' = substF f1 var expr in
  let f2' = substF f2 var expr in
    FormulaOr f1' f2' 

substB :: BExpr -> Var -> Expr -> BExpr
substB (BAnd bex0 bex1) var expr =
  BAnd (substB bex0 var expr) (substB bex1 var expr)
substB (BEq e0 e1) var expr =
  BEq (substE e0 var expr) (substE e1 var expr)
substB (BLeq e0 e1) var expr =
  BLeq (substE e0 var expr) (substE e1 var expr)
substB (BGt e0 e1) var expr =
  BGt (substE e0 var expr) (substE e1 var expr)
substB (BNot bex) var expr =
  BNot (substB bex var expr)
substB BTrue _ _ = BTrue
substB BFalse _ _ = BFalse

substE :: Expr -> Var -> Expr -> Expr
substE (EPlus exp0 exp1) var expr =
  EPlus (substE exp0 var expr) (substE exp1 var expr)
substE (EMinus exp0 exp1) var expr =
  EMinus (substE exp0 var expr) (substE exp1 var expr)
substE (EMul exp0 exp1) var expr =
  EMul (substE exp0 var expr) (substE exp1 var expr)
substE (EDiv exp0 exp1) var expr =
  EDiv (substE exp0 var expr) (substE exp1 var expr)
substE (ENum n) _ _ = ENum n
substE (EVar (Ident x)) var expr =
  if x == var then expr else EVar (Ident x)


-- vcGen statements
vcGen :: Stmt -> PEnv -> FEnv -> Formula -> (FEnv, Formula)
vcGen (SAssgn (Ident var) expr) rhoP fEnv post =
  let pre = substF post var expr in -- post[var := expr]
    (fEnv, pre)
vcGen (SSkip) rhoP fEnv post = (fEnv, post)
vcGen (SIf bex i1 i2) rhoP fEnv post =
  let (fEnv1, pre1) = vcGen i1 rhoP fEnv post in
  let (fEnv2, pre2) = vcGen i2 rhoP fEnv post in
  let pre = FormulaAnd (FormulaQI [] bex pre1)
                       (FormulaQI [] (BNot bex) pre2) in
  (Set.union fEnv1 fEnv2, pre)
  -- The invariant for while loop with no invariant is BTrue
vcGen (SWhile bex i) rhoP fEnv post = 
  vcGen (SWhileInv bex [Inv (FormulaB BTrue)] i) rhoP fEnv post
vcGen (SWhileInv bex invs i) rhoP fEnv post =
  let combInv = Prelude.foldl (\acc (Inv f) -> FormulaAnd acc f) (FormulaB BTrue) invs in
  let fEnv' = Prelude.foldl (\accEnv (Inv f) -> 
                      let (fEnv', f') = vcGen i rhoP accEnv f in
                      Set.insert f' fEnv') 
                    fEnv 
                    invs in
  (fEnv', combInv)
vcGen (SSeq i1 i2) rhoP fEnv post =
  let (fEnv1, pre1) = vcGen i1 rhoP fEnv post in
  let (fEnv2, pre2) = vcGen i2 rhoP fEnv1 pre1 in
  (fEnv2, pre2)
vcGen (SCall (Ident var) expr) rhoP fEnv post =
  (fEnv, post) -- TODO: this is not correct, we need to handle the procedure call differently
vcGen (SBlock dec i) rhoP fEnv post =
  let (rhoP', rhoV', sto') = iD dec rhoP rhoV0 sto0 in
  let (fEnv', pre) = vcGen i rhoP' fEnv post in
  (fEnv', pre)  

main :: IO ()
main = do
    getContents >>= compute
    putStrLn ""

rhoP0:: PEnv
rhoP0 = fromList []

rhoV0:: VEnv
rhoV0 = fromList [("x", 0), ("y", 1), ("z", 2)]

sto0:: Store
sto0 = CStore (fromList [(0, 3), (1, 2), (2, 3)]) 3

compute s =
    case pStmt (myLexer s) of
        Left err -> do
            putStrLn "\nParse              Failed...\n"
            putStrLn err
            exitFailure
        Right e -> do
            putStrLn "\nParse Successful!"
            putStrLn $ show (iS e rhoP0 rhoV0 sto0)
