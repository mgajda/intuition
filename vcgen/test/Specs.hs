import Test.Tasty
import Test.Tasty.HUnit
import Data.Map as Map
import Data.Set as Set
import Control.Exception (evaluate, SomeException, catch)
import Logic (getVar, freeVars, freeVarsB, freeVarsD, freeVarsF, VEnv, Store(CStore))

import AbsTiny ( Expr(..), BExpr(..), Stmt(..), SpecEl(..), Ident(..), Decl(..), FormulaD (..), Formula (..), Binder(..), Invariant (..) )
import Foreign (free)

main :: IO ()
main = defaultMain tests

catchSomeEx :: SomeException -> IO ()
catchSomeEx _ = return ()



getVarTests :: TestTree
getVarTests = testGroup "getVar"
    [ testCase "returns the value of a variable present in VEnv and Store" $ do
            let venv = Map.fromList [("x", 0), ("y", 1)]
                storeMap = Map.fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            getVar venv store "x" @?= 42
            getVar venv store "y" @?= 7

    , testCase "throws an exception if variable not in VEnv" $ do
            let venv = Map.fromList [("x", 0), ("y", 1)]
                storeMap = Map.fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            evaluate (let _ = getVar venv store "z" in ()) `catch` catchSomeEx

    , testCase "throws an exception if location not in Store" $ do
            let venv = Map.fromList [("x", 0), ("y", 1), ("z", 99)]
                storeMap = Map.fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            evaluate (let _ = getVar venv store "z" in ()) `catch` catchSomeEx
    ]


freeVarsTests :: TestTree
freeVarsTests = testGroup "freeVars"
    [ testCase "returns empty set for constant expressions" $ do
            freeVars (ENum 42) @?= Set.empty
            freeVars (EPlus (ENum 1) (ENum 2)) @?= Set.empty
    , testCase  "returns set with single variable for variable expressions" $ do
            freeVars (EVar (Ident "x")) @?= Set.singleton "x"
    , testCase "returns union of free variables for addition" $ do
            freeVars (EPlus (EVar (Ident "x")) (EVar (Ident "y"))) @?= Set.fromList ["x", "y"]
    , testCase "returns union of free variables for substraction" $ do
            freeVars (EMinus (EVar (Ident "a")) (EVar (Ident "b"))) @?= Set.fromList ["a", "b"]
    , testCase "returns union of free variables for multiplication" $ do
            freeVars (EMul (EVar (Ident "m")) (EVar (Ident "n"))) @?= Set.fromList ["m", "n"]
    , testCase "returns union of free variables for division" $ do
            freeVars (EDiv (EVar (Ident "p")) (EVar (Ident "q"))) @?= Set.fromList ["p", "q"]
    , testCase "works recursively for nested expressions" $ do
            let expr = EPlus (EMul (EVar (Ident "x")) (ENum 2)) (EVar (Ident "y"))
            freeVars expr @?= Set.fromList ["x", "y"]
    ]

freeVarsBTests :: TestTree
freeVarsBTests = testGroup "freeVarsB"
    [ testCase "returns union of free variables for /\\" $ do
            let b = BAnd (BEq (EVar (Ident "x")) (ENum 1)) (BLeq (EVar (Ident "y")) (ENum 2))
            freeVarsB b @?= Set.fromList ["x", "y"]
    , testCase "returns union of free variables for =" $ do
            let b = BEq (EVar (Ident "a")) (EVar (Ident "b"))
            freeVarsB b @?= Set.fromList ["a", "b"]
    , testCase "returns union of free variables for <=" $ do
            let b = BLeq (EVar (Ident "a")) (ENum 5)
            freeVarsB b @?= Set.singleton "a"
    , testCase "returns union of free variables for >" $ do
            let b = BGt (EVar (Ident "x")) (EVar (Ident "z"))
            freeVarsB b @?= Set.fromList ["x", "z"]
    , testCase "returns freeVarsB for ~" $ do
            let b = BNot (BEq (EVar (Ident "foo")) (ENum 0))
            freeVarsB b @?= Set.singleton "foo"
    , testCase "returns empty set for True" $ do
            freeVarsB BTrue @?= Set.empty
    , testCase "returns empty set for False" $ do
            freeVarsB BFalse @?= Set.empty
    , testCase "works recursively for nested boolean expressions" $ do
            let b = BAnd (BNot (BEq (EVar (Ident "x")) (ENum 1))) (BGt (EVar (Ident "y")) (ENum 2))
            freeVarsB b @?= Set.fromList ["x", "y"]
    ]

freeVarsDTests :: TestTree
freeVarsDTests = testGroup "freeVarsD"
    [ testCase "returns union of free variables for \\/" $ do
            let f = FormulaDOr (BEq (EVar (Ident "x")) (ENum 1)) 
                               (FormulaDB (BLeq (EVar (Ident "y")) (ENum 2)))
            freeVarsD f @?= Set.fromList ["x", "y"]
    , testCase "returns freeVarsB for boolean expressions as disjunctions" $ do
            let f = FormulaDB (BEq (EVar (Ident "a")) (ENum 3))
            freeVarsD f @?= Set.singleton "a"
    , testCase "works recursively for nested disjunctive formulas" $ do
            let f = FormulaDOr (BEq (EVar (Ident "x")) (ENum 1)) 
                               (FormulaDOr (BLeq (EVar (Ident "y")) (ENum 2)) 
                                           (FormulaDB (BGt (EVar (Ident "z")) (ENum 0))))
            freeVarsD f @?= Set.fromList ["x", "y", "z"]
    ]

freeVarsFTests :: TestTree
freeVarsFTests = testGroup "freeVarsF"
    [ testCase "returns freeVarsD for a disjunctive subformula" $ do
            let f = FormulaDA (FormulaDOr (BEq (EVar (Ident "x")) (ENum 1)) 
                                          (FormulaDB (BLeq (EVar (Ident "y")) (ENum 2))))
            freeVarsF f @?= Set.fromList ["x", "y"]
    , testCase "returns free variables for a quantified formula with bound variables removed" $ do
            let f = FormulaQI [ForallB (Ident "x"), ExistsB (Ident "y")] (BEq (EVar (Ident "x")) (EVar (Ident "z"))) 
                              (FormulaDA (FormulaDB (BLeq (EVar (Ident "y")) (ENum 2))))
            freeVarsF f @?= Set.singleton "z"
    , testCase "returns union of free variables for /\\" $ do
            let f = FormulaAnd (FormulaDA (FormulaDB (BEq (EVar (Ident "a")) (ENum 3))))
                               (FormulaDA (FormulaDOr (BLeq (EVar (Ident "b")) (ENum 5)) 
                                                       (FormulaDB (BGt (EVar (Ident "c")) (ENum 0)))))
            freeVarsF f @?= Set.fromList ["a", "b", "c"]
    , testCase "returns union of free variables for =>" $ do
            let f = FormulaI (FormulaDA (FormulaDB (BEq (EVar (Ident "m")) (ENum 10))))
                              (FormulaDA (FormulaDOr (BLeq (EVar (Ident "n")) (ENum 20)) 
                                                      (FormulaDB (BGt (EVar (Ident "p")) (ENum 0)))))
            freeVarsF f @?= Set.fromList ["m", "n", "p"]
    , testCase "works recursively for nested formulas" $ do
            let f = FormulaAnd 
                        (FormulaQI [ForallB (Ident "x")] (BEq (EVar (Ident "x")) (EVar (Ident "y"))) 
                                     (FormulaDA (FormulaDB (BLeq (EVar (Ident "z")) (ENum 2)))))
                        (FormulaI (FormulaDA (FormulaDB (BEq (EVar (Ident "a")) (ENum 3))))
                                   (FormulaDA (FormulaDOr (BLeq (EVar (Ident "b")) (ENum 5)) 
                                                           (FormulaDB (BGt (EVar (Ident "c")) (ENum 0))))))
            freeVarsF f @?= Set.fromList ["y", "z", "a", "b", "c"]
    ]

tests :: TestTree
tests = testGroup "Logic Tests"
    [ getVarTests,
      freeVarsTests,
      freeVarsBTests,
      freeVarsDTests,
      freeVarsFTests
    ]
    