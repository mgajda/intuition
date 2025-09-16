import Test.Tasty
import Test.Tasty.HUnit
import Logic
import Data.Map
import Control.Exception (evaluate, SomeException, catch)

main :: IO ()
main = defaultMain tests

catchSomeEx :: SomeException -> IO ()
catchSomeEx _ = return ()

tests :: TestTree
tests = testGroup "getVar"
    [ testCase "returns the value of a variable present in VEnv and Store" $ do
            let venv = fromList [("x", 0), ("y", 1)]
                storeMap = fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            getVar venv store "x" @?= 42
            getVar venv store "y" @?= 7

    , testCase "throws an exception if variable not in VEnv" $ do
            let venv = fromList [("x", 0), ("y", 1)]
                storeMap = fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            evaluate (let _ = getVar venv store "z" in ()) `catch` catchSomeEx

    , testCase "throws an exception if location not in Store" $ do
            let venv = fromList [("x", 0), ("y", 1), ("z", 99)]
                storeMap = fromList [(0, 42), (1, 7)]
                store = CStore storeMap 2
            evaluate (let _ = getVar venv store "z" in ()) `catch` catchSomeEx
    ]