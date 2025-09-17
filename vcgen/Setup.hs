import Distribution.Simple
import System.Directory
import System.Process
import Distribution.Types.HookedBuildInfo (HookedBuildInfo)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { postConf = \_ _ _ _ -> do
      createDirectoryIfMissing True "app/Tiny"

      -- Run bnfc
      callProcess "bnfc" ["-m", "--haskell", "-o", "app/Tiny", "Tiny.cf"]
      
      -- Run Alex
      callProcess "alex" ["app/Tiny/LexTiny.x", "--ghc", "-o", "app/Tiny/Lexer.hs"]

      -- Run Happy
      callProcess "happy" ["app/Tiny/ParTiny.y", "--array",  
                        "--info", "--ghc", "--coerce", 
                        "-o", "app/Tiny/ParTiny.hs"]
      return ()
  }
