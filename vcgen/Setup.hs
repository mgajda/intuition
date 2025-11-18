import Distribution.Simple
import System.Directory
import System.Process
import Distribution.Types.HookedBuildInfo (HookedBuildInfo)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { postConf = \_ _ _ _ -> do
      -- Create directories
      createDirectoryIfMissing True "app/Tiny"
      createDirectoryIfMissing True "app/Yul"

      -- Process Tiny.cf
      callProcess "bnfc" ["-m", "--haskell", "-o", "app/Tiny", "Tiny.cf"]
      callProcess "alex" ["app/Tiny/LexTiny.x", "--ghc", "-o", "app/Tiny/Lexer.hs"]
      callProcess "happy" ["app/Tiny/ParTiny.y", "--array",
                        "--info", "--ghc", "--coerce",
                        "-o", "app/Tiny/ParTiny.hs"]

      -- Process Yul.cf
      callProcess "bnfc" ["-m", "--haskell", "-o", "app/Yul", "Yul.cf"]
      callProcess "alex" ["app/Yul/LexYul.x", "--ghc", "-o", "app/Yul/LexerYul.hs"]
      callProcess "happy" ["app/Yul/ParYul.y", "--array",
                        "--info", "--ghc", "--coerce",
                        "-o", "app/Yul/ParYul.hs"]

      return ()
  }
