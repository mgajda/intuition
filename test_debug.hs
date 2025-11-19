import Data.TPTP
import Data.TPTP.Parse.Text
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
    content <- TIO.readFile "tests/simple/test-simple-negation.p"
    let parsed = parse content
    print parsed
