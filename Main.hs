import Matrix
import TPDB.Input
import TPDB.Pretty
import qualified TPDB.Data as T

import System.Environment

main = do
    [ file ] <- getArgs
    sys <- get_srs file
    print $ pretty sys
    handle 2 $ T.rules sys

handle bits [] = putStrLn "done"
handle bits us = do    
    (int,out) <- removes bits us
    print int
    print $ pretty out
    handle bits $ do (False, u) <- out ; return u
    
    
removes bits us = do
    let work dim = do
          int <- remove dim bits us
          case int of
              Nothing -> work $ succ dim
              Just out -> return out
    work 1
    
