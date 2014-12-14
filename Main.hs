import Matrix
import TPDB.Input
import TPDB.Pretty

import System.Environment

main = do
    [ file ] <- getArgs
    sys <- get_srs file
    print $ pretty sys
    
    int <- remove 3 2 sys
    print int
    
    
