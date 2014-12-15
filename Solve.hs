{-# language GeneralizedNewtypeDeriving #-}

module Solve where
    
import qualified Buddy as B
import Buddy (BDD)

import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.Reader as R
import qualified Data.Map.Strict as M
       
import Control.Applicative
import Control.Monad 
import Test.Hspec
import Test.Hspec.Runner
import Test.QuickCheck

-- | source code shows how to use this:
test1 = solve $ do
   x <- natural 7
   y <- natural 7
   c <- S.lift $ constant 1001
   xy <- S.lift $ times x y
   e <- S.lift $ equals c xy 
   constraint e
       ( (,) <$> read_natural x <*> read_natural y )

-- | allocate unknown natural. argument is bit width
-- natural :: Int -> S.State [Var] Natural
natural w | w >= 0 = do
    vars <- S.get
    let (pre, post) = splitAt w vars
    S.put post
    S.lift $ forM pre $ \ v -> B.unit v True

-- | this should be in the OBDD package
evaluate b = do
    f <- R.ask
    R.lift $ B.fold id ( \ v l r -> if M.findWithDefault False v f then r else l ) b
    
read_bit b = evaluate b
read_natural n = do
    xs <- forM n $ read_bit
    return $ foldr ( \ b x -> 2 * x + fromIntegral (fromEnum b) ) (0 :: Integer) xs


solve program = B.run [Var 0 .. Var 1000] $ do
    (c, action) <- S.evalStateT program [ Var 0 .. ]
    s <- B.satisfiable c
    case s of
        False -> return Nothing
        True -> do
            m <- B.model c
            Just <$> R.runReaderT action m

constraint c action = return (c, action)
    
-- *

mo f xs = sequence xs >>= f

newtype Var = Var Int deriving (Eq, Ord, Show, Enum)

type Bit = BDD Var

-- | lsb comes first
type Natural = [ Bit ]

positive xs = B.or xs

ge a b = do (g,e) <- gte a b ; g B.|| e
gt a b = do (g,e) <- gte a b ; return g 

gte xs0 ys0 = do
    (xs,ys) <- align xs0 ys0
    let work [] [] = do
            (,) <$>  B.constant False <*> B.constant True 
        work (x:xs) (y:ys) = do
          ( g , e ) <- work xs ys
          ny <- B.not y
          xgy <- B.and [e, x, ny ]
          gg <- g B.|| xgy
          xey <- B.biimp x y
          ee <- e B.&& xey
          return (gg, ee)
    work xs ys

align xs ys = do
  z <- B.constant False
  let n = max (length xs) (length ys)
      fill zs = zs ++ replicate (n - length zs) z
  return ( fill xs, fill ys )

equals xs0 ys0 = do
    (xs,ys) <- align xs0 ys0
    es <- forM (zip xs ys) $ \ (x,y) -> B.biimp x y
    B.and es
       
-- constant :: Integer -> Natural
constant n =
    if n > 0
    then (:) <$> B.constant (odd n) <*> constant (div n 2)
    else return []

-- | (result, carry)     
-- add2 :: Bit -> Bit -> (Bit, Bit)
-- using 2 ops
add2 x y = (,) <$> B.xor x y <*> ( x B.&& y )

-- | (result, carry)
-- add3 :: Bit -> Bit -> Bit -> (Bit, Bit)
-- using 5 ops
add3 x y z = do
    (r1,c1) <- add2 x y ; (r2,c2) <- add2 r1 z
    (,) <$> return r2 <*> ( c1 B.|| c2)
     
-- plus :: Natural -> Natural -> Natural
plus xs ys = do
    let work cin (x:xs) (y:ys) = do
            (r,cout) <- add3 cin x y
            (r :) <$> work cout xs ys
        work cin [] (y:ys) = do
            (r,cout) <- add2 cin   y
            (r :) <$> work cout [] ys
        work cin (x:xs) [] = do
            (r,cout) <- add2 cin x
            (r :) <$> work cout xs []
        work cin [] [] = return [ cin ]
    z <- B.constant False
    work z xs ys
    
times = times0

-- times0 :: Natural -> Natural -> Natural
times0 [] ys = return [] 
times0 (x:xs) ys = do
    xys <- forM ys $ (x B.&&)
    xsys <- (:) <$> B.constant False <*> times0 xs ys
    plus xys xsys

times1 xs ys = do
    up <- M.fromListWith (++) <$> sequence ( do
          (i,x) <- zip [0..] xs
          (j,y) <- zip [0..] ys
          return $ do
            xy <- x B.&& y
            return (i+j, [xy])   )
    let down [] = return []
        down ( [x] : rest ) = (x :) <$> down rest
        down ( [x,y] : rest ) = do
          (r,c) <- add2 x y
          (r :) <$> down (case rest of
                          [] -> [[c]]
                          r:est ->      (c : r): est)
        down ( (x:y:z:here) : rest ) = do
          (r,c) <- add3 x y z
          down $ (here ++ [r]) : case rest of
                [] -> [[c]]
                r:est -> (c:r) : est
        down args = error $ show $ map length args
    down $ map snd $ M.toAscList up


for = flip map

    
