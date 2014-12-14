{-# language GeneralizedNewtypeDeriving #-}

module Solve where
    
import qualified OBDD as O
import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.Reader as R
import qualified Data.Map.Strict as M
       
import Control.Applicative
import Control.Monad 
import Test.Hspec
import Test.QuickCheck

-- | source code shows how to use this
test1 = solve $ do
   x <- unknown 7
   y <- unknown 7
   constraint ( equals ( constant 1001 ) (times x y ) )
       ( (,) <$> read_natural x <*> read_natural y )

unknown :: Int -> S.State [Var] Natural
unknown w | w >= 0 = do
    vars <- S.get
    let (pre, post) = splitAt w vars
    S.put post
    return $ map ( \ v -> O.unit v True) pre

-- | this should be in the OBDD package
evaluate b = do
    f <- R.ask
    return $ O.fold id ( \ v l r -> if M.findWithDefault False v f then r else l ) b
    
read_bit b = evaluate b
read_natural n = do
    xs <- forM n $ read_bit
    return $ foldl ( \ x b -> 2 * x + fromIntegral (fromEnum b) ) (0 :: Integer) xs

solve :: S.State [Var] (O.OBDD Var, R.Reader (M.Map Var Bool) a)
      -> IO (Maybe a)
solve program = do
    let (c, action) = S.evalState program [ Var 0 .. ] 
    m <- O.some_model c
    return $ case m of
        Nothing -> Nothing
        Just f -> Just $ R.runReader action f

constraint c action = return (c, action)
    
       
newtype Var = Var Int deriving (Eq, Ord, Show, Enum)

type Bit = O.OBDD Var

-- | lsb comes first
type Natural = [ Bit ]

equals [] ys = O.not $ O.or ys
equals xs [] = O.not $ O.or xs
equals (x:xs) (y:ys) =
    O.binary (==) x y O.&& equals xs ys       
       
constant :: Integer -> Natural
constant n =
    if n > 0
    then O.constant (odd n) : constant (div n 2)
    else []

-- | (result, carry)     
add2 :: Bit -> Bit -> (Bit, Bit)
add2 x y = (O.binary (/=) x y, x O.&& y)

add3 :: Bit -> Bit -> Bit -> (Bit, Bit)
add3 x y z =
    let (r1,c1) = add2 x y ; (r2,c2) = add2 r1 z
    in  (r2, c1 O.|| c2)
     
plus :: Natural -> Natural -> Natural
plus xs ys =
    let work cin (x:xs) (y:ys) =
            let (r,cout) = add3 cin x y in  r : work cout xs ys
        work cin [] (y:ys) =
            let (r,cout) = add2 cin   y in  r : work cout [] ys
        work cin (x:xs) [] =
            let (r,cout) = add2 cin x   in  r : work cout xs []
        work cin [] [] = [ cin ]
    in  work (O.constant False) xs ys
    
times :: Natural -> Natural -> Natural
times [] ys = [] 
times (x:xs) ys =
    plus (map (x O.&&) ys) (O.constant False : times xs ys)

test = hspec $ do
    describe "equals" $ do
        it "reflexive" $ property $ \ x -> O.satisfiable $ equals (constant x) (constant x)
        it "works" $ property $ \ (NonNegative x) (NonNegative y) ->
           (x == y) == O.satisfiable ( equals (constant x) (constant y) )
    describe "add2" $ do
        it "result" $ property $ \ a b ->
            let s :: Int
                s = fromEnum a + fromEnum b
                (r,c) = add2 (O.constant a) (O.constant b)
            in  O.satisfiable r == odd s
        it "carry" $ property $ \ a b ->
            let s :: Int
                s = fromEnum a + fromEnum b
                (r,c) = add2 (O.constant a) (O.constant b)
            in  O.satisfiable c == (s >= 2)
    describe "add3" $ do
        it "result" $ property $ \ a b c ->
            let s :: Int
                s = fromEnum a + fromEnum b + fromEnum c
                (r,ca) = add3 (O.constant a) (O.constant b) (O.constant c)
            in  O.satisfiable r == odd s
        it "carry" $ property $ \ a b c ->
            let s :: Int
                s = fromEnum a + fromEnum b + fromEnum c
                (r,ca) = add3 (O.constant a) (O.constant b) (O.constant c)
            in  O.satisfiable ca == (s >= 2)
    describe "plus" $ do
        it "works" $ property $ \ (NonNegative x) (NonNegative y) ->
            O.satisfiable $ equals (plus (constant x) (constant y)) (constant (x+y))
    describe "times" $ do
        it "works" $ property $ \ (NonNegative x) (NonNegative y) ->
            O.satisfiable $ equals (times (constant x) (constant y)) (constant (x*y))
       
    
