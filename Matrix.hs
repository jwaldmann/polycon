{-# language TupleSections #-}

module Matrix where

import Solve
import Control.Monad
import Control.Applicative

import qualified Buddy as B
import qualified TPDB.Data as T

import qualified Data.Map as M
import Data.List ( transpose, nub )

import qualified Control.Monad.State as S

import System.IO

remove dim bits us = do
  hPutStrLn stderr $ unwords
    [ "remove", "dim", show dim, "bits", show bits ]
  solve $ do
    int <- inter (sigma us) dim bits
    (ok, sws) <- compatible int us
    mo <- monotone int
    good <- S.lift $ mo B.&& ok
    constraint good $ do
        i <- rinter int
        us <- forM sws $ \ (s, w, u) -> do
          ss <- read_bit s
          return (ss, u)
        return (i, us)

sigma us = nub $ do u <- us ; T.lhs u ++ T.rhs u
  
monotone int = S.lift $ mo B.and $ for (M.elems int) $ \ m ->
  do tl <- positive (topleft m) ; br <- positive (botright m)
     tl B.&& br

compatible int us = do
  sws <- forM us $ \ u -> do
      l <- eval int $ T.lhs u
      r <- eval int $ T.rhs u
      s <- strictly_greater l r
      w <- weakly_greater l r
      return (s, w, u)
  allweak <- S.lift $ B.plain_and $ for sws $ \ (s,w,u) -> w
  somestrict <- S.lift $  B.plain_or $ for sws $ \ (s,w,u) -> s
  good <- S.lift $ allweak B.&& somestrict
  return (good , sws )

eval int s = do
  let dim = length $ head $ M.elems int
  unit <- forM [1..dim] $ \ i -> forM [1..dim] $ \ j ->
       S.lift $ constant $ if i == j then 1::Integer else 0
  foldM mtimes unit $ for s ( int M.! )
      
type Matrix = [[Natural]]

topleft m = head $ head m
topright m = last $ head m
botright m = last $ last m


strictly_greater l r = S.lift $ gt (topright l) (topright r)

weakly_greater l r = S.lift $
  mo B.plain_and $ concat
      $ for ( zip l r ) $ \ (xs, ys) ->
        for ( zip xs ys) $  \ (x,y) -> ge x y

rmatrix m = forM m $ \ row -> forM row $ \ n -> read_natural n

matrix_ dim bits = do
    forM [ 1 .. dim ] $ \ i ->
      forM [ 1 .. dim ] $ \ j ->
        natural bits

matrix dim bits = do
    forM [ 1 :: Int .. dim ] $ \ i ->
      forM [ 1 :: Int .. dim ] $ \ j ->
        if j == 1
        then S.lift $ constant (if i == 1 then 1 :: Integer else 0)
        else if i == dim
        then S.lift $ constant (if j == dim then 1 :: Integer else 0)
        else natural bits

mtimes a b = S.lift $ 
  forM a $ \ row ->
    forM (transpose b) $ \ col -> do
       p : ps <- sequence $ zipWith times row col
       -- foldM plus p ps
       binary_fold undefined plus $ p : ps

binary_fold nil cons =
   let run [] = constant nil
       run [x] = return x
       run (x:y:zs) = do
           xy <- cons x y
           run (zs ++ [xy])
   in  run    

type Inter i = M.Map i Matrix

inter sigma dim bits = M.fromList
   <$> (forM sigma $ \ c -> (c,) <$> matrix dim bits)
                                     
rinter int = M.fromList <$> forM (M.toList int) (\ (k,v) ->
     (k,) <$> rmatrix v )
