{-# language TupleSections #-}

module Matrix where

import Solve
import Control.Monad
import Control.Applicative

import qualified OBDD as O
import qualified TPDB.Data as T

import qualified Data.Map as M
import Data.List ( transpose, nub )

remove dim bits srs = solve $ do
    int <- inter (sigma srs) dim bits
    let (ok, sws) = compatible int srs
    constraint ( monotone int O.&& ok ) $ do
        rinter int

sigma srs = nub $ do u <- T.rules srs ; T.lhs u ++ T.rhs u
  
monotone int = O.and $ for (M.elems int) $ \ m ->
  positive (topleft m) O.&& positive (botright m)

compatible int srs =
  let sws = for (T.rules srs) $ \ u ->
        let l = eval int $ T.lhs u
            r = eval int $ T.rhs u
            s = strictly_greater l r
            w = weakly_greater l r
        in  (s, w, u)
      allweak = O.and $ for sws $ \ (s,w,u) -> w
      somestrict = O.or $ for sws $ \ (s,w,u) -> s
  in  ( allweak O.&& somestrict, sws )

eval int s =
  let dim = length $ head $ M.elems int
      unit = for [1..dim] $ \ i -> for [1..dim] $ \ j ->
            constant $ if i == j then 1 else 0
  in  foldr mtimes unit $ for s ( int M.! )
      
type Matrix = [[Natural]]

topleft m = head $ head m
topright m = last $ head m
botright m = last $ last m


strictly_greater l r = gt (topright l) (topright r)

weakly_greater l r =
  O.and $ zipWith ( \ xs ys -> O.and $ zipWith ge xs ys ) l r

rmatrix m = forM m $ \ row -> forM row $ \ n -> read_natural n

matrix_ dim bits = do
    forM [ 1 .. dim ] $ \ i ->
      forM [ 1 .. dim ] $ \ j ->
        natural bits

matrix dim bits = do
    forM [ 1 .. dim ] $ \ i ->
      forM [ 1 .. dim ] $ \ j ->
        if j == 1
        then return $ constant (if i == 1 then 1 else 0)
        else if i == dim
        then return $ constant (if j == dim then 1 else 0)
        else natural bits

mtimes a b =
  for a $ \ row ->
    for (transpose b) $ \ col ->
       foldr1 plus $ zipWith times row col
       
type Inter i = M.Map i Matrix

inter sigma dim bits = M.fromList
   <$> (forM sigma $ \ c -> (c,) <$> matrix dim bits)
                                     
rinter int = M.fromList <$> forM (M.toList int) (\ (k,v) ->
     (k,) <$> rmatrix v )
