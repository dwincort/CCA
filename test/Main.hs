{-# LANGUAGE CPP, TemplateHaskell #-}

module Main where

#if __GLASGOW_HASKELL__ >= 610
import Control.Category
import Prelude hiding ((.), init, exp, id)
#else
import Prelude hiding (init, exp)
#endif

import Control.Arrow
import Control.CCA
import Control.CCA.CCNF
import Control.CCA.Types
import System.IO
import System.CPUTime
import Sample 
import qualified Sample1 as S

import Control.Monad.Fix (fix)
import Data.Dynamic
import Control.DeepSeq

newtype SF a b = SF { runSF :: (a -> (b, SF a b)) }

#if __GLASGOW_HASKELL__ >= 610
instance Category SF where
  id = SF h where h x = (x, SF h)
  g . f = SF (h f g)
    where
      h f g x =
        let (y, f') = runSF f x
            (z, g') = runSF g y
        in (z, SF (h f' g'))
#endif

instance Arrow SF where
  arr f = g
    where g = SF (\x -> (f x, g))
#if __GLASGOW_HASKELL__ < 610
  f >>> g = SF (h f g)
    where
      h f g x = 
        let (y, f') = runSF f x
            (z, g') = runSF g y
        in (z, SF (h f' g'))
#endif
  first f = SF (g f)
    where
      g f (x, z) = ((y, z), SF (g f'))
        where (y, f') = runSF f x
  second f = SF (g f)
    where
      g f (z, x) = ((z, y), SF (g f'))
        where (y, f') = runSF f x
  f &&& g = SF (h f g)
    where
      h f g x =
        let (y, f') = runSF f x
            (z, g') = runSF g x 
        in ((y, z), SF (h f' g'))
  f *** g = SF (h f g)
    where
      h f g x =
        let (y, f') = runSF f (fst x)
            (z, g') = runSF g (snd x) 
        in ((y, z), SF (h f' g'))

instance ArrowLoop SF where
  loop sf = SF (g sf)
    where
      g f x = (y, SF (g f'))
        where ((y, z), f') = runSF f (x, z)

instance ArrowInit SF where
  init i = SF (f i)
    where f i x = (i, SF (f x))
  loopD i g = SF (f i) 
    where
      f i x = 
        let (y, i') = g (x, i)
        in (y, SF (f i'))

instance ArrowChoice SF where
   left sf = SF (g sf)
       where 
         g f x = case x of
                   Left a -> let (y, f') = runSF f a in f' `seq` (Left y, SF (g f'))
                   Right b -> (Right b, SF (g f))

instance ArrowFix SF where
  afix = fix

run :: SF a b -> [a] -> [b]
run _ [] = []
run (SF f) (x:xs) =
  let (y, f') = f x 
  in y `seq` (y : run f' xs)

run' :: (i, (b, i) -> (c, i)) -> [b] -> [c]
run' _ [] = []
run' (i, f) inp = aux inp i
  where
    aux [] _ = []
    aux (x:xs) i = y `seq` (y:aux xs i')
      where (y, i') = f (x, i)
 
unfold :: SF () a -> [a]
unfold = flip run inp
  where inp = () : inp

nthWith :: NFData c => b -> Int -> SF b c -> c
nthWith b n (SF f) = x `deepseq` if n == 0 then x else nthWith b (n - 1) f'
  where (x, f') = f b

nth :: NFData a => Int -> SF () a -> a
nth = nthWith ()

nthWith' :: NFData c => b -> Int -> (i, (b, i) -> (c, i)) -> c
nthWith' b n (i, f) = aux n i
  where
    aux n i = x `deepseq` if n == 0 then x else aux (n-1) i'
      where (x, i') = f (b, i)

nth' :: NFData a => Int -> (b, ((), b) -> (a, b)) -> a
nth' = nthWith' ()
 
timer i = do t0 <- getCPUTime
             i `seq` (do
               t1 <- getCPUTime
	       let d = t1 - t0
               putStrLn $ show d ++ "\t" ++ show i
               return d)

gnuplot f l = do
      h <- openFile f WriteMode
      mapM_ (\(x, y) -> hPutStrLn h (show x ++ "\t" ++ show y)) 
            (zip [0, dt..] l)
      hClose h

plot3sec fn = gnuplot fn . take (sr * 3) . unfold 

testcase list = do
  ts <- mapM timer list
  let ts' = map (\x -> 1 / fromIntegral x) ts
  let x = minimum ts'
  let ns = map (/x) ts'
  sequence_ [ putStr (show (fromIntegral (floor (x * 100)) / 100) ++ "\t") | x <- ns ]
  putStrLn "\n"

main = do
  let n = 1000000
  putStrLn "Compare exp signal function"
  testcase [nth n S.exp, nth n exp, expNorm n, expOpt n]
  putStrLn "Compare sine signal function"
  testcase [nth n (S.sine 2), nth n (sine 2), sineNorm n, sineOpt n]
  putStrLn "Compare oscSine signal function"
  testcase [nth n (S.testOsc S.oscSine), nth n (testOsc oscSine), oscNorm n, oscOpt n]
  putStrLn "Compare sciFi signal function"
  testcase [nth n S.sciFi, nth n sciFi, sciFiNorm n, sciFiOpt n]
  putStrLn "Compare robot signal function"
  testcase [nth n (S.testRobot S.robot), nth n (testRobot robot), robotNorm n, robotOpt n]
  putStrLn "Compare Multiple Dynamic Counter (3) signal function"
  testcase [nthWith 3 n (S.runDynamic S.counter), nthWith 3 n (runDynamic counter), dynCNorm 3 n, dynCOpt 3 n]
  putStrLn "Compare Dynamic Linking Adder (3) signal function"
  testcase [nthWith (3,0) n (S.linkDynamic S.plusOne), nthWith (3,0) n (linkDynamic plusOne), dynLPNorm (3,0) n, dynLPOpt (3,0) n]
  putStrLn "Compare Dynamic Linking Integral (3) signal function"
  testcase [nthWith (3,1) n (S.linkDynamic S.integral), nthWith (3,1) n (linkDynamic integral), dynLINorm (3,1) n, dynLIOpt (3,1) n]



dynCNorm k n = nthWith  k n $(norm $ runDynamic counter)
dynCOpt  k n = nthWith' k n $(normOpt $ runDynamic counter)

dynLPNorm k n = nthWith  k n $(norm    $ linkDynamic plusOne)
dynLPOpt  k n = nthWith' k n $(normOpt $ linkDynamic plusOne)

dynLINorm k n = nthWith  k n $(norm    $ linkDynamic integral)
dynLIOpt  k n = nthWith' k n $(normOpt $ linkDynamic integral)

expNorm n = nth n $(norm exp)
expOpt n = nth' n $(normOpt exp)

sineNorm n = nth n $(norm $ sine 2)
sineOpt n = nth' n $(normOpt $ sine 2)

oscNorm n = nth n $(norm $ testOsc oscSine)
oscOpt n = nth' n $(normOpt $ testOsc oscSine) 

sciFiNorm n = nth n $(norm sciFi)
sciFiOpt n = nth' n $(normOpt sciFi)

robotNorm n = nth n $(norm $ testRobot robot)
robotOpt n = nth' n $(normOpt $ testRobot robot)

