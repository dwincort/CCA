module Sample where

import Control.CCA
import Prelude hiding (init, exp)
import Language.Haskell.TH

sr = 44100 :: Int
dt = 1 / (fromIntegral sr)

counter :: ArrowInit a => a () Int
counter = proc () -> do
  rec x <- init (0 :: Int) -< x + 1
  returnA -< x

plusOne :: ArrowInit a => a Int Int
plusOne = proc x -> do
  returnA -< x + (1 :: Int)

linkDynamic :: (ArrowFix a, ArrowChoice a, ArrowInit a) => a b b -> a (Int,b) b
linkDynamic sf = afix $ \linkDynamic -> proc (n,b) -> do
  case n of
    0 -> returnA -< b
    k -> do b'  <- sf -< b
            b'' <- linkDynamic -< (k-1,b')
            returnA -< b''

runDynamic :: (ArrowFix a, ArrowChoice a, ArrowInit a) => a () c -> a Int [c]
runDynamic sf = afix $ \runDynamic -> proc n -> do
  case n of
    0 -> returnA -< []
    k -> do c <- sf -< ()
            cs <- runDynamic -< k-1
            returnA -< c:cs

exp :: ArrowInit a => a () Double
exp = proc () -> do
  rec let e = 1 + i
      i <- integral -< e
  returnA -< e

integral :: ArrowInit a => a Double Double
integral = proc x -> do
  rec let i' = i + x * dt
      i <- init (0 :: Double) -< i'
  returnA -< i

sine :: ArrowInit a => Double -> a () Double
sine freq = proc _ -> do
  rec x <- init i -< r
      y <- init 0 -< x 
      let r = c * x - y
  returnA -< r
  where
    omh = 2 * pi / (fromIntegral sr) * freq
    i = sin omh
    c = 2 * cos omh

oscSine :: ArrowInit a => Double -> a Double Double
oscSine f0 = proc cv -> do
  let f = f0 * (2 ** cv)
  phi <- integral -< 2 * pi * f
  returnA -< sin phi

testOsc :: ArrowInit a => (Double -> a Double Double) -> a () Double
testOsc f = constant 1 >>> f 440

sciFi :: ArrowInit a => a () Double
sciFi = proc () -> do
   und <- oscSine 3.0 -< 0
   swp <- integral -< -0.25
   audio <- oscSine 440 -< und * 0.2 + swp + 1
   returnA -< audio

robot :: ArrowInit a => a (Double, Double) Double
robot = proc inp -> do
    let vr = snd inp
        vl = fst inp
        vz = vr + vl
    t <- integral -< vr - vl
    let t' = t / 10
    x <- integral -< vz * cos t'
    y <- integral -< vz * sin t'
    returnA -< x / 2 + y / 2

testRobot :: ArrowInit a => a (Double, Double) Double -> a () Double
testRobot bot = proc () -> do
    u <- sine 2 -< ()
    robot -< (u, 1 - u)

