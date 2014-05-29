> {-# LANGUAGE TemplateHaskell, FlexibleInstances #-}

> module Control.CCA 
>   ((>>>), (<<<), first, second, (***), (&&&), loop, 
>    Arrow, ArrowLoop, ArrowInit, 
>    ArrowChoice, (|||), ArrowFix, afix,
>    arr, init, arr', init', constant,
>    returnA,
>    norm, normOpt) where

> import Control.Arrow hiding (arr, returnA)
> import Control.CCA.Types hiding (init)
> import Control.CCA.CCNF
> import Language.Haskell.TH
> import Language.Haskell.TH.Syntax
> import Language.Haskell.TH.Instances
> import Prelude hiding (init)

> arr :: ExpQ -> ExpQ
> arr e = appE [|arr' e|] e

> init :: ExpQ -> ExpQ
> init i = appE [|init' i|] i

> returnA :: ArrowInit a => a b b
> returnA = arr' [|id|] id

> constant :: (ArrowInit a, Lift b) => b -> a () b
> constant c = arr' [|const c|] (const c)

