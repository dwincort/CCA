> {-# LANGUAGE CPP, TemplateHaskell, FlexibleInstances #-}

> module Control.CCA.CCNF 
>   (norm, normOpt, 
>    pprNorm, pprNormOpt, printCCA, ASyn,
>    cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT) where

#if __GLASGOW_HASKELL__ >= 610

> import Control.Category
> import Prelude hiding ((.), id, init)

#else

> import Prelude hiding (init)

#endif

> import Control.Arrow 
> import Control.CCA.Types
> import Data.Char (isAlpha)
> import Language.Haskell.TH
> import Language.Haskell.TH.Syntax
> import Language.Haskell.TH.Instances
> import qualified Data.Generics as G (everywhere, mkT)

> import Control.Monad.Fix (fix)
> import Data.Dynamic
> import Control.Monad (liftM2, ap)

Internal Representation
=======================

We use AExp to syntactically represent an arrow for normalization purposes. 

> data AExp
>   = Arr ExpQ
>   | First AExp
>   | AExp :>>> AExp
>   | Loop AExp
>   | LoopD ExpQ ExpQ -- loop with initialized feedback
>   | Init ExpQ
>   | Lft AExp
>   | AFix (AExp -> AExp)
> --  | RecVarA ExpQ
>   | RecVarL ExpQ ExpQ

> infixl 1 :>>>

We use phantom types to make ASyn an Arrow.

> newtype ASyn b c = AExp { unAExp :: AExp }

#if __GLASGOW_HASKELL__ >= 610

> instance Category ASyn where
>   id = AExp (Arr [|\x -> x|])
>   AExp g . AExp f = AExp (f :>>> g)

> instance Arrow ASyn where
>   arr f = error "use arr' instead" 
>   first (AExp f) = AExp (First f)

#else

> instance Arrow ASyn where
>   arr f = error "use arr' instead" 
>   AExp f >>> AExp g = AExp (f :>>> g)
>   first (AExp f) = AExp (First f)

#endif

> instance ArrowLoop ASyn where
>   loop (AExp f) = AExp (Loop f)

> instance ArrowInit ASyn where
>   init i = error "use init' instead"
>   arr' f _ = AExp (Arr f)
>   init' i _ = AExp (Init i)


ArrowChoice only requires definition for 'left', but the default implementation
for 'right' and '|||' uses arr so we need to redefine them using arr' here.
'+++' is also redefined here for completeness.

> instance ArrowChoice ASyn where
>   left (AExp f) = AExp (Lft f)
>   right f = arr' [| mirror |] mirror >>> left f
>             >>> arr' [| mirror |] mirror
>   f +++ g = left f >>> right g
>   f ||| g = f +++ g >>> arr' [| untag |] untag

> instance ArrowFix ASyn where
>   afix f = AExp (AFix (unAExp . f . AExp))


Pretty printing AExp.

> printCCA (AExp x) = printAExp x
> printAExp x = runQ (fromAExp x) >>= putStrLn . simplify . pprint
> simplify = unwords . map (unwords . map aux . words) . lines 
>   where aux (c:x) | not (isAlpha c) = c : aux x
>         aux x = let (u, v) = break (=='.') x
>                 in if length v > 1 then aux (tail v)
>                                    else x

Traversal over AExp is defined in terms of imap (intermediate map) 
and everywhere. 

> type Traversal = AExp -> AExp
> imap :: Traversal -> Traversal
> imap h (First f) = First (h f)
> imap h (f :>>> g) = h f :>>> h g
> imap h (Loop f) = Loop (h f)
> imap h (Lft f) = Lft (h f)
> imap h x = x

> everywhere :: Traversal -> Traversal 
> everywhere h = h . imap (everywhere h)

Normalization
=============

norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
give the CCNF of e. 

> norm :: ASyn t t1 -> ExpQ         -- returns a generic ArrowInit arrow
> norm (AExp e) = fromAExp (normE e)
> normE = everywhere normalize 

normOpt returns the pair of state and pure function as (i, f) from optimized 
CCNF in the form loopD i (arr f). 

> normOpt :: ASyn t t1 -> ExpQ      -- returns a pair of state and pure function (s, f)
> normOpt (AExp e) = 
>   case normE e of
>     LoopD i f -> tupE [i, f]
>     Arr f     -> [| ( (), $(appE [|first|] f) ) |]
>     _         -> error "The given arrow can't be normalized to optimized CCNF."

pprNorm and pprNormOpt return the pretty printed normal forms as a 
string.

> pprNorm = ppr' . norm
> pprNormOpt = ppr' . normOpt
> ppr' e = runQ (fmap toLet e) >>= litE . StringL . simplify . pprint

fromAExp converts AExp back to TH Exp structure.

> fromAExp :: AExp -> ExpQ
> fromAExp (Arr f) = appE [|arr|] f
> fromAExp (First f) = appE [|first|] (fromAExp f)
> fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
> fromAExp (Loop f) = appE [|loop|] (fromAExp f)
> fromAExp (LoopD i f) = appE (appE [|loopD|] i) f
> fromAExp (Init i) = appE [|init|] i
> fromAExp (Lft f) = appE [|left|] (fromAExp f)
> fromAExp (AFix f) = fromAExp (fix f)
> --fromAExp (RecVarA _) = error "RecVarA"
> fromAExp (RecVarL _ _) = error "RecVarL"

CCNF
====

Arrow laws:

> normalize (Arr f :>>> Arr g) = Arr (g `o` f)
> normalize (First (Arr f)) = Arr (f `crossE` idE)
> normalize (Arr f :>>> LoopD i g) = LoopD i (g `o` (f `crossE` idE))
> normalize (LoopD i f :>>> Arr g) = LoopD i ((g `crossE` idE) `o` f)
> normalize (LoopD i f :>>> LoopD j g) = LoopD (tupE [i,j]) 
>   (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE `o` (f `crossE` idE) `o` unassocE)
> normalize (Loop (LoopD i f)) = LoopD i (traceE (juggleE `o` f `o` juggleE))
> normalize (First (LoopD i f)) = LoopD i (juggleE `o` (f `crossE` idE) `o` juggleE)
> normalize (Init i) = LoopD i swapE

Choice:

> normalize (Lft (Arr f)) = Arr (lftE f)
> normalize (Lft (LoopD i f)) = LoopD i (untagE `o` lftE f `o` tagE)

fix and recursion:


> normalize (AFix f) = case normE (f (RecVarL [|id|] [|id|])) of
>   --RecVarA g -> Arr (fixE g)
>   RecVarL j g -> let i = fixE ([|toDyn|] `o` j)
>                      f = fixE ((ldot [|second toDyn|]) `o` (rdot (appE [|second|] (appE [|flip fromDyn|] (appE j i)))) `o` g)
>       in LoopD i f
>   x -> x

Fix Normalization for just RecVarA cases:

normalize (RecVarA f :>>> Arr g) = RecVarA ((ldot g) `o` f)
normalize (Arr f :>>> RecVarA g) = RecVarA ((rdot f) `o` g)
normalize (First (RecVarA f)) = RecVarA (crossId `o` f)
normalize (Lft (RecVarA f)) = RecVarA ([|lft|] `o` f)
normalize (RecVarA f :>>> RecVarA g) = RecVarA (appE (appE [| liftM2 (.) |] g) f) -- \x -> g x . f x

Fix Normalization for RecVarL cases:

> normalize (RecVarL j f :>>> Arr g) = RecVarL j ((ldot (g `crossE` idE)) `o` f)
> normalize (Arr f :>>> RecVarL j g) = RecVarL j ((rdot (f `crossE` idE)) `o` g)
> normalize (First (RecVarL j f)) = RecVarL j (ldot juggleE `o` rdot juggleE `o` crossId `o` f)
>               -- \x -> juggle . (f x `cross` id) . juggle
>               -- (juggle .) . (. juggle) . (flip cross) id . f
> normalize (Lft (RecVarL j f)) = RecVarL j (ldot untagE `o` rdot tagE `o` [|lft|] `o` f)
>               -- \x -> untag . lft (f x) . tag
>               -- (untag .) . (. tag) . lft . f
> normalize (RecVarL j f :>>> RecVarL k g) = RecVarL (appE (appE [| liftM2 (,) |] j) k) h where
>  h = (ldot (assocE `o` juggleE)) `o` 
>       (appE (appE [| ap |] (dot `o` crossId `o` g))
>             ((ldot juggleE) `o` (rdot unassocE) `o` crossId `o` f))
>               -- \x -> assoc . juggle . (g x `cross` id) . juggle . (f x `cross` id) . unassoc
>               -- ((assoc . juggle) .) . ap ((.) . (`cross` id) . g) ((juggle .) . (. unassoc) . (`cross` id) . f)
> normalize (RecVarL j f :>>> LoopD k g) = RecVarL (appE [|flip (,)|] k `o` j) h where
>  h = (ldot (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE)) `o` (rdot unassocE) `o` crossId `o` f
>               -- \x -> assoc . juggle . (g `cross` id) . juggle . (f x `cross` id) . unassoc
>               -- ((assoc . juggle . (g `cross` id) . juggle) .) . (. unassoc) . (`cross` id) . f
> normalize (LoopD j f :>>> RecVarL k g) = RecVarL (appE [|(,)|] j `o` k) h where
>  h = (ldot (assocE `o` juggleE)) `o` (rdot unassocE) `o` (rdot (f `crossE` idE)) `o` (rdot juggleE) `o` crossId `o` g
>               -- \x -> assoc . juggle . (g x `cross` id) . juggle . (f `cross` id) . unassoc
>               -- ((assoc . juggle) .) . (. unassoc) . (. (f `cross` id)) . (. juggle) . (`cross` id) . g
> normalize (Loop (RecVarL j f)) = RecVarL j ([|trace|] `o` (ldot juggleE) `o` (rdot juggleE) `o` f)
>               -- \x -> trace (juggle . f x . juggle)
>               -- trace . (juggle .) . (. juggle) . f

Unnecessary stuff
normalize (RecVarL j f :>>> RecVarA g) = RecVarL j (appE (appE [| liftM2 (.) |] (crossId `o` g)) f) 
              -- \x -> (g x `cross` id) . f x
normalize (RecVarA f :>>> RecVarL j g) = RecVarL j (appE (appE [| liftM2 (.) |] g) (crossId `o` f))
              -- \x -> g x . (f x `cross` id)

THESE TWO FUNCTIONS ARE BROKEN
normalize (LoopD i f :>>> RecVarA g) = RecVarL (appE [|(,)|] i) h where
 h = (ldot (assocE `o` juggleE)) `o` (rdot unassocE) `o` (rdot (f `crossE` idE)) `o` (rdot juggleE) `o` crossId `o` crossId `o` g
normalize (RecVarA f :>>> LoopD i g) = RecVarL (appE [|flip (,)|] i) h where
 h = (ldot (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE)) `o` (rdot unassocE) `o` crossId `o` crossId `o` f


All the other cases are unchanged. 

> normalize e = e 

To Let-Expression
=================

Transform function applications to let-expressions.

  (\x -> e1) e2  === let x = e2 in e1

> toLet :: Exp -> Exp
> toLet = G.everywhere (G.mkT aux)
>   where
>     aux (AppE (LamE [pat] body) arg) = LetE [ValD pat (NormalB arg) []] body
>     aux (AppE (LamE (pat:ps) body) arg) = LamE ps (LetE [ValD pat (NormalB arg) []] body)
>     aux x = x

Auxiliary Functions
===================

> dup x = (x, x)
> swap (x, y) = (y, x)
> unassoc (x, (y, z)) = ((x, y), z)
> assoc ((x, y), z) = (x, (y, z))
> juggle ((x, y), z) = ((x, z), y)
> trace f x = let (y, z) = f (x, z) in y
> cross f g (x, y) = (f x, g y)
> mirror (Left x) = Right x
> mirror (Right y) = Left y
> untag (Left x) = x
> untag (Right y) = y
> lft f x = case x of
>   Left  u -> Left (f u)
>   Right u -> Right u 
> tagT (x, y) = case x of
>   Left  u -> Left  (u, y)
>   Right u -> Right (u, y)
> untagT z = case z of
>   Left  (x, y) -> (Left  x, y)
>   Right (x, y) -> (Right x, y)
 
> ldot, rdot :: ExpQ -> ExpQ
> --ldot f === (f .)
> ldot = appE [|(.)|]
> --rdot f === (. f)
> rdot = appE [|flip (.)|]
> dot = [|(.)|]
> crossId = (appE [|flip cross|] idE)

> o :: ExpQ -> ExpQ -> ExpQ
> f `o` g = appE (appE [|(.)|] f) g
> f `crossE` g = appE (appE [|cross|] f) g
> idE :: ExpQ
> idE = [|id|]
> dupE = [|dup|]
> swapE = [|swap|]
> assocE = [|assoc|]
> unassocE = [|unassoc|]
> juggleE = [|juggle|]
> traceE = appE [|trace|]
> tagE = [|tagT|]
> untagE = [|untagT|]
> lftE :: ExpQ -> ExpQ
> lftE = appE [|lft|]

> fixE :: ExpQ -> ExpQ
> fixE = appE [|fix|]


