{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExplicitNamespaces #-}
{- |

This package (for now) is a companion to

 1. [de Oliveira et al, 2022, /On Structuring Functional Programs with Monoidal Profunctors/](https://arxiv.org/pdf/2207.00852.pdf#page=6)
 2. [de Oliveira et al, 2023, /Programming with Monoidal Profunctors and Semiarrows/](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=4496714)

intended to fill in some of the typos or omitted pieces of implementation and
allow the reader to work with the Haskell contained in those papers or with
analogues defined in existing Haskell packages: the package is not a
self-contained or self-documenting guide to the content of those papers, and
doesn't (for now) contain more than a few basic examples. It does however, give
you some tools to define those examples for yourself. (PRs are welcome!)

Below are correspondences between types and identifiers in the papers and
existing Haskell packages — chiefly @profunctors@ and @product-profunctors@.


== Morphisms in @Prof@

The type for morphisms in @Prof@ of
(de Oliveira et al 2022, p. 6)[https://arxiv.org/pdf/2207.00852.pdf#page=6]

> type (⇝) p q = ∀ x y. p x y → q x y

corresponds to ':->' in @profunctors@.

== SISO

@SISO@ seems (perhaps at least superficially) to correspond to @DoubleStar@ in
@proton@.

== @MonoPro@

@MonoPro@ of de Oliveira et al corresponds to 'ProductProfunctor' of
@product-profunctors@, where

 - @mpempty@ corresponds to 'empty'.
 - @★@ corresponds to '***!'.
 - 'diag' (a helper function in de Oliveira et al) corresponds to
   @dup == id &&& id == \x → (x,x)@.
 - 'lmap2', 'rmap', 'rlmap' are defined below.
 - @appToMonoPro@  in de Oliveira et al. corresponds to '***!'.
 - @zip'@ corresponds to @uncurry $ liftA2 (,)@.
 - @unzip'@ corresponds to 'unzip' from @Data.List.NonEmpty@.

== @CatProfunctor@

The @CatProfunctor@ type of de Oliveira et al is a special case of the
profunctors in @vitrea@, which allow for constraints and allow for @f@ and @g@
in @dimap f g p@ to be morphisms from /two/ distinct categories.

== @Semiarrow@

I haven't spent any time thinking about the mathematical interpretation, but any
@FreeMP@

 1. ...that is also a @Semigroupoid@.
 2. ...and where the semigroupoid composition satisfies the interchange and
    idempotence laws mentioned in de Oliveira et al 2023, §8.4

would seem to be a @Semiarrow@.

-}

module Data.Profunctor.Product.Extras
  ( assocR
  , assocL
  , MonoPro
  , (★)
  , lmap2
  , rmap2
  , rlmap
  , SISO (SISO, unSISO)
  , Day (Day)
  , FreeMP (MPempty, FreeMP)
  , toFreeMP
  , foldFreeMP
  , consMP
  , CatProfunctor (catdimap)
  , CatMonoPro (cmpunit, convolute)
  , cmpempty
  , (★★)
  , (**!)
  , Lift (Lift, runLift)
  , Semiarrow
  , o
  ) where

import Prelude hiding (id, (.), unzip)

import GHC.Generics (Generic)


import Control.Arrow (Arrow, arr, (***), Kleisli (Kleisli))
import Control.Category (Category, id, (.))
import Control.Category.Unicode ((∘))
import Data.Semigroupoid (Semigroupoid, o)

import Control.Composition (dup)
import Data.List.NonEmpty (unzip)

import Control.Applicative (liftA2)
import Control.Monad.Trans (MonadTrans, lift)

import Data.Profunctor ( Profunctor(..), type (:->) )
import Data.Profunctor.Product ( ProductProfunctor(empty, (***!)) )
import Data.Profunctor.Composition (Procompose(Procompose), procomposed)


assocR ∷ ((a,b),c) → (a,(b,c))
assocR ((a,b),c) = (a,(b,c))

assocL ∷ (a,(b,c)) → ((a,b),c)
assocL (a,(b,c)) = ((a,b),c)


type MonoPro = ProductProfunctor

(★) ∷ MonoPro p ⇒ a `p` b → a' `p` b' → (a, a') `p` (b, b')
(★) = (***!)

lmap2 ∷ MonoPro p ⇒ (s → (a,c)) → p a b → p c d → p s (b,d)
lmap2 f pa pc = dimap f id (pa ★ pc)

rmap2 ∷ MonoPro p ⇒ ((b,d) → t) → p a b → p c d → p (a,c) t
rmap2 f pa pc = dimap id f (pa ★ pc)

-- Mind the type signature typo in the arxiv preprint, corrected here.
rlmap ∷ MonoPro p ⇒ (s → (a,c)) → ((b,d) → t) → p a b → p c d → p s t
rlmap f g pa pc = dimap f g (pa ★ pc)



data SISO f g a b = SISO { unSISO ∷ f a → g b }
  deriving stock (Generic)

instance (Functor f, Functor g) ⇒ Profunctor (SISO f g) where
  dimap ab cd (SISO bc) = SISO (fmap cd ∘ bc ∘ fmap ab)

data Day p q s t = ∀ a b c d. Day (p a b) (q c d) (s → (a,c)) (b → d → t)


instance (Functor f, Applicative g) ⇒ ProductProfunctor (SISO f g) where
  empty = SISO (const . pure $ ())
  SISO f ***! SISO g = SISO (zip' ∘ (f ★ g) ∘ unzip)
    where zip' ∷ (g a, g b) → g (a, b)
          zip' = uncurry $ liftA2 (,)



data FreeMP p s t where
  MPempty ∷ t → FreeMP p s t
  FreeMP ∷ (s → (x,z)) → ((y,w) → t) → p x y → FreeMP p z w → FreeMP p s t

toFreeMP ∷ p s t → FreeMP p s t
toFreeMP p = FreeMP dup fst p (MPempty ())

foldFreeMP ∷ (Profunctor p, MonoPro q) ⇒ (p :-> q) → FreeMP p s t → q s t
foldFreeMP _ (MPempty t)       = dimap (const ()) (const t) empty
foldFreeMP h (FreeMP f g p mp) = dimap f          g         (h p ★ foldFreeMP h mp)

consMP ∷ Profunctor p ⇒ p a b → FreeMP p s t → FreeMP p (a,s) (b,t)
consMP pab (MPempty t       ) = FreeMP  id       id       pab (MPempty t  )
consMP pab (FreeMP  f g p fp) = FreeMP (id ★ f) (id ★ g) pab (consMP p fp)

-- | A profunctor instance for 'FreeMP' is not present in either de Oliveira et al
-- paper. Note that the instance given here does not depend on 'p' being a
-- profunctor.
instance Profunctor (FreeMP p) where
  lmap ∷ (a → b) → FreeMP p b c → FreeMP p a c
  lmap _  (MPempty c                ) = MPempty c
  lmap ab (FreeMP  bxz ywc pxy fmpzw) = FreeMP (bxz . ab) ywc pxy fmpzw
  rmap ∷ (b → c) → FreeMP p a b → FreeMP p a c
  rmap bc (MPempty b                ) = MPempty $ bc b
  rmap bc (FreeMP  axz ywb pxy fmpzw) = FreeMP axz (bc . ywb) pxy fmpzw

instance Profunctor p ⇒ ProductProfunctor (FreeMP p) where
  empty = MPempty ()
  (MPempty t) ***! q        = dimap snd (t,) q
  q ***! (MPempty t)        = dimap fst (,t) q
  (FreeMP f g p fp) ***! fq = dimap (assocR ∘ (f ★ id))
                                    ((g ★ id) ∘ assocL)
                                    (consMP p (fp ★ fq))

-- | The composition definition in both de Oliveira papers references identifiers
-- not defined anywhere in those papers.
instance (MonoPro p, Arrow p) ⇒ Category (FreeMP p) where
  id ∷ FreeMP p a a
  id = FreeMP (,()) fst (arr id) (MPempty ())

  (.) ∷ FreeMP p b c → FreeMP p a b → FreeMP p a c
  (MPempty c)                . _           = MPempty c
  (FreeMP bxz ywc pxy fmpzw) . (MPempty b) = FreeMP (bxz . const b) ywc pxy fmpzw
  f                          . g           = procomposed $ Procompose f g

instance (MonoPro p, Arrow p) ⇒ Arrow (FreeMP p) where
  arr f = FreeMP (,()) fst (arr f) (MPempty ())
  (***) = (★)


class Category k ⇒ CatProfunctor k p where
  catdimap ∷ k a b → k c d → p b c → p a d

class (Category k, CatProfunctor k p) ⇒ CatMonoPro k p | p → k where
  cmpunit ∷ k s () → k () t → p s t
  convolute ∷ k s (a,c) → k (b,d) t → p a b → p c d → p s t

cmpempty ∷ ∀ k p. CatMonoPro k p ⇒ p () ()
cmpempty = cmpunit id id

(★★) ∷ CatMonoPro k p ⇒ p a b → p c d → p (a,c) (b,d)
p ★★ q = convolute id id p q

-- What's a few more star operators among friends?
(**!) ∷ CatMonoPro k p ⇒ p a b → p c d → p (a,c) (b,d)
(**!) = (★★)



newtype Lift t m a b = Lift { runLift ∷ m a → t m b }

instance (MonadTrans t, Monad m, Monad (t m)) ⇒ CatProfunctor (Kleisli m) (Lift t m) where
  catdimap (Kleisli f) (Kleisli g) (Lift h) = Lift $
    \ma → let
      k = h (ma >>= f)
      l = lift ∘ g
    in
      k >>= l


-- | Note that — per de Oliveira et al 2023, §8.4, a 'MonoPro' instance with a
-- notion of (associative) sequential composition must also have a lawful
-- interaction of sequential composition with its notion of parallel composition
-- (the interchange law) and with its identity element (the idempotence law):
-- that is, *not* every 'MonoPro' which is also a 'Semigroupoid' is necessarily a
-- 'Semiarrow'.
class (MonoPro p, Semigroupoid p) ⇒ Semiarrow p

