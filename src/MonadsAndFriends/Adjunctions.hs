{-# LANGUAGE FunctionalDependencies #-}
module MonadsAndFriends.Adjunctions where


-- An adjunction is a relationship between two functors `f`
-- and `g` that states there is an isomorphism between:
--
-- `f a -> b` <=> `a -> g b`
--
-- An isomorphism can be thought of a reversible change in
-- structure without loss of information. In -- our case,
-- `f a -> c` can easily be converted into `a -> g c`,
-- while preserving information, and vice-versa.


-- Adjunctions in Haskell can be defined through the
-- `Adjunction` typeclass:
class (Functor f, Functor g) => Adjunction f g | f -> g, g -> f
  where
    leftAdjunct  :: (f a -> b) -> (a -> g b)
    rightAdjunct :: (a -> g b) -> (f a -> b)

-- Instances also satisfy the following laws:
--
-- leftAdjunct . rightAdjunct = id
-- rightAdjunct . leftAdjunct = id


-- One such example of an adjunction is that of the `(,) a`
-- and `(->) a` functors, which is demonstrated by the `curry`,
-- and the `uncurry` functions.
--
-- curry
--   :: ((a, b) -> c)
--   -> (a -> b -> c)
--
-- uncurry
--   :: (a -> b -> c)
--   -> ((a, b) -> c)
--
-- In our case, the "change in structure" would be how we call
-- our function, but nonetheless, information is preserved and
-- the following holds true:
--
-- curry . uncurry = id
-- uncurry . curry = id
--
--
-- With this in mind, we can define an `Adjunction` instance
-- between `(,) a` and `(->) a`, given `curry` and `uncurry`:
instance Adjunction ((,) a) ((->) a) where
  leftAdjunct  f  a  b  = f (b, a)
  rightAdjunct f (b, a) = f  a  b

-- The adjunction is not as straightforward as just doing `curry`
-- and `uncurry`, it also involves the arguments being flipped for
-- every conversion. This flip makes sure that the adjunction is
-- satisfied:
--
-- `(z -> a -> b)` into `(a -> z -> b)` into `a -> g b`
--
-- and
--
-- `(z, a) -> b` into `f a -> b`

-- Why do these relationships matter to us? Interestingly
-- enough, these adjunctions form the relationships between
-- monads and comonads. More on that on this section. TODO.
