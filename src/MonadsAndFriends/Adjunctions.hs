{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
module MonadsAndFriends.Adjunctions where


import Control.Comonad


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
-- monads and comonads. More on that on this section.

-- The `Reader` monad helps us abstract over functions that
-- take some read-only "environment" and produce some overall
-- result.
newtype Reader e r = Reader { runReader :: e -> r }
  deriving (Functor, Applicative, Monad)

-- Given this, we can define functions to produce `Reader`s,
-- allowing us to add more information. The most general form
-- would be `a -> Reader e r`.
extra :: Int -> Reader [Int] Int
extra x = Reader \xs -> sum $ x : xs

fourtyTwo :: Int
fourtyTwo = runReader (extra 2) [20, 20]

-- As an exercise, we can "unwrap" the inner function type from
-- the `Reader` monad and use that instead. This gives us the
-- general form of `a -> e -> r`.
extra' :: Int -> [Int] -> Int
extra' x xs = sum $ x : xs

fourtyTwo' :: Int
fourtyTwo' = extra' 2 [20, 20]

-- As another exercise, we then uncurry the `extra'` function.
-- This would then give us the general form of `(a, e) -> r`.
extra'' :: (Int, [Int]) -> Int
extra'' = uncurry extra'

-- With this in mind, let's look at these two forms:
--
-- a -> e -> r
-- (a, e) -> r
--
-- We learned earlier that we can form an adjunction between
-- the `(->) a` and `(,) a` functors, but before we proceed,
-- we have to adjust something first:
--
-- `(a, e) -> r` into `(e, a) -> r`
--
-- Remember that the adjunction between `(->) a` and `(,) a`
-- isn't just `curry`-ing and `uncurry`-ing functions, but
-- rather, it also involves flipping the arguments.
--
-- This gives us our new pair of functions:
--
-- a -> e -> r
-- (e, a) -> r
--
-- When generalized:
--
-- a -> f r
-- g a -> r
--
-- We lose some type information by replacing `(->) e` and `(,) e`
-- with `f` and `g` respectively, but we can assume that `f` and
-- `g` both consumes `e`. This will be useful in the next section.
--
-- That signature looks just like an adjunction!
--
-- One question that can be asked is: if we found the adjunction
-- for `a -> e -> r`, which is abstracted into `a -> Reader e r`,
-- could we define such a data type that abstracts over the
-- adjunction of the former?

-- First, let's define `Env` which is a simple product type of `e`
-- and `a`, that's also a `Functor`.
data Env e a = Env e a deriving (Functor)

-- We then define the "runner" function to extract an `Env` into a
-- familar-looking tuple.
runEnv :: Env e a -> (e, a)
runEnv (Env e a) = (e, a)

-- As well as a "constructor" function to create an `Env` from a
-- familiar-looking tuple.
env' :: (e, a) -> Env e a
env' (e, a) = Env e a

-- After which, we'll  prove that there exists an `Adjunction` between
-- the functors `Env e` and `Reader e`. Remember that `Env e` and
-- `Reader e` simply abstracts over the functors `(,) e` and `(->) e`.
instance Adjunction (Env e) (Reader e) where
  leftAdjunct :: (Env e a -> b) -> (a -> Reader e b)
  leftAdjunct f a  = Reader \e -> f $ Env e a

  rightAdjunct :: (a -> Reader e b) -> (Env e a -> b)
  rightAdjunct f e = r e'
    where
      (e', a) = runEnv e
      r = runReader $ f a

-- Let's define some types for convenience and clarity.
type Extra  = Int
type Input  = [Int]
type Result = Float

-- We'll define a "reader-like" function with the following
-- signature.
readerEx_ :: Extra -> Input -> Result
readerEx_ x xs = realToFrac . sum $ x : xs

-- Naturally, we're able to find its adjunction by applying
-- the `rightAdjunct` function.
envEx_ :: (Input, Extra) -> Result
envEx_ = rightAdjunct readerEx_

-- We can then use `Reader` to abstract over the other half
-- of this function, giving us the full power of the `Reader`
-- monad.
readerEx :: Extra -> Reader Input Result
readerEx x = Reader $ readerEx_ x

-- We're also able to find its adjunction by applying the
-- `rightAdjunct` function.
envEx :: Env Input Extra -> Result
envEx = rightAdjunct readerEx

-- With this more complex example out of the way, what more do
-- we have to know about adjunctions. Well, looking at the
-- type signature of `leftAdjunct` and `rightAdjunct`:
--
-- leftAdjunct  :: (f a -> b) -> (a -> g b)
-- rightAdjunct :: (a -> g b) -> (f a -> b)
--
-- We can define yet another relationship between these two;
-- that is, the `leftAdjunct` morphism is the dual of the
-- `rightAdjunct` morphism and vice-versa.

-- For the following section, let's define a comonad instance
-- for the `Env` functor.
instance Comonad (Env e) where
  extract :: Env e a -> a
  extract = snd . runEnv

  duplicate :: Env e a -> Env e (Env e a)
  duplicate env@(Env e r) = Env e env

  extend :: (Env e a -> b) -> Env e a -> Env e b
  extend f a = let b = f a
                   e = fst . runEnv $ a
                in Env e b

-- Given what we know about adjunctions and how they ultimately
-- for duals between functors, what can be infer about the `Reader`
-- monad and the `Env` comonad, given that they're adjunct with
-- each other?
--
-- This ultimately proves that monads are duals of comonads and
-- vice-versa.
--
-- If we look at `return :: a -> m a`, which has the comonadic
-- dual called `extract :: w a -> a`, we can see that in the
-- type signature of our adjunctions, namely, `a -> Reader e r`
-- and `Env e a -> r`.
