{-# LANGUAGE GADTs, DataKinds, RankNTypes, KindSignatures, PolyKinds,
    StandaloneDeriving, EmptyCase, TypeOperators, TypeFamilies,
    FlexibleInstances #-}

module HC where

import Data.Kind
import Control.Arrow ((***))

data (<|) (sh :: s -> *)(po :: s -> *)(x :: *) where
  (:<|) :: sh s -> (po s -> x) -> (sh <| po) x

infix 7 <|

data Con (s :: * -> *)(x :: *) where
  (:<!) :: s r -> (r -> x) -> Con p x

instance Functor (sh <| po) where
  fmap f (s :<| k) = s :<| (f . k)

instance Functor (Con s) where
  fmap f (s :<! k) = s :<! (f . k)

data Nat = Z | S Nat

data Natty (n :: Nat) where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)
deriving instance Show (Natty n)

data Fin (n :: Nat) where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)
deriving instance Show (Fin n)

type s -:> t = forall i. s i -> t i

infix 4 -:>

toList :: Natty <| Fin -:> []
toList (Zy   :<| k) = []
toList (Sy n :<| k) = k FZ : toList (n :<| (k . FS))

fromList :: [] -:> (Natty <| Fin)
fromList [] = Zy :<| \ p -> case p of {}
fromList (x : xs) = case fromList xs of
  n :<| k -> Sy n :<| \ p -> case p of
    FZ   -> x
    FS i -> k i

newtype I         x = I {unI :: x}
newtype K a       x = K {unK :: a}
newtype (:+:) f g x = Sum {muS :: Either (f x) (g x)}
newtype (:*:) f g x = Prod {dorP :: (f x , g x)}
infixr 5 :+:
infixr 6 :*:

instance Functor I where
  fmap h (I x) = I (h x)
instance Functor (K a) where
  fmap h (K a) = K a
instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap h = Sum . either (Left . fmap h) (Right . fmap h) . muS
instance (Functor f, Functor g) => Functor (f :*: g) where
  fmap h = Prod . (fmap h *** fmap h) . dorP


data family Morph (f :: * -> *) (g :: * -> *) :: *
data instance Morph (s <| p) (s' <| p')
  = Morph (forall i. s i -> (s' <| p') (p i))

($<$) :: Morph (s <| p) (s' <| p') ->
         (s <| p) -:> (s' <| p')
Morph m $<$ (s :<| k) = fmap k (m s)

morph :: (s <| p -:> s' <| p') -> Morph (s <| p) (s' <| p')
morph f = Morph (\ s -> f (s :<| id))

data Eithery (lefty :: s -> *) (righty :: t -> *) (x :: Either s t) where
  Lefty  :: lefty s   -> Eithery lefty righty (Left s)
  Righty :: righty t  -> Eithery lefty righty (Right t)

inl :: Morph (s0 <| p0) (Eithery s0 s1 <| Eithery p0 p1)
inl = Morph (\ s0 -> Lefty s0 :<| \ p -> case p of Lefty p0 -> p0)

inr :: Morph (s1 <| p1) (Eithery s0 s1 <| Eithery p0 p1)
inr = Morph (\ s1 -> Righty s1 :<| \ p -> case p of Righty p1 -> p1)

toSum :: (s0 <| p0) :+: (s1 <| p1) -:> (Eithery s0 s1 <| Eithery p0 p1)
toSum = either (inl $<$) (inr $<$) . muS

fromSum :: (Eithery s0 s1 <| Eithery p0 p1) -:> (s0 <| p0) :+: (s1 <| p1)
fromSum (Lefty  s0 :<| k0) = Sum (Left  (s0 :<| (k0 . Lefty)))
fromSum (Righty s1 :<| k1) = Sum (Right (s1 :<| (k1 . Righty)))

data Pairy (fsty :: s -> *) (sndy :: t -> *) (x :: (s, t)) where
  Pairy :: fsty s -> sndy t -> Pairy fsty sndy '(s , t)

data Choosy (fsty :: s -> *) (sndy :: t -> *) (x :: (s, t)) where
  ChL :: fsty s -> Choosy fsty sndy '(s, t)
  ChR :: sndy t -> Choosy fsty sndy '(s, t)

toProd :: (s0 <| p0) :*: (s1 <| p1) -:> Pairy s0 s1 <| Choosy p0 p1
toProd (Prod (s0 :<| k0, s1 :<| k1)) = Pairy s0 s1 :<| \ p -> case p of
  ChL p0 -> k0 p0
  ChR p1 -> k1 p1

outL :: Morph (Pairy s0 s1 <| Choosy p0 p1) (s0 <| p0)
outL = Morph (\ p -> case p of Pairy s0 s1 -> s0 :<| ChL)

outR :: Morph (Pairy s0 s1 <| Choosy p0 p1) (s1 <| p1)
outR = Morph (\ p -> case p of Pairy s0 s1 -> s1 :<| ChR)

newtype Compose (f :: * -> *) (g :: * -> *) (x :: *) = C {unC :: f (g x)}

tout :: Pairy s0 s1 <| Pairy p0 p1 -:> Compose (s0 <| p0) (s1 <| p1)
tout (Pairy s0 s1 :<| k) =
  C (s0 :<| \ p0 -> s1 :<| \ p1 -> k (Pairy p0 p1))

twist ::  Pairy s0 s1 <| Pairy p0 p1 -:> Pairy s1 s0 <| Pairy p1 p0
twist (Pairy s0 s1 :<| k) = Pairy s1 s0 :<| \ p -> case p of
  Pairy p1 p0 -> k (Pairy p0 p1)

data Listy (xy :: x -> *) (xs :: [x]) where
  Nily :: Listy xy '[]
  Consy :: xy x -> Listy xy xs -> Listy xy (x ': xs)

type family Append (xs :: [x])(ys :: [x]) :: [x] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

append :: Listy xy xs -> Listy xy ys -> Listy xy (Append xs ys)
append Nily ys = ys
append (Consy x xs) ys = Consy x (append xs ys)

dneppa :: Listy xy xs -> Listy xy ys -> Listy p (Append xs ys) ->
          (Listy p xs, Listy p ys)
dneppa Nily _ ps = (Nily, ps)
dneppa (Consy x xs) ys (Consy p ps) = case dneppa xs ys ps of
  (xp, yp) -> (Consy p xp, yp)

instance Applicative (Listy s <| Listy p) where
  pure x = Nily :<| \ p -> case p of Nily -> x
  (sf :<| kf) <*> (sa :<| ka) = append sf sa :<| \ ps ->
    case dneppa sf sa ps of
      (pf, pa) -> kf pf (ka pa)
