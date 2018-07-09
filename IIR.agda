module IIR where

open import Agda.Primitive

{---------------------------------------------------------------







    Irish Induction-Recursion

      (what is it?)

        (and what has it to do with session types?)












---------------------------------------------------------------}


{--------------------------------------------------------------}
-- Some Combinators

id : forall {l}{X : Set l} -> X -> X
id x = x

kk : forall {i j}{X : Set i}{Y : Set j} ->
       (x : X) -> Y -> X
kk x y = x

_<<_ : forall {i j k}
       {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
       (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
       (a : A) -> C a (g a)
(f << g) a = f (g a)

_>>_ : forall {i j k}
       {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
       (g : (a : A) -> B a)(f : {a : A}(b : B a) -> C a b) ->
       (a : A) -> C a (g a)
(g >> f) a = f (g a)
infixr 5 _>>_










{--------------------------------------------------------------}
-- 0, 1, +

data Zero {l} : Set l where

record One {l} : Set l where  constructor <>

data Two {l} : Set l where tt ff : Two
















{--------------------------------------------------------------}
-- Sigma

record Sg {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S  
    snd : T fst
open Sg public

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

infixr 4 _,_ _*_

swap : {I J : Set} -> I * J -> J * I
swap (i , j) = j , i











{--------------------------------------------------------------}
-- Agda is not cumulative, so we must make do

record Up {l}(X : Set l) : Set (lsuc l) where
  constructor up
  field
    down : X

open Up



















{--------------------------------------------------------------}
-- Numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
  
{-# BUILTIN NATURAL Nat #-}

_!N=_ : Nat -> Nat -> Set
zero  !N= zero   = Zero
zero  !N= suc _  = One
suc _ !N= zero   = One
suc x !N= suc y  = x !N= y












{--------------------------------------------------------------}
module IIR (I : Set)(J : I -> Set1) where

  data Desc : Set1        -- big
  Approx : Desc -> Set1   -- big underapproximation of content

  data Desc where
    var : (i : I) -> Desc
    kon : (A : Set) -> Desc
    sg  : (S : Desc)(T : Approx S -> Desc) -> Desc
    pi  : (A : Set)(T : A -> Desc) -> Desc

  Approx (var i)   = J i
  Approx (kon A)   = Up A
  Approx (sg S T)  = Sg (Approx S) \ s -> Approx (T s)
  Approx (pi A T)  = (a : A) -> Approx (T a)

  -- comment on variations









{--------------------------------------------------------------}
  module DATA (F : I -> Desc)                      -- it says
              (f : (i : I) -> Approx (F i) -> J i) -- it means
              where
{-(-}
    data Data (i : I) : Set
    decode : {i : I} -> Data i -> J i
    
    Node   : Desc -> Set                       -- small content
    approx : (D : Desc) -> Node D -> Approx D

    data Data i where
      <_> : Node (F i) -> Data i
    decode {i} < node > = f i (approx (F i) node)

    Node   (var i)  = Data i
    Node   (kon A)  = A
    Node   (sg S T) = Sg (Node S) \ s -> Node (T (approx S s))
    Node   (pi A T) = (a : A) -> Node (T a)
    approx (var i) d        = decode d
    approx (kon A)  a       = up a
    approx (sg S T) (s , t) = let s' = approx S s in
      s' , approx (T s') t
    approx (pi A T) f a     = approx (T a) (f a)
{-)-}




{--------------------------------------------------------------}
-- example
open IIR One (\ _ -> Nat -> Set)

{-(-}
DLIST : One {lzero} -> Desc
DLIST <> = sg (kon Two) \
       { (up tt) -> sg (kon Nat) \ n ->
                    sg (var <>) \ Fresh ->
                    kon (Fresh (down n))
       ; (up ff) -> kon One}

Fresh : Approx (DLIST <>) -> Nat -> Set
Fresh (up tt , up m , Fresh' , _) n = m !N= n * Fresh' n
Fresh (up ff , up <>) n = One

open DATA DLIST (\ _ -> Fresh)

pattern [] = < ff , <> >
pattern _,-_ n ns = < tt , n , ns , _ >
infixr 4 _,-_

tryit : Data <>
tryit = 1 ,- 2 ,- 3 ,- 2 ,- []
{-)-}

-- now switch to Session.agda
