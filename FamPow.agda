module FamPow where

Pow : Set1 -> Set1
Pow X = X -> Set

record Sg {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_

Fam : Set1 -> Set1
Fam X = Sg Set \ I -> I -> X

data Zero : Set where

record One : Set where constructor <>

data Two : Set where tt ff : Two

record Up (X : Set) : Set1 where
  constructor up
  field
    down : X
open Up

emptyP : Pow (Up Two)
emptyP (up b) = Zero

ttP : Pow (Up Two)
ttP (up tt) = One
ttP (up ff) = Zero

ffP : Pow (Up Two)
ffP (up ff) = One
ffP (up tt) = Zero

fullP : Pow (Up Two)
fullP (up b) = One

emptyF : Fam (Up Two)
emptyF = Zero , \ ()

ttF : Fam (Up Two)
ttF = One , \ _ -> up tt

ffF : Fam (Up Two)
ffF = One , \ _ -> up ff

fullF : Fam (Up Two)
fullF = Two , up

_$_ : Fam Set -> Set -> Set
(S , P) $ X = Sg S \ s -> P s -> X

data W (C : Fam Set) : Set where
  [_] : C $ (W C) -> W C

C-NAT : Fam Set
C-NAT = Two , \ { tt -> One ; ff -> Zero }

Nat = W C-NAT
zero : Nat
zero = [ ff , (\ ()) ]
suc : Nat -> Nat
suc n = [ tt , (\ _ -> n) ]

data W' (C : Pow Set) : Set1 where
  _<!_ : {R : Set} -> C R -> (R -> W' C) -> W' C

module PST  -- Petersson-Synek Trees
  (S : Set)
  (F : S -> Fam Set)
  (next : (s : S)(c : fst (F s))(r : snd (F s) c) -> S)
  where

  data Strategy (G : S -> Set)(s : S) : Set where
    skip : G s -> Strategy G s
    do   : (c : fst (F s))(k : (r : snd (F s) c) -> Strategy G (next s c r)) -> Strategy G s

  _=<<_ : forall {P Q} ->
            ({s : S} -> P s -> Strategy Q s) ->
             {s : S} -> Strategy P s -> Strategy Q s
  f =<< skip p = f p
  f =<< do c k = do c \ r -> f =<< k r
