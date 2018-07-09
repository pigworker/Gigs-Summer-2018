module STLC-IR where

data Zero : Set where

record One : Set where constructor <>

data Two : Set where tt ff : Two

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

infixr 4 _,_ _*_

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x




data Ty : Set where
  base : Ty
  _>>_ : Ty -> Ty -> Ty

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X







data Pick {X : Set}(G : Bwd X) : Set
picked : {X : Set}{G : Bwd X} -> Pick G -> X
Pick' : {X : Set}(G : Bwd X) -> Set

data Pick {X} G where
  [_] : Pick' G -> Pick G

Pick' [] = Zero
Pick' (G -, x) = Pick G + One

picked {G = []} [ () ]
picked {G = G -, x} [ tt , i ] = picked i
picked {G = G -, x} [ ff , <> ] = x









data Dir : Set where chk syn : Dir

In Out : Dir -> Set
In chk = Ty
In syn = One
Out chk = One
Out syn = Ty

data Chk : Set where lam emb : Chk
data Syn : Set where var app typ : Syn

Arr : Ty -> (Ty -> Ty -> Set) -> Set
Arr base K = Zero
Arr (S >> T) K = K S T

data Tm (G : Bwd Ty)(d : Dir)(i : In d) : Set
out : forall {G}{d}{i : In d} -> Tm G d i -> Out d
Tm' : (G : Bwd Ty)(d : Dir)(i : In d) -> Set

data Tm G d i where
  [_] : Tm' G d i -> Tm G d i

Tm' G chk R = Sg Chk \
   { lam -> Arr R \ S T -> Tm (G -, S) chk T
   ; emb -> Sg (Tm G syn <>) \ e -> out e == R
   }
Tm' G syn <> = Sg Syn \
   { var -> Pick G
   ; app -> Sg (Tm G syn <>) \ f -> Arr (out f) \ S T -> Tm G chk S
   ; typ -> Sg Ty \ T -> Tm G chk T
   }

out {G} {chk} {i} _                              = <>
out {G} {syn} {i} [ var , x ]                    = picked x
out {G} {syn} {i} [ app , f , s ]   with out f
out {G} {syn} {i} [ app , f , () ]     | base
out {G} {syn} {i} [ app , f , s ]      | S >> T  = T
out {G} {syn} {i} [ typ , T , t ]                = T

