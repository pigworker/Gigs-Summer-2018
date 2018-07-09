module Space where

{---------------------------------------------------------------






     +-------------------+
     |                   |
     |   S P A C E       |--------------------+
     |                   |                    |
     +-------------------+                    |
               |            m o n a d s !     |
               |                              |
               +------------------------------+










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

data Zero : Set where

record One : Set where  constructor <>

data _+_ (S : Set)(T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

_+map_ : forall {S S' T T'} ->
         (S -> S') -> (T -> T') -> S + T -> S' + T'
(f +map g) (inl x) = inl (f x)
(f +map g) (inr x) = inr (g x)

_<+>_ : forall {l}{S T}{P : S + T -> Set l}
        (f : (s : S) -> P (inl s))
        (g : (t : T) -> P (inr t)) ->
        (x : S + T) -> P x
(f <+> g) (inl s) = f s
(f <+> g) (inr t) = g t






{--------------------------------------------------------------}
-- Sigma

record Sg (S : Set)(T : S -> Set) : Set where
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
-- Catholicism

data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x

{-# BUILTIN EQUALITY _==_ #-}

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl f =$= refl x = refl (f x)

infixl 2 _=$=_

sym : {X : Set}{x y : X} -> x == y -> y == x
sym (refl x) = refl x

_[QED] : {X : Set}(x : X) -> x == x
x [QED] = refl x
_=[_>=_ : {X : Set}(x : X){y z : X} ->
  x == y -> y == z -> x == z
x =[ refl .x >= q = q
_=<_]=_ : {X : Set}(x : X){y z : X} ->
  y == x -> y == z -> x == z
x =< refl .x ]= q = q
infixr 1 _=[_>=_ _=<_]=_
infixr 2 _[QED]



{--------------------------------------------------------------}
-- Numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
  
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc x +N y = suc (x +N y)

sucInj : {x y : Nat} -> suc x == suc y -> x == y
sucInj (refl (suc _)) = refl _

ind : (n : Nat)(P : Nat -> Set) -> P zero ->
         ((k : Nat) -> P k -> P (suc k)) -> P n
ind zero P pz ps = pz
ind (suc n) P pz ps = ps n (ind n P pz ps)

+N-zero : (x : Nat) -> (x +N zero) == x
+N-zero x = ind x (\ x -> (x +N zero) == x)
  (refl _)
  (\ _ h -> refl suc =$= h)

+N-suc : (x y : Nat) -> (x +N suc y) == suc (x +N y)
+N-suc x y = ind x (\ x -> (x +N suc y) == suc (x +N y))
  (refl _)
  (\ _ h -> refl suc =$= h)

comm-+N : (x y : Nat) -> (x +N y) == (y +N x)
comm-+N x zero = +N-zero x
comm-+N x (suc y) rewrite +N-suc x y = refl suc =$= comm-+N x y










{--------------------------------------------------------------}
-- Lists

data List (X : Set) : Set where
  []   : List X
  _,-_ : (x : X)(xs : List X) -> List X
infixr 4 _,-_
{-# COMPILE GHC List = data [] ([] | (:)) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _,-_ #-}

list : forall {X Y : Set} -> (X -> Y) -> List X -> List Y
list f [] = []
list f (x ,- xs) = f x ,- list f xs

_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
infixr 4 _+L_

cart : forall {I J} -> List I -> List J -> List (I * J)
cart [] js = []
cart (i ,- is) js = list (i ,_) js +L cart is js







{--------------------------------------------------------------}
-- Some results about lists

catNatural : {X Y : Set}(f : X -> Y)(xs xs' : List X) ->
  (list f xs +L list f xs') == list f (xs +L xs')
catNatural f [] xs' = refl (list f xs')
catNatural f (x ,- xs) xs' = refl (f x ,-_) =$= catNatural f xs xs'

listlist : {X Y Z : Set}(f : Y -> Z)(g : X -> Y)(h : X -> Z)
  (q : (x : X) -> f (g x) == h x) ->
  (xs : List X) -> list f (list g xs) == list h xs
listlist f g h q [] = refl []
listlist f g h q (x ,- xs) = refl (_,-_) =$= q x =$= listlist f g h q xs


_+L[] : {X : Set}(xs : List X) -> (xs +L []) == xs
[] +L[] = refl []
(x ,- xs) +L[] = refl (x ,-_) =$= (xs +L[])

assoc+L : {X : Set}(xs ys zs : List X) -> ((xs +L ys) +L zs) == (xs +L ys +L zs)
assoc+L [] ys zs = refl (ys +L zs)
assoc+L (x ,- xs) ys zs = refl (x ,-_) =$= assoc+L xs ys zs





{--------------------------------------------------------------}
-- Booleans are necessary, for some reason

data Two : Set where tt ff : Two
{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

-- nondependent conditional with traditional syntax
if_then_else_ : forall {l}{X : Set l} -> Two -> X -> X -> X
if tt then t else e = t
if ff then t else e = e

-- dependent conditional cooked for partial application
caseTwo : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
caseTwo t f tt = t
caseTwo t f ff = f










{--------------------------------------------------------------}
-- Characters and Strings

postulate       -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String












{--------------------------------------------------------------}
-- This Indexed Life

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i
infixr 4 _-:>_

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i

Algebra : {I : Set}(F : (I -> Set) -> (I -> Set)) -> (I -> Set) -> Set
Algebra F X = [ F X -:> X ]


















{--------------------------------------------------------------}
-- something ALL THE THINGS

All : {X : Set} -> (X -> Set) -> (List X -> Set)
All P []        = One
All P (x ,- xs) = P x * All P xs

allPu : forall {X}{T : X -> Set} -> [ T ] -> [ All T ]
allPu t [] = <>
allPu t (x ,- xs) = t x , allPu t xs

allAp : forall {X}{S T : X -> Set} ->
        [ All (S -:> T) -:> All S -:> All T ]
allAp [] <> <> = <>
allAp (x ,- xs) (f , fs) (s , ss) = f s , allAp xs fs ss

all : {X : Set}{S T : X -> Set} ->
      [ S -:> T ] -> [ All S -:> All T ]
all f xs = allAp xs (allPu f xs)









{--------------------------------------------------------------}
-- flotsam

allRe : forall {X Y}(f : X -> Y){P : Y -> Set}
        (xs : List X) -> All (\ x -> P (f x)) xs -> All P (list f xs)
allRe f [] <> = <>
allRe f (x ,- xs) (p , ps) = p , allRe f xs ps

collect : {I J : Set}(is : List I) -> All (\ i -> List J) is -> List J
collect [] <> = []
collect (i ,- is) (js , jss) = js +L collect is jss















{--------------------------------------------------------------}
-- How to cut stuff up

record _|>_ (I O : Set) : Set1 where
  constructor _/_
  field
    Cuts   : O -> Set
    inners : {o : O} -> Cuts o -> List I

NatCut : Nat |> Nat
NatCut = record
  { Cuts   = \ mn -> Sg Nat \ m -> Sg Nat \ n -> (m +N n) == mn
  ; inners = \ { (m , n , _) -> m ,- n ,- [] }
  }















{--------------------------------------------------------------}
-- Cuttings

record Cutting {I O}(C : I |> O)(P : I -> Set)(o : O) : Set where
  constructor _8><_
  open _|>_ C
  field
    cut     : Cuts o
    pieces  : All P (inners cut)
infixr 3 _8><_
open Cutting public




















{--------------------------------------------------------------}
module INTERIOR {I}(C : I |> I) where

  open _|>_ C

  data Interior (P : I -> Set)(i : I) : Set where
    tile : P i -> Interior P i
    <_>  : Cutting C (Interior P) i -> Interior P i

  ifold : forall {P Q} ->
          [ P -:> Q ] ->
          [ Cutting C Q -:> Q ] ->
          [ Interior P -:> Q ]
  ifolds : forall {P Q} ->
          [ P -:> Q ] ->
          [ Cutting C Q -:> Q ] ->
          [ All (Interior P) -:> All Q ]
  ifold pq cq i (tile p) = pq i p
  ifold pq cq i < c 8>< ps > = cq i (c 8>< ifolds pq cq _ ps)
  ifolds pq cq [] <> = <>
  ifolds pq cq (i ,- is) (x , xs) =
    ifold pq cq i x , ifolds pq cq is xs









{--------------------------------------------------------------}
-- Interior is a (free) monad

  -- tile : [ P -:> Interior P ]

  extend : forall {P Q} ->
          [ P -:> Interior Q ] ->
          [ Interior P -:> Interior Q ]
  extend k = ifold k (\ i x -> < x >)

  -- go for interior example

















{--------------------------------------------------------------}
-- Hancockiana

_>|_ : forall {I O} -> (I |> O) ->
       forall J -> (I * J) |> (O * J)

_|>_.Cuts   ((C / is) >| J) (o , j) = C o
_|>_.inners ((C / is) >| J) {o , j} c = list (_, j) (is c)

_|<_ : forall {I O} J -> (I |> O) ->
       (J * I) |> (J * O)
_|>_.Cuts   (J |< (C / is)) (j , o) = C o
_|>_.inners (J |< (C / is)) {j , o} c = list (j ,_) (is c)

_>+<_ : forall {I O} -> (I |> O) -> (I |> O) -> (I |> O)
_|>_.Cuts   ((C / is) >+< (D / js)) o = C o + D o
_|>_.inners ((C / is) >+< (D / js))   = is <+> js

_|+|_ : forall {I J} -> (I |> I) -> (J |> J) ->
                        (I * J) |> (I * J)
_|+|_ {I}{J} Cis Djs = (Cis >| J) >+< (I |< Djs)

RectCut = NatCut |+| NatCut




{--------------------------------------------------------------}
module CUTKIT {I}(C : I |> I) where

  open _|>_

  CutKit : (I -> Set) -> Set
  CutKit P = (i : I)(c : Cuts C i) -> P i -> All P (inners C c)

-- go to RECUTTER




















{--------------------------------------------------------------}
-- Splittings

data _<[_]>_ {X : Set} : List X -> List X -> List X -> Set where
  sz : [] <[ [] ]> []
  sl : forall {l ls ms rs} ->      ls <[      ms ]> rs
                           -> l ,- ls <[ l ,- ms ]> rs
  sr : forall {r ls ms rs} ->      ls <[      ms ]>      rs
                           ->      ls <[ r ,- ms ]> r ,- rs

infixr 3 _<[_]>_

srs : forall {X : Set}(xs : List X) -> [] <[ xs ]> xs
srs []        = sz
srs (x ,- xs) = sr (srs xs)

slrs : forall {X : Set}(xs ys : List X) -> xs <[ xs +L ys ]> ys
slrs []        ys = srs ys
slrs (x ,- xs) ys = sl (slrs xs ys)







splimap : forall {X Y}(f : X -> Y){xs xys ys} -> xs <[ xys ]> ys ->
           list f xs <[ list f xys ]> list f ys
splimap f sz = sz
splimap f (sl s) = sl (splimap f s)
splimap f (sr s) = sr (splimap f s)







mirror : {X : Set}{ls ms rs : List X} -> ls <[ ms ]> rs -> rs <[ ms ]> ls
mirror sz = sz
mirror (sl x) = sr (mirror x)
mirror (sr x) = sl (mirror x)

rotatel : {X : Set}{ls ms rs lrs rrs : List X} -> ls <[ ms ]> rs -> lrs <[ rs ]> rrs ->
  Sg (List X) \ ns -> (ls <[ ns ]> lrs) * (ns <[ ms ]> rrs)
rotatel sz sz = [] , sz , sz
rotatel (sl x) y with rotatel x y
... | _ , a , b = _ , sl a , sl b
rotatel (sr x) (sl y) with rotatel x y
... | _ , a , b = _ , sr a , sl b
rotatel (sr x) (sr y) with rotatel x y
... | _ , a , b = _ , a , sr b

rotater : {X : Set}{lls rls ls ms rs : List X} -> lls <[ ls ]> rls -> ls <[ ms ]> rs -> 
  Sg (List X) \ ns -> (lls <[ ms ]> ns) * (rls <[ ns ]> rs)
rotater x y with rotatel (mirror y) (mirror x)
... | _ , a , b = _ , mirror b , mirror a 


llswap : {X : Set}{ls ms lrs rrs : List X} ->
 (Sg (List X) \ rs -> (ls <[ ms ]> rs) * (lrs <[ rs ]> rrs)) ->
  Sg (List X) \ ns -> (lrs <[ ms ]> ns) * (ls <[ ns ]> rrs)
llswap (_ , x , y) with rotatel x y
... | _ , a , b = rotater (mirror a) b

insS : {X : Set}(xs : List X)(y : X)(zs : List X) -> (y ,- []) <[ (xs +L y ,- zs) ]> (xs +L zs)
insS [] y zs = sl (srs zs)
insS (x ,- xs) y zs = sr (insS xs y zs)

catS : forall {X}{as abs bs cs cds ds : List X} ->
        as <[ abs ]> bs -> cs <[ cds ]> ds ->
        (as +L cs) <[ (abs +L cds) ]> (bs +L ds)
catS sz y = y
catS (sl x) y = sl (catS x y)
catS (sr x) y = sr (catS x y)




{--------------------------------------------------------------}
-- riffling and its inverse

riffle : {X : Set}{ls ms rs : List X} -> ls <[ ms ]> rs ->
         {P : X -> Set} -> All P ls -> All P rs -> All P ms
riffle sz <> <> = <>
riffle (sl x) (p , lp) rp = p , riffle x lp rp
riffle (sr x) lp (p , rp) = p , riffle x lp rp

data IsRiffle {X : Set}{ls ms rs : List X}
              (i : ls <[ ms ]> rs){P : X -> Set}
            : All P ms -> Set where
  mkRiffle  : (lp : All P ls)(rp : All P rs) ->
              IsRiffle i (riffle i lp rp)
isRiffle : {X : Set}{ls ms rs : List X}(i : ls <[ ms ]> rs)
           {P : X -> Set}(mp : All P ms) -> IsRiffle i mp
isRiffle sz <> = mkRiffle <> <>
isRiffle (sl i) (p , mp) with isRiffle i mp
isRiffle (sl i) (p , .(riffle i lp rp))
  | mkRiffle lp rp = mkRiffle (p , lp) rp
isRiffle (sr i) (p , mp) with isRiffle i mp
isRiffle (sr i) (p , .(riffle i lp rp))
  | mkRiffle lp rp = mkRiffle lp (p , rp)



{--------------------------------------------------------------}
-- concatenating All tuples

cat : forall {X}{P : X -> Set}(xs ys : List X) ->
      All P xs -> All P ys -> All P (xs +L ys)
cat xs ys ps qs = riffle (slrs xs ys) ps qs




















{--------------------------------------------------------------}
-- Permutations

data _~_ {X : Set} : List X -> List X -> Set where
  []   : [] ~ []
  _,-_ : forall {x xs ys xys}
                          ->   x ,- [] <[ xys ]> ys
                          ->   xs ~ ys
                          ->   x ,- xs ~ xys

infixr 3 _~_

reflP : {X : Set}(xs : List X) -> xs ~ xs
reflP [] = []
reflP (x ,- xs) = sl (srs xs) ,- reflP xs

permute : {X : Set}{xs ys : List X} -> xs ~ ys ->
          {P : X -> Set} -> All P xs -> All P ys
permute []        <> = <>
permute (i ,- is) (p , ps) = riffle i (p , <>) (permute is ps)

permap : forall {X Y}(f : X -> Y){xs xs' : List X} ->
         xs ~ xs' -> list f xs ~ list f xs'
permap f [] = []
permap f (x ,- p) = splimap f x ,- permap f p







data SRS {X : Set}(ms : List X) : (xs : List X) -> [] <[ ms ]> xs -> Set where
  mkSRS : SRS ms ms (srs ms)

isSRS : {X : Set}{ms xs : List X}(i : [] <[ ms ]> xs) -> SRS ms xs i
isSRS sz = mkSRS
isSRS (sr i) with isSRS i
isSRS (sr .(srs _)) | mkSRS = mkSRS

insP : forall {X : Set}{x : X}{xs xs' ys ys'} -> (x ,- []) <[ xs' ]> xs -> (x ,- []) <[ ys' ]> ys
         -> xs ~ ys -> xs' ~ ys'
insP (sl i) j p with isSRS i
insP (sl .(srs _)) j p | mkSRS = j ,- p
insP (sr i) j (k ,- p) =
  let  _ , k' , j' = llswap (_ , j , k)
  in   k' ,- insP i j' p

l2r : forall {X : Set}{x : X}{xs xs' ys'}(i : (x ,- []) <[ xs' ]> xs)(p' : xs' ~ ys') ->
  Sg (List X) \ ys -> Sg ((x ,- []) <[ ys' ]> ys) \ j -> xs ~ ys
l2r (sl i) (j ,- p) with isSRS i
l2r (sl .(srs _)) (j ,- p) | mkSRS = _ , j , p
l2r (sr i) (k' ,- p') with l2r i p'
... | _ , j' , p with llswap (_ , k' , j')
... | _ , j , k = _ , j , (k ,- p)

transP : {X : Set}{xs ys zs : List X} -> xs ~ ys -> ys ~ zs -> xs ~ zs
transP [] [] = []
transP (i ,- p) q' with l2r i q'
... | _ , j , q = j ,- transP p q

symP : {X : Set}{xs ys : List X} -> xs ~ ys -> ys ~ xs
symP [] = []
symP (i ,- p) = insP i (sl (srs _)) (symP p)

swapP : {X : Set}(xs ys : List X) -> (xs +L ys) ~ (ys +L xs)
swapP [] ys rewrite ys +L[] = reflP ys
swapP (x ,- xs) ys = insS ys x xs ,- swapP xs ys

catP : forall {X : Set}{as bs cs ds : List X} -> as ~ cs -> bs ~ ds -> (as +L bs) ~ (cs +L ds)
catP [] q = q
catP (x ,- p) q = catS x (srs _) ,- catP p q

cartNil : forall {I}(is : List I){J} -> cart {J = J} is [] == []
cartNil [] = refl []
cartNil (i ,- is) = cartNil is

cartCons : forall {I J}(is : List I)(j : J)(js : List J) ->
  cart is (j ,- js) ~ (list (_, j) is +L cart is js)
cartCons [] j js = []
cartCons (i ,- is) j js with catP (swapP (list (i ,_) js) (list (_, j) is)) (reflP (cart is js))
... | z rewrite assoc+L (list (i ,_) js) (list (_, j) is) (cart is js)
              | assoc+L (list (_, j) is) (list (i ,_) js) (cart is js)
  =
  (sl (srs (list (_, j) is +L cart (i ,- is) js))) ,-
  transP (catP (reflP (list (i ,_) js)) (cartCons is j js))
    z

cartLemma : forall {I J}(is : List I)(js : List J) ->
  cart is js ~ list swap (cart js is)
cartLemma {I}{J} [] js rewrite cartNil js {I} = []
cartLemma {I}{J} (i ,- is) js with catP (reflP (list (i ,_) js)) (cartLemma is js)
... | z rewrite sym (listlist swap (_, i) (i ,_) (\ j ->  refl (i , j)) js)
              | catNatural swap (list (_, i) js) (cart js is)
  = transP
  z
  (symP (permap (\ ji -> snd ji , fst ji) (cartCons js i is)))










{--------------------------------------------------------------}
module RECUTTER {I}(C : I |> I) where

  open _|>_

  Subs : List I -> Set
  Subs = All (\ i -> One + Cuts C i)
  subCollect : (is : List I) -> Subs is -> List I
  subCollect is cs =
    collect is (all (\ i -> kk (i ,- []) <+> inners C) is cs)

  Sub : I |> Sg I (Cuts C)
  Cuts   Sub (i , c) = Subs (inners C c)
  inners Sub {i , c} cs = subCollect (inners C c) cs

  Recutter : Set
  Recutter = (i : I)
             (c c' : Cuts C i) ->
             Sg (Cuts Sub (i , c)) \ d ->
             Sg (Cuts Sub (i , c')) \ d' ->
             inners Sub d ~ inners Sub d'








{--------------------------------------------------------------}
module NATRECUT where

  open RECUTTER NatCut

  data CutCompare (x x' y y' n : Nat) : Set where

    -- if we knew x +N x' == n == y +N y', what gives?

    cutLt : (d : Nat) ->
            (x +N suc d) == y -> (suc d +N y') == x' ->
            CutCompare x x' y y' n
            
    cutEq : x == y -> x' == y' ->
            CutCompare x x' y y' n
            
    cutGt : (d : Nat) ->
            (y +N suc d) == x -> (suc d +N x') == y' ->
            CutCompare x x' y y' n














{--------------------------------------------------------------}
-- fancy subtraction

  cutCompare : (x x' y y' n : Nat) ->
               (x +N x') == n -> (y +N y') == n ->
               CutCompare x x' y y' n
  cutCompare zero .n zero .n n (refl _) (refl _)
    = cutEq (refl _) (refl _)
  cutCompare zero ._ (suc y) y' ._ (refl _) (refl _)
    = cutLt y (refl _) (refl _)
  cutCompare (suc x) x' zero ._ ._ (refl _) (refl _)
    = cutGt x (refl _) (refl _)
  cutCompare (suc x) x' (suc y) y' zero () ()
  cutCompare (suc x) x' (suc y) y' (suc n) xq yq
    with cutCompare x x' y y' n (sucInj xq) (sucInj yq) 
  cutCompare (suc x) x' (suc .(x +N suc d)) y' (suc n) xq yq
    | cutLt d (refl _) bq = cutLt d (refl _) bq
  cutCompare (suc x) x' (suc .x) y' (suc n) xq yq
    | cutEq (refl _) bq = cutEq (refl _) bq
  cutCompare (suc .(y +N suc d)) x' (suc y) y' (suc n) xq yq
    | cutGt d (refl _) bq = cutGt d (refl _) bq





{--------------------------------------------------------------}
-- recutting numbers

  NatRecut : Recutter
  NatRecut n (a , b , qab) (c , d , qcd)
    with cutCompare a b c d n qab qcd
  NatRecut n (a , b , qab) (c , d , qcd)
    | cutLt e q0 q1
    = (inl <> , inr (suc e , d , q1) , <>)
    , (inr (a , suc e , q0) , inl <> , <>)
    , reflP _
  NatRecut n (a , b , qab) (.a , .b , qcd)
    | cutEq (refl .a) (refl .b)
    = (inl <> , inl <> , <>)
    , (inl <> , inl <> , <>)
    , reflP _
  NatRecut n (a , b , qab) (c , d , qcd)
    | cutGt e q0 q1
    = (inr (c , suc e , q0) , inl <> , <>)
    , (inl <> , inr (suc e , b , q1) , <>)
    , reflP _






{--------------------------------------------------------------}
-- masking

module MASK {I}(C : I |> I) where

  open _|>_
  open INTERIOR C ;  open CUTKIT C ;  open RECUTTER C

  module CHOP {P}(pc : CutKit P)(rec : Recutter) where

    mask : forall {O Q}
           -> [ O -:> Interior P -:> Interior Q ]
           -> [ Interior O -:> Interior P -:> Interior Q ]
    mask {O}{Q} f = ifold f alg where
      alg  :  [ Cutting C (Interior P -:> Interior Q)
                -:> Interior P -:> Interior Q ]
      glue : (is : List I) -> (d : Subs is)
             -> All (Interior P) (subCollect is d)
             -> All (Interior P) is
      chop : (i : I)(c c' : Cuts C i)
             -> All (Interior P) (inners C c)
             -> All (Interior P) (inners C c')
      chops : (is : List I)
              -> All (Interior P) is -> (d : Subs is)
              -> All (Interior P) (subCollect is d)




{--------------------------------------------------------------}
-- the algebra of the fold

      alg i (c' 8>< fs) (tile p) with pc i c' p
      ... | ps =
           < c' 8><
             allAp (inners C c') fs (all (\ _ -> tile) _ ps) >
      alg i (c' 8>< fs) < c 8>< ps > =
           < c' 8><
             allAp (inners C c') fs (chop i c c' ps) >














{--------------------------------------------------------------}
-- unedifying details

      glue [] <> <> = <>
      glue (i ,- is) (inl <> , ds) (p , ps) = p , glue is ds ps
      glue (i ,- is) (inr c , ds) ps with isRiffle (slrs (inners C c) (subCollect is ds)) ps
      glue (i ,- is) (inr c , ds) .(riffle (slrs (inners C c) (subCollect is ds)) lp rp)
        | mkRiffle lp rp = < c 8>< lp > , glue is ds rp

      chop i c c' ps with rec i c c'
      ... | d , d' , m with chops (inners C c) ps d
      ... | qs = glue (inners C c') d' (permute m qs)
      chops [] <> <> = <>
      chops (i ,- is) (p , ps) (inl <> , ds) = p , chops is ps ds
      chops (i ,- is) (tile p , ps) (inr c' , ds) =
        cat (inners C c') (subCollect is ds) (all (\ _ -> tile) _ (pc i c' p)) (chops is ps ds)
      chops (i ,- is) (< c 8>< ps' > , ps) (inr c' , ds) =
        cat (inners C c') (subCollect is ds) (chop i c c' ps') (chops is ps ds)

    




module SUBCOLLECTLEMMA where

  open _|>_
  open RECUTTER

  subCollectLemma : forall {I J}(C : I |> I)(D : J |> J)
                    (f : I -> J)(g : (i : I) -> Cuts C i -> Cuts D (f i)) ->
                    (q : (i : I)(c : Cuts C i) -> inners D (g i c) == list f (inners C c)) ->
                    (is : List I)(ps : All (\ i -> One + Cuts C i) is) ->
                    subCollect D (list f is) (allRe f is (all (\ i -> id +map g i) is ps)) ==
                    list f (subCollect C is ps)
  subCollectLemma C D f g q [] <> = refl []
  subCollectLemma C D f g q (i ,- is) (inl <> , ps) =
    refl (f i ,-_) =$= subCollectLemma C D f g q is ps
  subCollectLemma C D f g q (i ,- is) (inr c , ps) = 
    (inners D (g i c) +L
     subCollect D (list f is) (allRe f is (allAp is (allPu (\ i -> id +map g i) is) ps)))
      =[ refl _+L_ =$= q i c =$= subCollectLemma C D f g q is ps >=
    (list f (inners C c) +L list f (subCollect C is ps))
      =[ catNatural f (inners C c) (subCollect C is ps) >=
    list f (inners C c +L subCollect C is ps)
      [QED]


{--------------------------------------------------------------}
-- Recutting in multiple dimensions

module SUMRECUT  {I J}(C : I |> I)(D : J |> J) where
 open _|>_ ; open RECUTTER ; open SUBCOLLECTLEMMA
 module SUMRECUT' (rec : Recutter C)(red : Recutter D) where

  SumRecut : Recutter (C |+| D)



















  cartLeftLemma : (is : List I)(j : J)(d : Cuts D j) -> subCollect (C |+| D) (list (_, j) is)
                (allRe (_, j) is
                   (allPu (\ _ -> inr (inr d)) is)) == cart is (inners D d)
  cartLeftLemma [] j d = refl []
  cartLeftLemma (i ,- is) j d = refl (list (i ,_) (inners D d) +L_) =$= cartLeftLemma is j d

  cartRightLemma : (i : I)(c : Cuts C i)(js : List J) ->
     subCollect (C |+| D) (list (i ,_) js)
                 (allRe (i ,_) js (allPu (\ _ -> inr (inl c)) js)) ==
                 list swap (cart js (inners C c))
  cartRightLemma i c [] = refl []
  cartRightLemma i c (j ,- js)
    rewrite sym (catNatural swap (list (j ,_) (inners C c)) (cart js (inners C c)))
                | listlist swap (j ,_) (_, j) (\ i -> refl (i , j)) (inners C c)
                = refl (list (_, j) (inners C c) +L_) =$= cartRightLemma i c js



  -- both cuts in left dimension
  SumRecut (i , j) (inl c) (inl c') with rec i c c'
  ... | x , y , m
      = allRe (_, j) (inners C c) (all (\ _ -> id +map inl) _ x)
      , allRe (_, j) (inners C c') (all (\ _ -> id +map inl) _ y)
      , lemma where
        lemma : subCollect (C |+| D) (list (_, j) (inners C c))
                 (allRe (_, j) (inners C c) (all (\ _ -> id +map inl) (inners C c) x))
                ~
                subCollect (C |+| D) (list (_, j) (inners C c'))
                 (allRe (_, j) (inners C c') (all (\ _ -> id +map inl) (inners C c') y))
        lemma rewrite subCollectLemma C (C |+| D) (_, j) (\ _ -> inl) (\ i c -> refl _)
                        (inners C c) x
                    | subCollectLemma C (C |+| D) (_, j) (\ _ -> inl) (\ i c -> refl _)
                        (inners C c') y
          = permap (_, j) m

  -- left to right
  fst (SumRecut (i , j) (inl c) (inr d)) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  fst (snd (SumRecut (i , j) (inl c) (inr d))) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  snd (snd (SumRecut (i , j) (inl c) (inr d)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = cartLemma (inners C c) (inners D d)

  -- right to left
  fst (SumRecut (i , j) (inr d) (inl c)) =
    allRe (i ,_) (inners D d) (allPu (\ i -> inr (inl c)) (inners D d))
  fst (snd (SumRecut (i , j) (inr d) (inl c))) =
    allRe (_, j) (inners C c) (allPu (\ i -> inr (inr d)) (inners C c))
  snd (snd (SumRecut (i , j) (inr d) (inl c)))
    rewrite cartLeftLemma (inners C c) j d
          | cartRightLemma i c (inners D d)
          = symP (cartLemma (inners C c) (inners D d))

  -- both cuts in right dimension
  SumRecut (i , j) (inr d) (inr d') with red j d d'
  ... | x , y , m
    = allRe (i ,_) (inners D d) (all (\ _ -> id +map inr) _ x)
    , allRe (i ,_) (inners D d') (all (\ _ -> id +map inr) _ y)
    , lemma where
        lemma : subCollect (C |+| D) (list (i ,_) (inners D d))
                 (allRe (i ,_) (inners D d) (all (\ _ -> id +map inr) (inners D d) x))
                ~
                subCollect (C |+| D) (list (i ,_) (inners D d'))
                 (allRe (i ,_) (inners D d') (all (\ _ -> id +map inr) (inners D d') y))
        lemma rewrite subCollectLemma D (C |+| D) (i ,_) (\ _ -> inr) (\ i d -> refl _)
                        (inners D d) x
                    | subCollectLemma D (C |+| D) (i ,_) (\ _ -> inr) (\ i d -> refl _)
                        (inners D d') y
                    = permap (i ,_) m


{--------------------------------------------------------------}
-- Cutting up rectangles

module RECTANGLE where

  open NATRECUT
  open SUMRECUT NatCut NatCut; open SUMRECUT' NatRecut NatRecut

  RectRecut = SumRecut






















{--------------------------------------------------------------}
-- Vectors, at last!

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

_+V_ : forall {X n m} -> Vec X n -> Vec X m -> Vec X (n +N m)
[]        +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

record Applicative (F : Set -> Set) : Set1 where
  field
    pure : {X : Set} -> X -> F X
    _<*>_ : {S T : Set} -> F (S -> T) -> F S -> F T
  infixl 2 _<*>_

VecAppl : (n : Nat) -> Applicative \ X -> Vec X n
Applicative.pure (VecAppl zero)    x = []
Applicative.pure (VecAppl (suc n)) x =
  x ,- Applicative.pure (VecAppl n) x
Applicative._<*>_ (VecAppl .zero)    []        []        = []
Applicative._<*>_ (VecAppl .(suc _)) (f ,- fs) (s ,- ss) =
  f s ,- Applicative._<*>_ (VecAppl _) fs ss


{--------------------------------------------------------------}
-- traversability
module VTRAVERSE {F}(A : Applicative F) where

  open Applicative A

  vtraverse : forall {n S T} -> (S -> F T) -> Vec S n -> F (Vec T n)
  vtraverse f []        = pure []
  vtraverse f (s ,- ss) = pure _,-_ <*> f s <*> vtraverse f ss

Matrix : Set -> Nat * Nat -> Set
Matrix X (i , j) = Vec (Vec X i) j

xpose : forall {X ij} -> Matrix X ij -> Matrix X (swap ij)
xpose = vtraverse id where
  open VTRAVERSE (VecAppl _)










{--------------------------------------------------------------}
-- lifting an algebra

module VECALL {I : Set}{P : I -> Set}{n : Nat}where

  open Applicative (VecAppl n)
  
  vecAll : {is : List I} ->
         All (\ i -> Vec (P i) n) is -> Vec (All P is) n
  vecAll {[]} pss = pure <>
  vecAll {i ,- is} (ps , pss) = pure _,_ <*> ps <*> vecAll pss

  VecLiftAlg : (C : I |> I) ->
             Algebra (Cutting C) P ->
             Algebra (Cutting C) (\ i -> Vec (P i) n)
  VecLiftAlg C alg i (c 8>< pss) = pure (alg i << (c 8><_)) <*> vecAll pss

open VECALL










{--------------------------------------------------------------}
-- a matrix algebra for rectangular cuts

NatCutVecAlg : {X : Set} -> Algebra (Cutting NatCut) (Vec X)
NatCutVecAlg .(m +N n) (m , n , refl .(m +N n) 8>< xm , xn , <>)
  = xm +V xn

open RECTANGLE

NatCut2DMatAlg : {X : Set} ->
                 Algebra (Cutting RectCut) (Matrix X)
NatCut2DMatAlg _ (inl c 8>< ms)
  = VecLiftAlg NatCut NatCutVecAlg _ (c 8>< ms) 
NatCut2DMatAlg _ (inr c 8>< ms)
  = NatCutVecAlg _ (c 8>< ms)
















{--------------------------------------------------------------}
-- interior example

open RECTANGLE
open INTERIOR RectCut

rot : {P : Nat * Nat -> Set}{w h : Nat} ->
  ({w h : Nat} -> P (w , h) -> P (h , w)) ->
  Interior P (w , h) -> Interior P (h , w)
rot pc90 (tile p) = tile (pc90 p)
rot pc90 < inl (l , r , refl _) 8>< (il , ir , <>) >
  = < inr (l , r , refl _) 8><
      rot pc90 il , rot pc90 ir , <> >
rot pc90 < inr (t , b , refl _) 8>< it , ib , <> >
  = < (inl (b , t , comm-+N b t)) 8><
      rot pc90 ib , rot pc90 it , <> >











{--------------------------------------------------------------}
-- golden rectangles

Square : Nat * Nat -> Set
Square (w , h) = w == h

c90Sq : {w h : Nat} -> Square (w , h) -> Square (h , w)
c90Sq (refl _) = refl _

golden : (n : Nat) ->
         Sg Nat \ w -> Sg Nat \ h -> Interior Square (w , h)
golden zero = 1 , 1 , tile (refl 1)
golden (suc n) with golden n
... | w , h , i = (w +N h) , w , < (inl (w , h , refl _)) 8><
                  tile (refl w) , rot c90Sq i , <> >












{--------------------------------------------------------------}
-- making ascii rectangles

fill : {n : Nat}{X : Set} -> X -> X -> X -> Vec X (suc (suc n))
fill {n} first midst last rewrite comm-+N 1 (suc n) =
  first ,- (pure midst +V (last ,- []))
  where open Applicative (VecAppl n)

border : {w h : Nat} -> Matrix Char (w , h)
border {w} {zero} = []
border {zero} {h} = pure [] where open Applicative (VecAppl _)
border {suc zero} {suc zero} = ('O' ,- []) ,- []
border {suc (suc w)} {suc zero} = fill '<' '-' '>' ,- []
border {suc zero} {suc (suc h)} =
  fill ('^' ,- []) ('|' ,- []) ('v' ,- [])
border {suc (suc w)} {suc (suc h)} =
  fill (fill ',' '-' '.')
       (fill '|' ' ' '|')
       (fill '`' '-' '\'')








{--------------------------------------------------------------}
-- displaying golden rectangles

goldenInterior :  (n : Nat) -> Sg Nat \ w -> Sg Nat \ h ->
                  Interior (Matrix Char) (w , h)
goldenInterior n with golden n
... | w , h , sqi
    = w , h ,
      extend (\ _ _ -> tile border) (w , h) sqi

picture : [ Interior (Matrix Char) -:> Matrix Char ]
picture = ifold (\ _ -> id) NatCut2DMatAlg

goldenPicture : (n : Nat) -> Sg Nat \ w -> Sg Nat \ h ->
                Matrix Char (w , h)
goldenPicture n with goldenInterior n
... | w , h , mi = w , h , picture _ mi










{--------------------------------------------------------------}
-- stringing you along

v2l : forall {n X} -> Vec X n -> List X
v2l [] = []
v2l (x ,- xs) = x ,- v2l xs

vcs : forall {n} -> Vec Char n -> String
vcs = primStringFromList << v2l

seeGold : (n : Nat) -> List String
seeGold n =
  let w , h , m = goldenPicture n
      open Applicative (VecAppl h)
  in  v2l (pure vcs <*> m)

-- now reverse search Hancock
