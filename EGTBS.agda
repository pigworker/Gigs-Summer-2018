module EGTBS where

{---------------------------------------------------------------

      SEAGOON:      What are you doing down here?

                  ,----------------------------------,
                  |                                  |
      ECCLES:     | Everybody's got to be somewhere. |
                  |                                  |
                  '----------------------------------'

      SEAGOON:      Yes, but who are you?*

      ECCLES:       Oooh, da hard ones first, eh?

      --  Spike Milligan, in "The Last Goon Show Of All"




  * Conor McBride
    Mathematically Structured Programming
    University of Strathclyde








----------------------------------------------------------------}

{--------------------------------------------------------------

       thinnings which do not cover the scope
   left-support -----> scope <----- right-support

        O---------------O
        |              O:               
      O---------------O---------------O
     O---------------O: :             |
     || |           O---------------O |
     || |           ::: :           | |
  id || |           ::: :           | | id
     || O...........:::.O           | |
     ||             :::             | |
     |O.............::O.............|.O
     O..............:O              |
                    O...............O

  left-support --> support <---- right-support
        thinnings which cover the support
                







----------------------------------------------------------------}

{--------------------------------------------------------------




          thinning  partition  gninniht

        O---------------O
                       O---------------O
                      O---------------O:
     O---------------O||              ::
     :              O---------------O ::
     :               |||              ::
     :               |||              ::
     :               |||              ::
     :               ||O..............:O
     :               |O...............O
     O...............O
                     
              refined partition










----------------------------------------------------------------}
{--------------------------------------------------------------


   1. basic equipment
                                                             (notation fixing)

   2. de Bruijn syntax
                                                 (thinning-nearest-the-leaves)

   3. things with thinning from support to scope
                                                   (quickly thinned some more)

   4. constructing relevant pairs
                                             (everybody's got to be somewhere)

   5. concatenating scopes and binding variables
                                                    (by chopping up thinnings)

   6. a universe of co-de-Bruijn metasyntaxes
                                                   (thinning-nearest-the-root)

   7. simultaneous hereditary substitution
                                             (structurally recursive, at last)




















--------------------------------------------------------------}


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









{---------------------------------------------------------------}
-- Basics

data    Zero : Set where
record  One  : Set where constructor <>
data    Two  : Set where ff tt : Two

Tt : Two -> Set
Tt ff = Zero
Tt tt = One

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}














{---------------------------------------------------------------}
-- dependent pairs (Sigma types)

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

pattern !_ t = _ , t

infixr 4 _,_ !_ _*_












{---------------------------------------------------------------}
-- boo, hiss

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
infixr 5 _==_





















{---------------------------------------------------------------}
-- backward lists and their thinnings

data Bwd (K : Set) : Set where  -- K will later be "Kind"
  []    : Bwd K
  _-,_  : Bwd K -> K -> Bwd K

infixl 6 _-,_

data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o' : forall {iz jz k} ->  iz <= jz  ->  iz      <= jz -, k
  _os : forall {iz jz k} ->  iz <= jz  ->  iz -, k <= jz -, k
  oz :                                       []   <=    []
infixl 5 _<=_ _o' _os

myExample : [] -, 5 -, 3 -, 1  <=  [] -, 5 -, 4 -, 3 -, 2 -, 1
myExample = oz os o' os o' os











{---------------------------------------------------------------}
-- identity and composition of thinnings

oi : forall {K}{kz : Bwd K} -> kz <= kz
oi {_} {[]}     = oz
oi {_} {_ -, _} = oi os

_-_ : forall {K}{iz jz kz : Bwd K} ->
      iz <= jz -> jz <= kz -> iz <= kz
th    - ph o'  = (th - ph) o'      -- if either side discards,
th o' - ph os  = (th - ph) o'      --   then discard
th os - ph os  = (th - ph) os      -- if both keep, then keep
oz    - oz     = oz

infixl 4 _-_

-- initial object

oe : forall {K}{kz : Bwd K} -> [] <= kz
oe {_} {[]}     = oz
oe {_} {_ -, _} = oe o'










{---------------------------------------------------------------}
-- this indexed life

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i
infixr 4 _-:>_

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall {i} -> P i

Cx : Set -> Set1
Cx K = Bwd K -> Set





















{---------------------------------------------------------------}
-- de Bruijn indexing

_<-_ : forall {K} -> K -> Cx K
k <- kz = [] -, k <= kz

data Lam : Cx One where
  var : [          (<> <-_) -:> Lam ]
  _$_ : [       Lam -:> Lam -:> Lam ]
  lam : [ ((_-, <>) >> Lam) -:> Lam ]

ren : forall {n m} -> Lam n -> n <= m -> Lam m
ren (var x) th = var (x - th)                    -- action at leaves
ren (f $ s) th = ren f th $ ren s th
ren (lam t) th = lam (ren t (th os))             -- os is snoc for thinning


















{---------------------------------------------------------------}
-- Things with Thinnings

record _/_ {K}(R : Cx K)(scope : Bwd K) : Set where
  constructor _^_
  field
    {support}  : Bwd K
    thing      : R support        -- plan: R enforces relevance
    thinning   : support <= scope
open _/_
infixl 3 _^_ _/_

map/ : forall {K}{R S : Cx K} ->
       [ R -:> S ] -> [ (R /_) -:> (S /_) ]
map/ f (r ^ th) = f r ^ th

unit/ : forall {K}{R : Cx K} ->      [ R -:> (R /_) ]
unit/ r = r ^ oi

mult/ : forall {K}{R : Cx K} ->      [ ((R /_) /_) -:> (R /_) ]
mult/ (r ^ th ^ ph) = r ^ th - ph

-- what is a relevant pair?





{---------------------------------------------------------------}
-- Coverings and Partitions

data Cover {K} :  forall {iz jz ijz : Bwd K}
                  (th : iz <= ijz)(ph : jz <= ijz) -> Set where
                  
  _cs' : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
         Cover th ph -> Cover {ijz = _ -, k} (th os) (ph o')

  _c's : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
         Cover th ph -> Cover {ijz = _ -, k} (th o') (ph os)

  _css : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
         Cover th ph -> Cover {ijz = _ -, k} (th os) (ph os)

  czz  :                Cover                    oz      oz
infixl 5 _c's _cs' _css

data Parti {K} :  forall {iz jz ijz : Bwd K}
                  (th : iz <= ijz)(ph : jz <= ijz) -> Set where
  _ps' : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
         Parti th ph -> Parti {ijz = _ -, k} (th os) (ph o')
  _p's : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
         Parti th ph -> Parti {ijz = _ -, k} (th o') (ph os)
  pzz  :                Parti                    oz      oz
infixl 5 _p's _ps'






{---------------------------------------------------------------}
-- Relevant Pairing

record _><_ {K}(L R : Cx K)(kz : Bwd K) : Set where
  constructor pair
  field
    outl  : L / kz
    outr  : R / kz
    cover : Cover (thinning outl) (thinning outr)
open _><_
infixr 4 _><_

-- but how to construct?

{-
   iz ------,    th
     `       ------,
  th' `             ------,
      /`v                  ------v
     |   ijz .....ps...........> kz
      \,^                  ------^
  ph' ,             ------'
     ,       ------'
   jz ------'    ph
-}







{---------------------------------------------------------------}
-- Replace Composition By Its Graph

data Tri {K} : forall {iz jz kz : Bwd K}
               (th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz)
            -> Set where
  _t-'' : forall {iz jz kz k}
                 {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
                 Tri th ph ps -> Tri {kz = _ -, k} th (ph o') (ps o')
  _t's' : forall {iz jz kz k}
                 {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
                 Tri th ph ps -> Tri {kz = _ -, k} (th o') (ph os) (ps o')
  _tsss : forall {iz jz kz k}
                 {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
                 Tri th ph ps -> Tri {kz = _ -, k} (th os) (ph os) (ps os)
  tzzz  :        Tri oz oz oz

infixr 5 _t-'' _t's' _tsss












{---------------------------------------------------------------}
-- in and out of the graph representation

tri : forall {K} {iz jz kz : Bwd K} (th : iz <= jz)(ph : jz <= kz) ->
      Tri th ph (th - ph)
tri th (ph o') = tri th ph t-''
tri (th o') (ph os) = tri th ph t's'
tri (th os) (ph os) = tri th ph tsss
tri oz oz = tzzz

isTri : forall {K} {iz jz kz : Bwd K}
        {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
        Tri th ph ps -> ps == (th - ph)
isTri (t t-'') rewrite isTri t = refl
isTri (t t's') rewrite isTri t = refl
isTri (t tsss) rewrite isTri t = refl
isTri tzzz = refl











{---------------------------------------------------------------}
-- constructing the coproduct in the slice category

cop : forall {K}{kz : Bwd K}       -- which slice?
             {iz}(th : iz <= kz)   -- left  object in the slice
             {jz}(ph : jz <= kz)   -- right object in the slice
      ->
      Sg (Bwd K) \ ijz -> Sg (ijz <= kz) \ ps ->  -- coproduct
      Sg (iz <= ijz) \ th' ->                 Sg (jz <= ijz) \ ph' ->
         Tri th' ps th      * Cover th' ph'    * Tri ph' ps ph
    -- left injection                        -- right injection
      
cop (th o') (ph o') = let ! ! ! ! lt      , c     , rt       = cop th ph
                      in  ! ! ! ! lt t-'' , c     , rt t-''
cop (th o') (ph os) = let ! ! ! ! lt      , c     , rt       = cop th ph
                      in  ! ! ! ! lt t's' , c c's , rt tsss
cop (th os) (ph o') = let ! ! ! ! lt      , c     , rt       = cop th ph
                      in  ! ! ! ! lt tsss , c cs' , rt t's'
cop (th os) (ph os) = let ! ! ! ! lt      , c     , rt       = cop th ph
                      in  ! ! ! ! lt tsss , c css , rt tsss
cop     oz      oz  =     ! ! ! !    tzzz ,   czz ,    tzzz









{---------------------------------------------------------------}
-- relevant pairing

_,R_ : forall {K}{L R : Cx K} ->
       [ (L /_) -:> (R /_) -:> (L >< R /_) ]
(l ^ th) ,R (r ^ ph) =
  let ! ps , th' , ph' , _ , c , _ = cop th ph
  in  pair (l ^ th') (r ^ ph') c ^ ps
infixr 4 _,R_

outlR : forall {K}{L R : Cx K} ->
        [ (L >< R /_) -:> (L /_) ]
outlR (pair l _ _ ^ ps) = mult/ (l ^ ps)

outrR : forall {K}{L R : Cx K} ->
        [ (L >< R /_) -:> (R /_) ]
outrR (pair _ r _ ^ ps) = mult/ (r ^ ps)












{---------------------------------------------------------------}
-- refining partitions

refine : forall {K}{iz' jz' ijz' ijz : Bwd K}
         {th' : iz' <= ijz'}{ph' : jz' <= ijz'} ->
         ijz <= ijz' -> Parti th' ph' ->
         Sg _ \ iz -> Sg _ \ jz ->
         Sg (iz <= ijz) \ th   -> Sg (jz <= ijz) \ ph ->
         iz <= iz'  *  Parti th ph  *  jz <= jz'
refine (ps o') (p' p's) =
  let ! ! ! ! ps0 , p , ps1    = refine ps p'
  in  ! ! ! ! ps0 , p , ps1 o'
refine (ps o') (p' ps') =
  let ! ! ! ! ps0    , p , ps1 = refine ps p'
  in  ! ! ! ! ps0 o' , p , ps1
refine (ps os) (p' p's) =
  let ! ! ! ! ps0 , p     , ps1    = refine ps p'
  in  ! ! ! ! ps0 , p p's , ps1 os
refine (ps os) (p' ps') =
  let ! ! ! ! ps0    , p     , ps1 = refine ps p'
  in  ! ! ! ! ps0 os , p ps' , ps1
refine oz pzz = ! ! ! ! oz , pzz , oz








{---------------------------------------------------------------}
-- skip me for now

leftyLemma : forall {K}{iz ijz : Bwd K}
             {th : iz <= ijz}{ph : [] <= ijz} ->
             Parti th ph ->
             Sg (iz == ijz) \ { refl -> th == oi * ph == oe }
leftyLemma (p ps') with leftyLemma p
... | refl , refl , refl  = refl , refl , refl
leftyLemma pzz            = refl , refl , refl




















{---------------------------------------------------------------}
-- concatenating and splitting thinnings

_++_ : forall {K} -> Bwd K -> Bwd K -> Bwd K
iz ++     []     = iz
iz ++ (jz -, j)  = iz ++ jz -, j
infixl 6 _++_

_<++=_ : forall {K}{iz iz' jz jz' : Bwd K} ->
         iz <= jz   ->   iz' <= jz'   ->
         iz ++ iz'  <=  jz ++ jz'
th <++= (ph o') = (th <++= ph) o'
th <++= (ph os) = (th <++= ph) os
th <++=     oz  = th

gloloc : forall {K}{kz jz : Bwd K} jz' -> kz <= jz ++ jz' ->
         Sg _ \ iz -> Sg _ \ iz' ->
         kz == (iz ++ iz') * iz <= jz * iz' <= jz'
gloloc []         ps     = ! ! refl , ps , oi
gloloc (jz' -, j) (ps o') with gloloc jz' ps
... | ! ! refl , th , ph = ! ! refl , th , ph o'
gloloc (jz' -, j) (ps os) with gloloc jz' ps
... | ! ! refl , th , ph = ! ! refl , th , ph os













{---------------------------------------------------------------}
-- my favourite Parti

leftRight : forall {K}(iz jz : Bwd K) ->
            Sg (iz <= iz ++ jz) \ th ->
            Sg (jz <= iz ++ jz) \ ph ->
            Parti th ph
leftRight iz (jz -, j) = let ! ! p = leftRight iz jz in ! ! p p's
leftRight (iz -, i) [] = let ! ! p = leftRight iz [] in ! ! p ps'
leftRight []        [] = oz , oz , pzz





















{---------------------------------------------------------------}
-- Binding a bunch of variables

_|-_ : forall {K} -> Bwd K -> Cx K -> Cx K
(jz |- P) iz = P (iz ++ jz)

record _|-R_ {K}(jz : Bwd K)(R : Cx K)(iz : Bwd K) : Set where
  constructor _\\_
  field
    {relevant}  : Bwd K
    binder      : relevant <= jz
    body        : (relevant |- R) iz
open _|-R_
infixr 4 _|-R_
infixl 5 _\\_

_\\R_ : forall {K}{R : Cx K} jz -> [ (jz |- (R /_)) -:> ((jz |-R R) /_) ]
  
jz \\R (r ^ ps) with gloloc jz ps
... | ! ! refl , th , ph = (ph \\ r) ^ th











{---------------------------------------------------------------}
-- Base cases and Tagging

data OneR {K} : Cx K where
  <> : OneR []

<>R : forall {K}{kz : Bwd K} -> OneR / kz   -- [ (OneR /_) ]
<>R = <> ^ oe

data VarR {K}(k : K) : Cx K where
  only : VarR k ([] -, k)

varR : forall {K}{k : K} -> [ (k <-_) -:> (VarR k /_) ]
varR = (only ^_)

SgR : forall {K}(S : Set)(T : S -> Cx K) -> Cx K
SgR S T kz = Sg S \ s -> T s kz

_`_ : forall {K}{S : Set}{T : S -> Cx K} ->
      (s : S) -> [ (T s /_) -:> (SgR S T /_) ]
s ` (t ^ th) = (s , t) ^ th
infixr 4 _`_









{---------------------------------------------------------------}
-- A Universe of METAsyntaxes

module META (Sort : Set) where

  data Kind : Set where
    _=>_ : Bwd Kind -> Sort -> Kind
  infixr 5 _=>_

  data Desc : Set1 where
    rec' :                     Kind -> Desc
    sg'  : (S : Set)(T : S -> Desc) -> Desc
    _*'_ :     (S : Desc)(T : Desc) -> Desc
    one' :                             Desc
  infixr 4 _*'_














{---------------------------------------------------------------}
-- Interpreting Desc

  Sp : Bwd Kind -> Desc
  Sp []        = one'
  Sp (kz -, k) = Sp kz *' rec' k

  _%_ : Desc -> (Sort -> Cx Kind) -> Cx Kind
  rec' (jz => s) % R   = jz |-R R s
  sg' S T        % R   = SgR S \ s -> (T s % R)
  (S *' T)       % R   = (S % R) >< (T % R)
  one'           % R   = OneR

  module TERM (F : Sort -> Desc) where

    data Tm (s : Sort)(kz : Bwd Kind) : Set where
    
      <_> :                       (F s % Tm) kz -> Tm s kz
      
      vap : forall {jz} ->
            (VarR (jz => s) >< (Sp jz % Tm)) kz -> Tm s kz











{---------------------------------------------------------------}
-- Smart Constructors

    <_>R : forall {s} -> [ ((F s % Tm) /_) -:> (Tm s /_) ]
    < t ^ th >R = < t > ^ th

    vapR : forall {s}{jz kz : Bwd Kind} ->
           (jz => s) <- kz  ->  (Sp jz % Tm) / kz  -> Tm s / kz
    vapR x as = map/ vap (varR x ,R as)






















{---------------------------------------------------------------}
-- Untyped Lambda Calculus

module LAM where
  open META One
  data Tag : Set where app lam : Tag

  b1 : Bwd Kind
  b1 = [] -, ([] => <>)

  LAM : One -> Desc
  LAM <> = sg' Tag \ { app -> rec' ([] => <>) *' rec' ([] => <>)
                     ; lam -> rec' (b1 => <>)
                     }

  open TERM LAM














{---------------------------------------------------------------}
-- K and S combinators

  combK : Tm <> []
  combK = < lam , oi \\
           < lam , oe \\
            vap (pair (only ^ oi) (<> ^ oe) (czz cs')) > >

  combS : Tm <> / []
  combS = < lam ` (b1 \\R
          < lam ` (b1 \\R
          < lam ` (b1 \\R
          < app ` ([] \\R < app ` ([] \\R vapR (oz os o' o') <>R)
                               ,R ([] \\R vapR (oz o' o' os) <>R) >R) ,R
                  ([] \\R < app ` ([] \\R vapR (oz o' os o') <>R)
                               ,R ([] \\R vapR (oz o' o' os) <>R) >R) >R
          ) >R) >R) >R












{---------------------------------------------------------------}
-- Hereditary substitution by structural recursion

module HERED (Sort : Set) where
  open META Sort
  module _ (F : Sort -> Desc) where
    open TERM F

    record HSub (src trg act : Bwd Kind) : Set where
      constructor _<=[_]:=_
      field
        {pass}     : Bwd Kind
        {passive}  : pass <= src
        {active}   : act  <= src
        passTrg    : pass <= trg
        parti      : Parti passive active
        images     : (Sp act % Tm) / trg
    open HSub

    wkHSub : forall {src trg act} ->
             HSub  src         trg        act -> forall jz ->
             HSub (src ++ jz) (trg ++ jz) act
    wkHSub p [] = p
    wkHSub p (jz -, j) with wkHSub p jz
    ... |  ph     <=[ p'     ]:= (is ^ th)
        = (ph os) <=[ p' ps' ]:= (is ^ th o')









{---------------------------------------------------------------}
-- type it!

    hSub  : forall {src trg act supp s}
         -> Tm s supp -> supp <= src       -- term in source
         -> HSub src trg act               -- substitution
         -> Tm s / trg                     -- term in target

    hSubs : forall {src trg act supp}   D  -- node description
         -> (D % Tm) supp -> supp <= src   -- node in source
         -> HSub src trg act               -- substitution
         -> (D % Tm) / trg                 -- node in target

    hered : forall {jz src trg act s}
         -> (jz => s) <- src               -- source var
         -> HSub src trg act               -- substitution
         -> (Sp jz % Tm) / trg             -- target spine
         -> Tm s / trg                     -- term in target


{---------------------------------------------------------------}
-- do it!

    hSub t ps (ph <=[ p ]:= ts) with refine ps p
    hSub t ps (ph <=[ p ]:= ts) | _ , [] , _ , _ , th , p-[] , _
      with leftyLemma p-[]
    ... | refl , refl , refl = t ^ th - ph
    
    hSub (vap {jz} (pair (only ^ x) (ss ^ ph) _)) ps h@_ | _ =
      hered (x - ps) h (hSubs (Sp jz) ss (ph - ps) h)
      
    hSub {s = s} < t > ps h@_ | _ = < hSubs (F s) t ps h >R

    hSubs (rec' (jz => s))  (th \\ t)           ps h =
      jz \\R hSub t (ps <++= th) (wkHSub h jz)
    hSubs (sg' S T)         (s , t)             ps h =
      s ` hSubs (T s) t ps h
    hSubs (S *' T) (pair (s ^ th) (t ^ ph) _ )  ps h =
      hSubs S s (th - ps) h ,R hSubs T t (ph - ps) h
    hSubs one'              _                   ps h =
      <>R









{----------------------------------------------------------------}
-- a-hunting we shall go!

-- miss

    hered {act = act} (x o') (ph <=[ p ps' ]:= is) ss =
      hered {act = act} x ((oi o' - ph) <=[ p ]:= is) ss
    hered {act = (act -, _)} (x o') (ph <=[ p p's ]:= is) ss =
      hered {act = act} x (ph <=[ p ]:= outlR is) ss

-- hit

    hered {act = act} (x os) (ph <=[ p ps' ]:= is) ss =
      vapR (oe os - ph) ss
    hered {act = (_ -, (jz => _))} (x os) (ph <=[ p p's ]:= is) ss
      with outrR is | leftRight _ jz
    ... | (th \\ t) ^ ps | ! ! p'
        = hSub {act = jz} t (ps <++= th) (oi <=[ p' ]:= ss)














{--------------------------------------------------------------

  * it's not for humans

  * I have no idea if it goes any faster

  * it gives you a lot of extra information about usage

  * shifting is now easy

  * fools rush in where angels fear to tread

  * glory to God in the highest (dimension you can get your hands on)























--------------------------------------------------------------}
