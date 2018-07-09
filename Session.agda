module Session where


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

data Two : Set where tt ff : Two

not : Two -> Two
not tt = ff
not ff = tt

Tt : Two -> Set
Tt tt = One
Tt ff = Zero












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
-- Heterogeneous Equality

data _==_ {l}(S : Set l) : Set l -> Set l where
  Refl : S == S

Sym : forall {l}{S T : Set l} -> S == T -> T == S
Sym Refl = Refl

data _=[_]=_ {l}{S : Set l}(s : S)
        : {T : Set l} -> S == T -> T -> Set l
  where
    refl : s =[ Refl ]= s





















sym : forall {l}{S T : Set l}(Q : S == T){s t} -> s =[ Q ]= t -> t =[ Sym Q ]= s
sym Refl refl = refl

Resp : forall {k l}{S : Set k}(F : S -> Set l){x y}
        (q : x =[ Refl ]= y) -> F x == F y
Resp F refl = Refl

{-
resp1 : forall {k l}{A : Set k}{B : Set l}(f : A -> B){x y}(q : x =[ Refl ]= y) -> f x =[ Refl ]= f y
resp1 f refl = refl
-}

resp : forall {k l}{A : Set k}{B : A -> Set l}(f : (a : A) -> B a){x y}(q : x =[ Refl ]= y) -> f x =[ Resp B q ]= f y
resp f refl = refl

pair= : forall (A : Set)(B : A -> Set){a a' : A}(q : a =[ Refl ]= a'){b : B a}{b' : B a'}(q' : b =[ Resp B q ]= b') -> (a , b) =[ Refl {S = Sg A B} ]= (a' , b')
pair= A B refl refl = refl

irr : forall {l}{S : Set l}{s : S}{T : Set l}{t : T}{q q' : S == T} -> s =[ q ]= t -> s =[ q' ]= t
irr {q = Refl}{q' = Refl} st = st

















{--------------------------------------------------------------}
module Session (I : Set)(J : I -> Set) where

  data Desc (b : Two) : Set1
  Approx : {b : Two} -> Desc b -> Set

  data Desc b where
    var : {_ : Tt b} -> (i : I) -> Desc b
    kon : (A : Set) -> Desc b
    sg  : (S : Desc b)(T : Approx S -> Desc b) -> Desc b
    op  : Desc (not b) -> Desc b

  Approx (var i)   = J i
  Approx (kon A)   = A
  Approx (sg S T)  = Sg (Approx S) \ s -> Approx (T s)
  Approx (op T)    = Approx T









{--------------------------------------------------------------}
  module TRAFFIC (F : I -> Desc tt)
                 (f : (i : I) -> Approx (F i) -> J i)
                 where

    data Traffic (i : I) : Set
    decode : {i : I} -> Traffic i -> J i

    Node : {b : Two} -> Desc b -> Set
    approx : {b : Two}(D : Desc b) -> Node D -> Approx D

    data Traffic i where
      <_> : Node (F i) -> Traffic i
    decode {i} < node > = f i (approx (F i) node)

    Node (var i)  = Traffic i
    Node (kon A)  = A
    Node (sg S T) = Sg (Node S) \ s -> Node (T (approx S s))
    Node (op T)   = Node T
    approx (var i) < t > = f i (approx (F i) t)
    approx (kon A) a = a
    approx (sg S T) (s , t) = s' , approx (T s') t where
      s' = approx S s
    approx (op T) t = approx T t








{--------------------------------------------------------------}
-- Clients and Servers

    data    Client (i : I) : Set
    ClientNode : {b : Two} -> Desc b -> Set
    data    Client i where
      <_> : ClientNode (F i) -> Client i

    record  Server (i : I) : Set
    ServerNode : {b : Two} -> Desc b -> Set
    record Server i where
      coinductive
      constructor [_]
      field
        serve : ServerNode (F i)
    open Server public











{--------------------------------------------------------------}
-- Backchat

    ServerSays : {i : I} -> Client i -> Set
    ServerNodeSays : {b : Two}(D : Desc b) -> ClientNode D -> Set
    ServerSays {i} < cn > = ServerNodeSays (F i) cn

    data ClientSays {i : I}(s : Server i) : Set
    ClientNodeSays : {b : Two}(D : Desc b) -> ServerNode D -> Set
    data ClientSays {i} s where
      <_> : ClientNodeSays (F i) (serve s) -> ClientSays s















{--------------------------------------------------------------}
-- Perceptions of Traffic

    clientTraffic : {i : I}(c : Client i) ->    ServerSays c
                      -> Traffic i
    clientNodeTraffic : {b : Two}(D : Desc b)
      (cn : ClientNode D)(ss : ServerNodeSays D cn) ->
      Node D
    clientTraffic {i} < cn > sns =
      < clientNodeTraffic (F i) cn sns >

    serverTraffic : {i : I}(s : Server i) ->    ClientSays s
                      -> Traffic i
    serverNodeTraffic : {b : Two}(D : Desc b)
      (cn : ServerNode D)(ss : ClientNodeSays D cn) ->
      Node D
    serverTraffic {i} s < cns > =
      < serverNodeTraffic (F i) (serve s) cns >










{--------------------------------------------------------------}
-- Node Business, Client view

    ClientNode (var i) = Client i
    ClientNode (kon A) = A
    ClientNode (sg S T) =
      Sg (ClientNode S) \ cS ->
                                  (ssS : ServerNodeSays S cS) ->
      ClientNode (T (approx S (clientNodeTraffic S cS ssS)))
    ClientNode (op D) = ServerNode D
    ServerNodeSays (var i) c = ServerSays c
    ServerNodeSays (kon A) c = One
    ServerNodeSays (sg S T) (cS , fT) =
        Sg (ServerNodeSays S cS) \ ssS ->
        ServerNodeSays
          (T (approx S (clientNodeTraffic S cS ssS))) (fT ssS)
    ServerNodeSays (op D) s = ClientNodeSays D s
    clientNodeTraffic (var i) c ss = clientTraffic c ss
    clientNodeTraffic (kon A) a <> = a
    clientNodeTraffic (sg S T) (cS , fT) (ssS , ssT) =
      let trS = clientNodeTraffic S cS ssS
      in trS ,
         clientNodeTraffic (T (approx S trS)) (fT ssS) ssT
    clientNodeTraffic (op D) s cs = serverNodeTraffic D s cs

{--------------------------------------------------------------}
-- Node Business, Server view

    ServerNode (var i) = Server i
    ServerNode (kon A) = One
    ServerNode (sg S T) =           Sg (ServerNode S) \ sS ->
      (csS : ClientNodeSays S sS) ->
         ServerNode (T (approx S (serverNodeTraffic S sS csS)))
    ServerNode (op D) = ClientNode D
    ClientNodeSays (var i) s = ClientSays s
    ClientNodeSays (kon A) s = A
    ClientNodeSays (sg S T) (sS , gT) =
      Sg (ClientNodeSays S sS) \ csS ->
      ClientNodeSays
        (T (approx S (serverNodeTraffic S sS csS))) (gT csS)
    ClientNodeSays (op D) c = ServerNodeSays D c
    serverNodeTraffic (var i) s cs = serverTraffic s cs
    serverNodeTraffic (kon A) <> a = a
    serverNodeTraffic (sg S T) (sS , gT) (csS , csT) =
      let trS = serverNodeTraffic S sS csS
      in trS ,
         serverNodeTraffic (T (approx S trS)) (gT csS) csT
    serverNodeTraffic (op D) c ss = clientNodeTraffic D c ss





{--------------------------------------------------------------}
-- coroutining client and server, reconciling traffic

    talk : {i : I}(c : Client i)(s : Server i) ->
            Sg (ClientSays s) \ cs -> Sg (ServerSays c) \ ss ->
            clientTraffic c ss =[ Refl ]= serverTraffic s cs
            
    talks : (DC : Desc tt)(DS : Desc tt) ->
                        (Q : DC =[ Refl ]= DS) ->
        (c : ClientNode DC)(s : ServerNode DS) ->
        Sg (ClientNodeSays DS s) \ cs ->
                               Sg (ServerNodeSays DC c) \ ss ->
        clientNodeTraffic DC c ss
           =[ Resp Node Q ]=
        serverNodeTraffic DS s cs
        
    sklat : (DC : Desc ff)(DS : Desc ff) ->
                        (Q : DC =[ Refl ]= DS) ->
        (c : ClientNode DC)(s : ServerNode DS) ->
        Sg (ClientNodeSays DS s) \ cs ->
                               Sg (ServerNodeSays DC c) \ ss ->
        clientNodeTraffic DC c ss
           =[ Resp Node Q ]=
        serverNodeTraffic DS s cs
        
    talk {i} < c > s with talks (F i) (F i) refl c (serve s)
    ... | cs , ss , q = < cs > , ss , irr (resp <_> q)
    
    talks (var i) ._ refl c s with talk c s
    ... | cs , ss , q = cs , ss , q
    talks (kon A) ._ refl a <> = a , <> , refl
    talks (sg S T) ._ refl (cS , fT) (sS , gT)
      with talks S S refl cS sS
    ... | csS , ssS , qS
        with talks (T (approx S (clientNodeTraffic S cS ssS)))
                   (T (approx S (serverNodeTraffic S sS csS)))
                   (irr (resp T (irr (resp (approx S) qS))))
              (fT ssS) (gT csS)
    ... | csT , ssT , qT
        = (csS , csT)
        , (ssS , ssT)
        , pair= _ _ qS (irr qT)
    talks (op D) ._ refl c s with sklat D D refl s c
    ... | ss , cs , q = cs , ss , sym Refl q
    
    sklat (var {()} i) ._ refl c s
    sklat (kon A) ._ refl a <> = a , <> , refl
    sklat (sg S T) ._ refl (cS , fT) (sS , gT)
      with sklat S S refl cS sS
    ... | csS , ssS , qS
        with sklat (T (approx S (clientNodeTraffic S cS ssS)))
                   (T (approx S (serverNodeTraffic S sS csS)))
                   (irr (resp T (irr (resp (approx S) qS))))
              (fT ssS) (gT (csS))
    ... | csT , ssT , qT
        = (csS , csT)
        , (ssS , ssT)
        , pair= _ _ qS (irr qT)
    sklat (op D) ._ refl c s with talks D D refl s c
    ... | ss , cs , q = cs , ss , sym Refl q

{-
    talks (var i) c s with talk c s
    ... | cs , ss , q = cs , ss , q
    talks (kon A) a <> = a , <> , pure a
    talks (sg S T) (cS , fT) (sS , gT) with talks S cS sS
    ... | = {!!}
    talks (op D) c s = {!!}
-}
