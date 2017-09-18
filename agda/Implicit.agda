module Implicit where

open import Common

--------------------------------------------------------------------------------
-- terms are written without explicit context splitting,
-- and then have resources checked

data _|-_ (D : Ctx) : LTy -> Set where
  var : forall {T} -> T elem D -> D |- T
  lam : forall {S T} -> (S :: D) |- T -> D |- (S -o T)
  app : forall {S T} -> D |- (S -o T) -> D |- S -> D |- T

  nil   : forall {T}   -> D |- LIST T
  cons  : forall {T}   -> D |- (T -o LIST T -o LIST T)
  foldr : forall {S T} -> D |- T
                         -> D |- (S -o (LIST S & T) -o T)
                         -> D |- (LIST S -o T)

  cmp   : forall {T}   -> D |- (KEY -o KEY -o ((KEY -o KEY -o T) & (KEY -o KEY -o T)) -o T)

  tensor  : forall {S T} -> D |- S -> D |- T -> D |- (S <**> T)
  pm      : forall {S T U} -> D |- (S <**> T) -> (S :: T :: D) |- U -> D |- U

  _&_   : forall {S T} -> D |- S -> D |- T -> D |- (S & T)
  proj1    : forall {S T} -> D |- (S & T) -> D |- S
  proj2    : forall {S T} -> D |- (S & T) -> D |- T

-- where resources have to be split, we specify what goes to the left,
-- and then everything else we were given goes to the right
_\\_ : forall {x} {X : Set x} {l : List X} -> Partition l -> Partition l -> Partition l
_\\_ = zipAll xor

-- the new allocations of resources should only use resources available originally
_G=>_ : forall {x} {X : Set x} {l : List X} (G0 G : Partition l) -> Set
G0 G=> G = fold One _*_ (allTags (zipAll (\ x y -> T x -> T y) G0 G))

_->?_ : forall x y -> Dec (T x -> T y)
tt ->? tt = yes (λ x -> <>)
tt ->? ff = no (λ z -> z <>)
ff ->? y = yes (λ ())

_G=>?_ : forall {x} {X : Set x} {l : List X} (G0 G : Partition l) -> Dec (G0 G=> G)
nil G=>? nil = yes <>
(p0 :: G0) G=>? (p :: G) = (p0 ->? p) *? (G0 G=>? G)

data _|-r_ {D} : Partition D -> forall {T} -> D |- T -> Set where
  var : forall {T} {e : T elem D} -> singlPartition e |-r var e
  lam : forall {G S T} {t : (S :: D) |- T} -> (tt :: G) |-r t -> G |-r lam t
  app : forall {G G0 S T} {t0 : D |- (S -o T)} {t1 : D |- S} {subres : Auto (G0 G=>? G)} ->
        G0 |-r t0 -> (G \\ G0) |-r t1 -> G |-r app t0 t1

  nil : forall {T} -> emptyPartition |-r nil {T = T}
  cons : forall {T} -> emptyPartition |-r cons {T = T}
  foldr : forall {S T} {t0 : D |- T} {t1 : D |- (S -o (LIST S & T) -o T)} ->
          emptyPartition |-r t0 -> emptyPartition |-r t1 -> emptyPartition |-r foldr t0 t1

  cmp : forall {T} -> emptyPartition |-r cmp {T = T}

  tensor : forall {G G0 S T} {t0 : D |- S} {t1 : D |- T} {subres : Auto (G0 G=>? G)} ->
           G0 |-r t0 -> (G \\ G0) |-r t1 -> G |-r tensor t0 t1
  pm : forall {G G0 S T U} {t0 : D |- (S <**> T)} {t1 : (S :: T :: D) |- U}
              {subres : Auto (G0 G=>? G)} ->
       G0 |-r t0 -> (tt :: tt :: (G \\ G0)) |-r t1 -> G |-r pm t0 t1

  _&_ : forall {G S T} {t0 : D |- S} {t1 : D |- T} -> G |-r t0 -> G |-r t1 -> G |-r (t0 & t1)
  proj1 : forall {G S T} {t : D |- (S & T)} -> G |-r t -> G |-r proj1 t
  proj2 : forall {G S T} {t : D |- (S & T)} -> G |-r t -> G |-r proj2 t

id-t : forall T -> nil |- (T -o T)
id-t T = lam (var here)

id-r : forall T -> nil |-r id-t T
id-r T = lam var

-- x : KEY, y : KEY |- [y,x] : LIST KEY
test-list : (KEY :: KEY :: nil) |- LIST KEY
test-list = app (app cons (var (there here))) (app (app cons (var here)) nil)

test-list-r : (tt :: tt :: nil) |-r test-list
test-list-r = app {G0 = ff :: tt :: nil}
                  (app {G0 = ff :: ff :: nil} cons var)
                  (app {G0 = tt :: ff :: nil} (app cons var) nil)

{-
test-list-r-bad : (tt :: tt :: nil) |-r test-list
test-list-r-bad = app {G0 = tt :: ff :: nil}
                      (app cons var) -- ff != tt of type Two
                      ?
-}

{-+}
data _|-r_ {D} : Ctx -> forall {T} -> D |- T -> Set where
  var : forall {T} {e : T elem D} -> (T :: nil) |-r var e
  lam : forall {G S T} {t : (S :: D) |- T} -> (S :: G) |-r t -> G |-r lam t
  app : forall {G G0 G1 S T} {t0 : D |- (S -o T)} {t1 : D |- S} ->
        G >< (G0 ++ G1) -> G0 |-r t0 -> G1 |-r t1 -> G |-r app t0 t1

  nil : forall {T} -> nil |-r nil {T = T}
  cons : forall {T} -> nil |-r cons {T = T}
  foldr : forall {S T} {t0 : D |- T} {t1 : D |- (S -o (LIST S & T) -o T)} ->
          nil |-r t0 -> nil |-r t1 -> nil |-r foldr t0 t1

id : forall T -> nil |- (T -o T)
id T = lam (var here)

id-r : forall T -> nil |-r id T
id-r T = lam var

-- x : KEY, y : KEY |- [y,x] : LIST KEY
test-list : (KEY :: KEY :: nil) |- LIST KEY
test-list = app (app cons (var (there here))) (app (app cons (var here)) nil)

-- The two resources are sent to the right places.
test-list-r : (KEY :: KEY :: nil) |-r test-list
test-list-r = app permSwap (app (permRefl _) cons var) (app (permRefl _) (app (permRefl _) cons var) nil)

-- The order of the resources is not swapped, but it is still accepted.
test-list-r-bad : (KEY :: KEY :: nil) |-r test-list
test-list-r-bad = app (permRefl _) (app (permRefl _) cons var) (app (permRefl _) (app (permRefl _) cons var) nil)
{+-}

\\-transfer : forall {x} {X : Set x} {l : List X} {G G' G0 : Partition l} ->
              (G \\ G0) == (G' \\ G0) -> G == G'
\\-transfer {G = nil} {nil} {nil} eq = refl
\\-transfer {G = g :: G} {g' :: G'} {g0 :: G0} eq with All::Inj eq
... | eq0 , eq1 = cong2 _::_ (xor-transfer eq0) (\\-transfer eq1)

|-r-partialFunction : forall {D T G G'} {t : D |- T} ->
                      G |-r t -> G' |-r t -> G == G'
|-r-partialFunction var var = refl
|-r-partialFunction (lam r) (lam r') with |-r-partialFunction r r'
... | refl = refl
|-r-partialFunction (app r0 r1) (app r0' r1') with |-r-partialFunction r0 r0'
                                                 | |-r-partialFunction r1 r1'
... | refl | G\\G0eq = \\-transfer G\\G0eq
|-r-partialFunction nil nil = refl
|-r-partialFunction cons cons = refl
|-r-partialFunction (foldr r0 r1) (foldr r0' r1') = refl
|-r-partialFunction cmp cmp = refl
|-r-partialFunction (tensor r0 r1) (tensor r0' r1') with |-r-partialFunction r0 r0'
                                                       | |-r-partialFunction r1 r1'
... | refl | G\\G0eq = \\-transfer G\\G0eq
|-r-partialFunction (pm r0 r1) (pm r0' r1') with |-r-partialFunction r0 r0'
                                               | |-r-partialFunction r1 r1'
... | refl | G\\G0eq =
  snd (All::Inj (snd (All::Inj (\\-transfer {G = tt :: tt :: _}
                                            {tt :: tt :: _}
                                            {ff :: ff :: _} G\\G0eq))))
|-r-partialFunction (r0 & r1) (r0' & r1') rewrite |-r-partialFunction r0 r0'
                                                | |-r-partialFunction r1 r1' = refl
|-r-partialFunction (proj1 r) (proj1 r') = |-r-partialFunction r r'
|-r-partialFunction (proj2 r) (proj2 r') = |-r-partialFunction r r'

or-G=> : forall {x} {X : Set x} {l : List X} (G0 G1 : Partition l) -> G0 G=> zipAll or G0 G1
or-G=> nil nil = <>
or-G=> (g0 :: G0) (g1 :: G1) = ->-or , or-G=> G0 G1

other-half : forall {x} {X : Set x} {l : List X} {G0 G1 : Partition l} ->
             zipAll and G0 G1 == emptyPartition -> zipAll or G0 G1 \\ G0 == G1
other-half {G0 = nil} {nil} emp = refl
other-half {G0 = g0 :: G0} {g1 :: G1} emp =
  let femp , semp = All::Inj emp in
  cong2 _::_ (or-xor {x = g0} femp) (other-half semp)

separate-partitions : forall {x} {X : Set x} {l : List X} {G G0 : Partition l} ->
                      G0 G=> G -> zipAll and G0 (G \\ G0) == emptyPartition
separate-partitions {G = nil} {nil} subres = refl
separate-partitions {G = g :: G} {g0 :: G0} (impl , subres) =
  cong2 _::_ (and-xor impl) (separate-partitions subres)

inferTensorLike : forall {D S T} (t0 : D |- S) (t1 : D |- T) ->
                  Dec (Sg _ \ G -> Sg _ \ G0 -> (G0 G=> G) * (G0 |-r t0) * ((G \\ G0) |-r t1))
inferResources : forall {D T} (t : D |- T) -> Dec (Sg _ \ G -> G |-r t)

inferTensorLike t0 t1 with inferResources t0 | inferResources t1
inferTensorLike t0 t1 | yes (G0 , r0) | yes (G1 , r1)
  with ==All? _==Two?_ (zipAll and G0 G1) emptyPartition
... | yes emp =
  yes (zipAll or G0 G1 , G0 , or-G=> G0 G1
      , r0 , subst (\ G -> G |-r t1) (sym (other-half emp)) r1)
... | no nemp = no (nemp o f)
  where
  f : (Sg _ \ G -> Sg _ \ G0' -> (G0' G=> G) * (G0' |-r t0) * ((G \\ G0') |-r t1)) ->
      zipAll and G0 G1 == emptyPartition
  f (G , G0' , subres , r0' , r1') rewrite |-r-partialFunction r0 r0'
                                         | |-r-partialFunction r1 r1' =
    separate-partitions subres
inferTensorLike t0 t1 | yes _ | no np =
  no (np o \ { (G , G0 , subres , r0 , r1) -> (G \\ G0) , r1 })
inferTensorLike t0 t1 | no np | b =
  no (np o \ { (G , G0 , subres , r0 , r1) -> G0 , r0 })

inferResources (var x) = yes (singlPartition x , var)
inferResources (lam t) with inferResources t
-- TODO: these two yes cases might be coalesced
... | yes (tt :: G , r) = yes (G , lam r)
... | yes (ff :: G , r) = no f
  where
  f : (Sg _ \ G' -> G' |-r lam t) -> Zero
  f (G' , lam r') with |-r-partialFunction r r'
  ... | ()
inferResources (lam t) | no np = no (np o \ { (G , lam r) -> tt :: G , r })
inferResources (app t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , app {subres = fromWitness subres} r0 r1 })
         (\ { (G , app {G0 = G0} {subres = subres} r0 r1) ->
              G , G0 , toWitness subres , r0 , r1 })
         (inferTensorLike t0 t1)
inferResources nil = yes (emptyPartition , nil)
inferResources cons = yes (emptyPartition , cons)
inferResources (foldr t0 t1) with inferResources t0 | inferResources t1
... | yes (G0 , r0) | yes (G1 , r1)
  with ==All? _==Two?_ G0 emptyPartition | ==All? _==Two?_ G1 emptyPartition
... | yes refl | yes refl = yes (emptyPartition , foldr r0 r1)
... | yes p | no np = no (np o \ { (.emptyPartition , foldr r0' r1') ->
                                   |-r-partialFunction r1 r1' })
... | no np | b = no (np o \ { (.emptyPartition , foldr r0' r1') ->
                               |-r-partialFunction r0 r0' })
inferResources (foldr t0 t1) | yes p | no np =
  no (np o \ { (.emptyPartition , foldr r0 r1) -> emptyPartition , r1 })
inferResources (foldr t0 t1) | no np | b =
  no (np o \ { (.emptyPartition , foldr r0 r1) -> emptyPartition , r0 })
inferResources cmp = yes (emptyPartition , cmp)
inferResources (tensor t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , tensor {subres = fromWitness subres} r0 r1 })
         (\ { (G , tensor {subres = subres} r0 r1) ->
              G , _ , toWitness subres , r0 , r1  })
         (inferTensorLike t0 t1)
inferResources (pm t0 t1) with inferResources t0 | inferResources t1
... | yes (G0 , r0) | yes (x :: y :: G1 , r1) with
  ==All? _==Two?_ (zipAll and G0 G1) emptyPartition
... | yes emp =
  mapDec (\ { (refl , refl) ->
              zipAll or G0 G1
              , pm {subres = fromWitness (or-G=> G0 G1)}
                   r0
                   (subst (\ x -> (tt :: tt :: x) |-r t1) (sym (other-half emp)) r1) })
         (\ { (G , pm r0' r1') ->
              map* id (fst o All::Inj) (All::Inj (|-r-partialFunction r1 r1')) })
         ((x ==Two? tt) *? (y ==Two? tt))
... | no nemp =
  no (nemp o f)
  where
  f : (Sg _ \ G -> G |-r pm t0 t1) -> zipAll and G0 G1 == emptyPartition
  f (G , pm {subres = subres} r0' r1') with |-r-partialFunction r0 r0'
                                          | |-r-partialFunction r1 r1'
  ... | refl | refl = separate-partitions (toWitness subres)
inferResources (pm t0 t1) | yes p | no np = no (np o \ { (G , pm r0 r1) -> _ , r1 })
inferResources (pm t0 t1) | no np | b = no (np o \ { (G , pm r0 r1) -> _ , r0 })
inferResources (t0 & t1) with inferResources t0 | inferResources t1
... | yes (G , r0) | yes (G' , r1) =
  mapDec (\ { refl -> G , r0 & r1 })
         (\ { (G'' , r0' & r1') ->
              trans (|-r-partialFunction r0 r0') (|-r-partialFunction r1' r1) })
         (==All? _==Two?_ G G')
inferResources (t0 & t1) | yes p | no np = no (np o \ { (G , r0 & r1) -> G , r1 })
inferResources (t0 & t1) | no np | b = no (np o \ { (G , r0 & r1) -> G , r0 })
inferResources (proj1 t) =
  mapDec (mapSg id proj1) (mapSg id \ { (proj1 r) -> r }) (inferResources t)
inferResources (proj2 t) =
  mapDec (mapSg id proj2) (mapSg id \ { (proj2 r) -> r }) (inferResources t)
