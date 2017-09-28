module Extrinsic where

open import Common

--------------------------------------------------------------------------------
-- terms are written without explicit context splitting,
-- and then have resources checked

data _|-_ (D : Ctx) : LTy -> Set where
  var     : forall {T}   -> T elem D -> D |- T
  lam     : forall {S T} -> (S :: D) |- T -> D |- (S -o T)
  app     : forall {S T} -> D |- (S -o T) -> D |- S -> D |- T

  nil     : forall {T}   -> D |- LIST T
  cons    : forall {T}   -> D |- (T -o LIST T -o LIST T)
  foldr   : forall {S T} -> D |- T
                         -> D |- (S -o (LIST S & T) -o T)
                         -> D |- (LIST S -o T)

  cmp     : forall {T}   -> D |- (KEY -o KEY -o ((KEY -o KEY -o T) & (KEY -o KEY -o T)) -o T)

  tensor  : forall {S T} -> D |- S -> D |- T -> D |- (S <**> T)
  pm      : forall {S T U} -> D |- (S <**> T) -> (S :: T :: D) |- U -> D |- U

  _&_     : forall {S T} -> D |- S -> D |- T -> D |- (S & T)
  proj1   : forall {S T} -> D |- (S & T) -> D |- S
  proj2   : forall {S T} -> D |- (S & T) -> D |- T

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

  nil   : forall {T} -> emptyPartition |-r nil {T = T}
  cons  : forall {T} -> emptyPartition |-r cons {T = T}
  foldr : forall {S T} {t0 : D |- T} {t1 : D |- (S -o (LIST S & T) -o T)} ->
          emptyPartition |-r t0 -> emptyPartition |-r t1 -> emptyPartition |-r foldr t0 t1

  cmp : forall {T} -> emptyPartition |-r cmp {T = T}

  tensor : forall {G G0 S T} {t0 : D |- S} {t1 : D |- T} {subres : Auto (G0 G=>? G)} ->
           G0 |-r t0 -> (G \\ G0) |-r t1 -> G |-r tensor t0 t1
  pm     : forall {G G0 S T U} {t0 : D |- (S <**> T)} {t1 : (S :: T :: D) |- U}
                  {subres : Auto (G0 G=>? G)} ->
           G0 |-r t0 -> (tt :: tt :: (G \\ G0)) |-r t1 -> G |-r pm t0 t1

  _&_   : forall {G S T} {t0 : D |- S} {t1 : D |- T} -> G |-r t0 -> G |-r t1 -> G |-r (t0 & t1)
  proj1 : forall {G S T} {t : D |- (S & T)} -> G |-r t -> G |-r proj1 t
  proj2 : forall {G S T} {t : D |- (S & T)} -> G |-r t -> G |-r proj2 t

id-t : forall T -> nil |- (T -o T)
id-t T = lam (var here)

id-r : forall T -> nil |-r id-t T
id-r T = lam var

-- x : KEY, y : KEY |- [y,x] : LIST KEY
test-list : (KEY :: KEY :: nil) |- LIST KEY
test-list = app (app cons (var (there here))) (app (app cons (var here)) nil)

test-list-r : fullPartition |-r test-list
test-list-r = app {G0 = ff :: tt :: nil}
                  (app {G0 = ff :: ff :: nil} cons var)
                  (app {G0 = tt :: ff :: nil} (app cons var) nil)

\\-transfer : forall {x} {X : Set x} {l : List X} {G G' G0 : Partition l} ->
              (G \\ G0) == (G' \\ G0) -> G == G'
\\-transfer {G = nil} {nil} {nil} eq = refl
\\-transfer {G = g :: G} {g' :: G'} {g0 :: G0} eq with ::AllInj eq
... | eq0 , eq1 = cong2 _::_ (xor-transfer eq0) (\\-transfer eq1)

--------------------------------------------------------------------------------
-- for any term, there is at most one resource allocation

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
  snd (::AllInj (snd (::AllInj (\\-transfer {G = tt :: tt :: _}
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
  let femp , semp = ::AllInj emp in
  cong2 _::_ (or-xor {x = g0} femp) (other-half semp)

separate-partitions : forall {x} {X : Set x} {l : List X} {G G0 : Partition l} ->
                      G0 G=> G -> zipAll and G0 (G \\ G0) == emptyPartition
separate-partitions {G = nil} {nil} subres = refl
separate-partitions {G = g :: G} {g0 :: G0} (impl , subres) =
  cong2 _::_ (and-xor impl) (separate-partitions subres)

--------------------------------------------------------------------------------
-- we can decide whether a term is resource-correct
-- inferTensorLike is for situations where the resources are split into two (app, tensor, pm)

inferResources : forall {D T} (t : D |- T) -> Dec (Sg _ \ G -> G |-r t)

inferTensorLike : forall {D S T} D0 (t0 : D |- S) (t1 : (D0 ++ D) |- T) ->
                   Dec (Sg _ \ G -> Sg _ \ G0 -> (G0 G=> G) * (G0 |-r t0) *
                                                 ((fullPartition {l = D0} ++All (G \\ G0)) |-r t1))
inferTensorLike D0 t0 t1 with inferResources t0 | inferResources t1
inferTensorLike D0 t0 t1 | yes (G0 , r0) | yes (G1 , r1) with takeDropAll D0 G1
                                                             | ++All-takeDropAll D0 G1
...   | G10 , G11 | G1eq with ==All? _==Two?_ G10 fullPartition
                            | ==All? _==Two?_ (zipAll and G0 G11) emptyPartition
...     | yes full | yes emp =
  yes (zipAll or G0 G11 , G0 , or-G=> G0 G11 , r0
      , subst (_|-r t1)
              (trans (sym G1eq)
                     (cong2 _++All_ full (sym (other-half emp))))
              r1)
...     | yes full | no nemp = no (nemp o f)
  where
  f : (Sg _ \ G -> Sg _ \ G0' -> (G0' G=> G) * (G0' |-r t0)
                               * ((fullPartition {l = D0} ++All (G \\ G0')) |-r t1)) ->
      zipAll and G0 G11 == emptyPartition
  f (G , G0' , subres , r0' , r1') rewrite |-r-partialFunction r0 r0' =
    subst (\ x -> zipAll and G0' x == emptyPartition)
          (sym (snd (++AllInj G10 fullPartition (trans G1eq (|-r-partialFunction r1 r1')))))
          (separate-partitions subres)
...     | no nfull | b =
  no (nfull o \ { (G , G0' , subres , r0' , r1') ->
                  fst (++AllInj G10 fullPartition (trans G1eq (|-r-partialFunction r1 r1'))) })
inferTensorLike D0 t0 t1 | yes p | no np =
  no (np o \ { (G , G0 , subres , r0 , r1) -> fullPartition {l = D0} ++All (G \\ G0) , r1 })
inferTensorLike D0 t0 t1 | no np | b =
  no (np o \ { (G , G0 , subres , r0 , r1) -> G0 , r0 })

inferResources (var x) = yes (singlPartition x , var)
inferResources (lam t) with inferResources t
... | yes (g :: G , r) = mapDec (\ { refl -> G , lam r }) f (g ==Two? tt)
  where
  f : (Sg _ \ G' -> G' |-r lam t) -> g == tt
  f (G' , lam r') with |-r-partialFunction r r'
  ... | refl = refl
inferResources (lam t) | no np = no (np o \ { (G , lam r) -> tt :: G , r })
inferResources (app t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , app {subres = fromWitness subres} r0 r1 })
         (\ { (G , app {G0 = G0} {subres = subres} r0 r1) ->
              G , G0 , toWitness subres , r0 , r1 })
         (inferTensorLike nil t0 t1)
inferResources nil = yes (emptyPartition , nil)
inferResources cons = yes (emptyPartition , cons)
inferResources (foldr t0 t1) with inferResources t0 | inferResources t1
... | yes (G0 , r0) | yes (G1 , r1)
  with ==All? _==Two?_ G0 emptyPartition | ==All? _==Two?_ G1 emptyPartition
...   | yes refl | yes refl = yes (emptyPartition , foldr r0 r1)
...   | yes p | no np = no (np o \ { (.emptyPartition , foldr r0' r1') ->
                                     |-r-partialFunction r1 r1' })
...   | no np | b = no (np o \ { (.emptyPartition , foldr r0' r1') ->
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
         (inferTensorLike nil t0 t1)
inferResources (pm {S} {T} t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , pm {subres = fromWitness subres} r0 r1 })
         (\ { (G , pm {subres = subres} r0 r1) ->
              G , _ , toWitness subres , r0 , r1  })
         (inferTensorLike (S :: T :: nil) t0 t1)
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

--------------------------------------------------------------------------------
-- insertion sort, but hopefully nicer

infixl 4 _$$_
_$$_ : forall {D S T} -> D |- (S -o T) -> D |- S -> D |- T
_$$_ = app

var! : forall {D} m {less : Auto (m <? length D)} -> D |- (D !! #_ m {less})
var! m = var (_ !!Elem # m)

insert : forall {D} -> D |- (LIST KEY -o KEY -o LIST KEY)
insert = foldr (lam (cons $$ var here $$ nil))
               ((lam (lam (lam (cmp $$ var! 2
                                    $$ var! 0
                                    $$ (lam (lam (cons $$ var! 1
                                                       $$ (proj2 (var! 3) $$ var! 0)))
                                      & lam (lam (cons $$ var! 0
                                                       $$ (cons $$ var! 1
                                                                $$ proj1 (var! 3))))))))))

insertion-sort : forall {D} -> D |- (LIST KEY -o LIST KEY)
insertion-sort = foldr nil (lam (lam (insert $$ proj2 (var! 0) $$ var! 1)))

insertion-sort-r : nil |-r insertion-sort {nil}
insertion-sort-r with byDec (inferResources (insertion-sort {nil}))
... | nil , b = b

--------------------------------------------------------------------------------
-- semantics

[[_]]G : {D : Ctx} -> Partition D -> Set
[[ nil ]]G = One
[[_]]G {S :: D} (tt :: G) = [[ S ]]T * [[ G ]]G
[[ ff :: G ]]G = [[ G ]]G

[[emptyPartition]]G : forall D -> [[ emptyPartition {l = D} ]]G == One
[[emptyPartition]]G nil = refl
[[emptyPartition]]G (S :: D) = [[emptyPartition]]G D

ctxIndex : forall {D T} -> T elem D -> [[ D ]]C -> [[ T ]]T
ctxIndex here (t , d) = t
ctxIndex (there v) (t , d) = ctxIndex v d

[[_]]t : forall {D T} -> D |- T -> [[ D ]]C -> [[ T ]]T
[[ var x ]]t d = ctxIndex x d
[[ lam t ]]t d = \ v -> [[ t ]]t (v , d)
[[ app tf te ]]t d = ([[ tf ]]t d) ([[ te ]]t d)
[[ nil ]]t d = nil
[[ cons ]]t d = _::_
[[ foldr tn tc ]]t d = foldright ([[ tn ]]t d) ([[ tc ]]t d)
[[ cmp ]]t d = compare
[[ tensor tl tr ]]t d = [[ tl ]]t d , [[ tr ]]t d
[[ pm t0 t1 ]]t d with [[ t0 ]]t d
... | s , t = [[ t1 ]]t (s , t , d)
[[ tl & tr ]]t d = [[ tl ]]t d , [[ tr ]]t d
[[ proj1 t ]]t d = fst ([[ t ]]t d)
[[ proj2 t ]]t d = snd ([[ t ]]t d)

split : forall {D G} (G0 : Partition D) -> G0 G=> G -> [[ G ]]G -> [[ G0 ]]G * [[ G \\ G0 ]]G
split {G = nil} nil subres g = <> , <>
split {G = tt :: G} (p0 :: G0) (imp , subres) (t , g) with split G0 subres g
split {_} {tt :: G} (tt :: G0) (imp , subres) (t , g) | g0 , g1 = (t , g0) , g1
split {_} {tt :: G} (ff :: G0) (imp , subres) (t , g) | g0 , g1 = g0 , (t , g1)
split {G = ff :: G} (tt :: G0) (imp , subres) g = Zero-elim (imp <>)
split {G = ff :: G} (ff :: G0) (imp , subres) g = split G0 subres g

empty\\empty : (D : Ctx) -> emptyPartition {l = D} \\ emptyPartition == emptyPartition
empty\\empty nil = refl
empty\\empty (S :: D) rewrite empty\\empty D = refl

emptyG=>empty : (D : Ctx) -> emptyPartition {l = D} G=> emptyPartition
emptyG=>empty nil = <>
emptyG=>empty (S :: D) = id , emptyG=>empty D

[[_]]r : forall {D G T} {t : D |- T} -> G |-r t -> [[ G ]]G -> [[ T ]]T
[[ var {T} {e} ]]r = go e
  where
  go : forall {D} (e : T elem D) -> [[ singlPartition e ]]G -> [[ T ]]T
  go here (t , g) = t
  go (there e) g = go e g
[[ lam r ]]r g = λ s → [[ r ]]r (s , g)
[[ app {G0 = G0} {subres = subres} rf re ]]r g with split G0 (toWitness subres) g
... | g0 , g1 = ([[ rf ]]r g0) ([[ re ]]r g1)
[[ nil ]]r g = nil
[[ cons ]]r g = _::_
[[_]]r {D} (foldr rn rc) g = foldright ([[ rn ]]r g) ([[ rc ]]r g)
[[ cmp ]]r g = compare
[[ tensor {G0 = G0} {subres = subres} rl rr ]]r g with split G0 (toWitness subres) g
... | g0 , g1 = [[ rl ]]r g0 , [[ rr ]]r g1
[[ pm {G0 = G0} {subres = subres} r0 r1 ]]r g with split G0 (toWitness subres) g
... | g0 , g1 with [[ r0 ]]r g0
... | rl , rr = [[ r1 ]]r (rl , rr , g1)
[[ rl & rr ]]r g = [[ rl ]]r g , [[ rr ]]r g
[[ proj1 r ]]r g = fst ([[ r ]]r g)
[[ proj2 r ]]r g = snd ([[ r ]]r g)

sorter : List Nat -> List Nat
sorter = [[ insertion-sort ]]t <>

[_|=_*contains_] : KeySet -> {D : Ctx} (G : Partition D) -> [[ G ]]G -> Set
[ K |= nil *contains <> ] = nil >< K
[_|=_*contains_] K {S :: D} (tt :: G) (t , g) =
  Sg _ \ K1 -> Sg _ \ K2 -> (K1 ++ K2) >< K * [ K1 |= S contains t ] * [ K2 |= G *contains g ]
[ K |= ff :: G *contains g ] = [ K |= G *contains g ]

[_|=emptyPartition[_]*contains_] :
  forall K D g -> [ K |= emptyPartition {l = D} *contains g ] == nil >< K
[ K |=emptyPartition[ nil ]*contains g ] = refl
[ K |=emptyPartition[ x :: D ]*contains g ] = [ K |=emptyPartition[ D ]*contains g ]

record Split {D} (G G0 : Partition D) (subres : G0 G=> G) (K : List Nat)
             (g0 : [[ G0 ]]G) (g1 : [[ G \\ G0 ]]G) : Set where
  constructor splitting
  field
    K0 : List Nat
    K1 : List Nat
    p : (K0 ++ K1) >< K
    phi0 : [ K0 |= G0 *contains g0 ]
    phi1 : [ K1 |= (G \\ G0) *contains g1 ]

makeSplitting : forall {D} (G G0 : Partition D) (subres : G0 G=> G)
                (K : List Nat)
                (g : [[ G ]]G) ->
                [ K |= G *contains g ] ->
                let g0 , g1 = split G0 subres g in
                Split G G0 subres K g0 g1
makeSplitting nil nil subres K g phi = splitting nil nil phi permNil permNil
makeSplitting (tt :: G) (p0 :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  with makeSplitting G G0 subres K1 g phi1
makeSplitting (tt :: G) (tt :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  | splitting K10 K11 p1 phi10 phi11 =
  splitting (K0 ++ K10) K11
            (permTrans (permAssoc K0 K10 K11)
             (permTrans (permAppR K0 p1)
                        p))
            (K0 , K10 , permRefl _ , phi0 , phi10) phi11
makeSplitting (tt :: G) (ff :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  | splitting K10 K11 p1 phi10 phi11 =
  splitting K10 (K0 ++ K11)
            (permTrans (permSymm (permAssoc K10 K0 K11))
             (permTrans (permAppL (permSwap++ K10 K0))
              (permTrans (permAssoc K0 K10 K11)
               (permTrans (permAppR K0 p1)
                          p))))
            phi10 (K0 , K11 , permRefl _ , phi0 , phi11)
makeSplitting (ff :: G) (tt :: G0) (imp , subres) K g phi = Zero-elim (imp <>)
makeSplitting (ff :: G) (ff :: G0) (imp , subres) K g phi with makeSplitting G G0 subres K g phi
... | splitting K0 K1 p phi0 phi1 = splitting K0 K1 p phi0 phi1

foldright-welltyped : forall {S T} n c ->
                      [ nil |= T contains n ] ->
                      [ nil |= (S -o (LIST S & T) -o T) contains c ] ->
                      [ nil |= (LIST S -o T) contains foldright n c ]
foldright-welltyped n c phin phic K nil phiss rewrite nilPerm phiss = phin
foldright-welltyped {S} {T} n c phin phic K (s :: ss) (Ks , Kss , p , phis , phiss) =
  preservePerm T _ p
               (phic Ks s phis Kss _
                     (phiss , foldright-welltyped {S} {T} n c phin phic Kss ss phiss))

fundamental : forall {D G T} ->
              {t : D |- T} (r : G |-r t) ->
              forall K g -> [ K |= G *contains g ] -> [ K |= T contains ([[ r ]]r g) ]
fundamental {D} {G} {T} {var e} var = go e
  where
  go : forall {D} (e : T elem D) K g ->
       [ K |= singlPartition e *contains g ] -> [ K |= T contains [[ var {e = e} ]]r g ]
  go {S :: D} here K (s , g) (K0 , K1 , perm , psi0 , psi1) rewrite [ K1 |=emptyPartition[ D ]*contains g ] | nilPerm psi1 | ++nil K0 = preservePerm S s perm psi0
  go (there e) K g phi = go e K g phi
fundamental (lam r) K g phi =
  \ K' s psi -> fundamental r (K ++ K') (s , g) (K' , K , permSwap++ K' K , psi , phi)
fundamental (app {G} {G0} {S = S} {T} {subres = subres} rf re) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1 =
  preservePerm T _ p ((fundamental rf K0 _ phi0) _ _ (fundamental re K1 _ phi1))
fundamental {D} nil K g phi rewrite [ K |=emptyPartition[ D ]*contains g ] = phi
fundamental {D} cons K g phi rewrite [ K |=emptyPartition[ D ]*contains g ] | nilPerm phi =
  \ K0 s0 phi0 K1 s1 phi1 -> K0 , K1 , permRefl _ , phi0 , phi1
fundamental {D} (foldr {S} {T} rn rc) K g phi
  rewrite [ K |=emptyPartition[ D ]*contains g ] | nilPerm phi =
  foldright-welltyped {S} {T} _ _
                      (fundamental rn nil _ (subst id
                                                   (sym ([ nil |=emptyPartition[ D ]*contains _ ]))
                                                   (permRefl nil)))
                      (fundamental rc nil _ (subst id
                                                   (sym ([ nil |=emptyPartition[ D ]*contains _ ]))
                                                   (permRefl nil)))
fundamental {D} {G} {T} (cmp {S}) K g phi K0 s0 phi0 K1 s1 phi1 K2 s2 phi2
  rewrite [ K |=emptyPartition[ D ]*contains g ] | nilPerm phi with compareNat s0 s1
... | lt .s0 k = preservePerm S _ (lem-2 K0 K1 K2) (snd phi2 K1 s1 phi1 K0 s0 phi0)
... | gte k .s1 = preservePerm S _ (lem-1 K0 K1 K2) (fst phi2 K0 s0 phi0 K1 s1 phi1)
fundamental (tensor {G} {G0} {subres = subres} rl rr) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1 =
  K0 , K1 , p , fundamental rl K0 _ phi0 , fundamental rr K1 _ phi1
fundamental (pm {G} {G0} {S} {T} {U} {subres = subres} r0 r1) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1
  with fundamental r0 K0 _ phi0
... | K00 , K01 , p0 , phi00 , phi01 =
  preservePerm U _
               (subst (_>< K) (++Assoc K00 K01 K1) (permTrans (permAppL p0) p))
               (fundamental r1 (K00 ++ (K01 ++ K1)) _
                            (K00 , K01 ++ K1 , permRefl _ , phi00
                            , K01 , K1 , permRefl _ , phi01
                            , phi1))
fundamental (rl & rr) K g phi = fundamental rl K g phi , fundamental rr K g phi
fundamental (proj1 r) K g phi = fst (fundamental r K g phi)
fundamental (proj2 r) K g phi = snd (fundamental r K g phi)
