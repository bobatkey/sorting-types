module Intrinsic where

open import Common
--------------------------------------------------------------------------------
-- explicit splitting presentation of terms

data _|-_ : Ctx -> LTy -> Set where
  var : forall {T} -> (T :: nil) |- T
  lam : forall {G S T} -> (S :: G) |- T -> G |- (S -o T)
  app : forall {G G0 G1 S T} -> G >< (G0 ++ G1) -> G0 |- (S -o T) -> G1 |- S -> G |- T

  nil   : forall {T}   -> nil |- LIST T
  cons  : forall {T}   -> nil |- (T -o LIST T -o LIST T)
  foldr : forall {S T} -> nil |- T
                  -> nil |- (S -o (LIST S & T) -o T)
                  -> nil |- (LIST S -o T)

  cmp   : forall {T}   -> nil |- (KEY -o KEY -o ((KEY -o KEY -o T) & (KEY -o KEY -o T)) -o T)

  tensor  : forall {G G0 G1 S T} -> G >< (G0 ++ G1) -> G0 |- S -> G1 |- T -> G |- (S <**> T)
  pm      : forall {G G0 G1 S T U} -> G >< (G0 ++ G1) -> G0 |- (S <**> T) -> (S :: T :: G1) |- U -> G |- U

  _&_   : forall {G S T} -> G |- S -> G |- T -> G |- (S & T)
  proj1    : forall {G S T} -> G |- (S & T) -> G |- S
  proj2    : forall {G S T} -> G |- (S & T) -> G |- T

--------------------------------------------------------------------------------
-- insertion sort
_$$_ : forall {G0 G1 S T} -> G0 |- (S -o T) -> G1 |- S -> (G0 ++ G1) |- T
t1 $$ t2 = app (permRefl _) t1 t2

infixl 4 _$$_

insert : nil |- (LIST KEY -o KEY -o LIST KEY)
insert = foldr (lam (cons $$ var $$ nil))
               (lam (lam (lam (app (permSkip permSwap)
                                   (cmp $$ var $$ var)
                                   (lam (lam (app (permSkip permSwap) (cons $$ var) (proj2 var $$ var)))
                                    &
                                    lam (lam (cons $$ var $$ (cons $$ var $$ proj1 var))))))))

insertion-sort : nil |- (LIST KEY -o LIST KEY)
insertion-sort = foldr nil (lam (lam (insert $$ proj2 var $$ var)))

--------------------------------------------------------------------------------
[[_]]p : forall {G G'} -> G >< G' -> [[ G ]]C -> [[ G' ]]C
[[ permNil ]]p         <>          = <>
[[ permSkip p ]]p      (x , g)     = x , [[ p ]]p g
[[ permSwap ]]p        (x , y , g) = (y , x , g)
[[ permTrans p1 p2 ]]p g           = [[ p2 ]]p ([[ p1 ]]p g)

split : forall G0 {G1} -> [[ G0 ++ G1 ]]C -> [[ G0 ]]C * [[ G1 ]]C
split nil           g = <> , g
split (T :: G0) (t , g) with split G0 g
...                     | g0 , g1 = (t , g0) , g1

[[_]]t : forall {G T} -> G |- T -> [[ G ]]C -> [[ T ]]T
[[ var ]]t         (t , <>) = t
[[ lam t ]]t       g  = \ v -> [[ t ]]t (v , g)
[[ app {_} {G0} p t1 t2 ]]t g  with split G0 ([[ p ]]p g) 
...                          | g0 , g1 = [[ t1 ]]t g0 ([[ t2 ]]t g1)
[[ nil ]]t         <> = nil
[[ cons ]]t        <> = _::_
[[ foldr t1 t2 ]]t <> = foldright ([[ t1 ]]t <>) ([[ t2 ]]t <>)
[[ cmp ]]t         <> = compare
[[ tensor {_} {G0} p t1 t2 ]]t g with split G0 ([[ p ]]p g)
...                            | g0 , g1 = ([[ t1 ]]t g0) , ([[ t2 ]]t g1)
[[ pm {_} {G0} p t1 t2 ]]t g with split G0 ([[ p ]]p g)
...                         | g0 , g1 with [[ t1 ]]t g0
...                                   | s , t = [[ t2 ]]t (s , t , g1)
[[ t1 & t2 ]]t     g  = [[ t1 ]]t g , [[ t2 ]]t g
[[ proj1 t ]]t     g  = fst ([[ t ]]t g)
[[ proj2 t ]]t     g  = snd ([[ t ]]t g)

sorter : List Nat -> List Nat
sorter = [[ insertion-sort ]]t <>

--------------------------------------------------------------------------------
-- Logical Predicates to prove the permutation property

[_|=_*contains_] : KeySet -> (G : Ctx) -> [[ G ]]C -> Set
[ K |= nil    *contains <>    ] = nil >< K
[ K |= T :: G *contains t , g ] = Sg KeySet \ K1 -> Sg KeySet \ K2 -> (K1 ++ K2) >< K * [ K1 |= T contains t ] * [ K2 |= G *contains g ]

foldright-welltyped : forall {T S} n f ->
                      [ nil |= T contains n ] ->
                      [ nil |= (S -o (LIST S & T) -o T) contains f ] ->
                      [ nil |= (LIST S -o T) contains foldright n f ]
foldright-welltyped         n f psin psif Kl nil       phil rewrite nilPerm phil = psin
foldright-welltyped {T} {S} n f psin psif Kl (s :: ss) (K1 , K2 , phi , phis , phiss) rewrite ++nil Kl =
    preservePerm T _ phi (psif K1 s phis K2 (ss , foldright n f ss) (phiss , foldright-welltyped {T} {S} n f psin psif K2 ss phiss))

compare-welltyped : forall T ->
                    [ nil |= (KEY -o KEY -o ((KEY -o KEY -o T) & (KEY -o KEY -o T)) -o T) contains compare ]

compare-welltyped T K0 x0 phi0 K1 x1 phi1 K2 (GTE , LT) (phi2 , psi2) with compareNat x0 x1
compare-welltyped T K0 x0 phi0 K1 .(succ (x0 +N k)) phi1 K2 (GTE , LT) (phi2 , psi2) | lt .x0 k  =
    preservePerm T _ (lem-2 K0 K1 K2) (psi2 K1 (succ (x0 +N k)) phi1 K0 x0 phi0)
compare-welltyped T K0 .(x1 +N k) phi0 K1 x1 phi1 K2 (GTE , LT) (phi2 , psi2)        | gte k .x1 =
    preservePerm T _ (lem-1 K0 K1 K2) (phi2 K0 (x1 +N k) phi0 K1 x1 phi1)


respPerm : forall {G G'} -> (p : G >< G') -> (g : [[ G ]]C) -> forall {K} -> [ K |= G *contains g ] -> [ K |= G' *contains [[ p ]]p g ]
respPerm permNil           g           phi = phi
respPerm (permSkip p)      (t , g)     (K1 , K2 , phi , psi1 , psi2) = K1 , K2 , phi , psi1 , respPerm p g psi2
respPerm permSwap (s , t , g) (K1 , K2 , phi1 , psi1 , K3 , K4 , phi2 , psi3 , psi4) =
  K3 , K1 ++ K4 , permTrans (permSymm (permAssoc K3 K1 K4)) (permTrans (permAppL (permSwap++ K3 K1)) (permTrans (permAssoc K1 K3 K4) (permTrans (permAppR K1 phi2) phi1))) , psi3 , K1 , K4 , permRefl _ , psi1 , psi4
respPerm (permTrans p1 p2) g phi = respPerm p2 _ (respPerm p1 _ phi)


data Split (G0 G1 : Ctx) (K : List Nat) : (g0 : [[ G0 ]]C) -> (g1 : [[ G1 ]]C) -> Set where
  splitting : (g0 : [[ G0 ]]C) ->
              (g1 : [[ G1 ]]C) ->
              (K0 : List Nat) ->
              (K1 : List Nat) ->
              (p  : (K0 ++ K1) >< K) ->
              (phi0 : [ K0 |= G0 *contains g0 ]) ->
              (phi1 : [ K1 |= G1 *contains g1 ]) ->
              Split G0 G1 K g0 g1

makeSplitting : forall G0 G1 ->
                (g : [[ G0 ++ G1 ]]C) ->
                (K : List Nat) ->
                [ K |= G0 ++ G1 *contains g ] ->
                Split G0 G1 K (fst (split G0 g)) (snd (split G0 g))
makeSplitting nil       G1 g       K phi = splitting <> g nil K (permRefl K) permNil phi
makeSplitting (T :: G0) G1 (t , g) K (K1 , K2 , phi , psi1 , psi2) with makeSplitting G0 G1 g K2 psi2
makeSplitting (T :: G0) G1 (t , g) K (K1' , K2 , phi , psi1 , psi2) | splitting .(fst (split G0 g)) .(snd (split G0 g)) K0 K1 p phi0 phi1
        = splitting (t , fst (split G0 g))
                    (snd (split G0 g))
                    (K1' ++ K0)
                    K1
                    (permTrans (permAssoc K1' K0 K1) (permTrans (permAppR K1' p) phi))
                    (K1' , K0 , permRefl (K1' ++ K0) , psi1 , phi0)
                    phi1

fundamental : forall {G T} ->
              (t : G |- T) ->
              forall K g -> [ K |= G *contains g ] -> [ K |= T contains ([[ t ]]t g) ]

fundamental (var {T}) K (t , <>) (K1 , K2 , phi , tOK , nilK2) rewrite nilPerm nilK2 | ++nil K1 = preservePerm T t phi tOK
fundamental (lam t)       K g phi  = \ K' s psi -> fundamental t (K ++ K') (s , g) (K' , K , permSwap++ K' K , psi , phi)
fundamental {_} {T} (app {._} {G0} {G1} p t1 t2) K g phi with makeSplitting G0 G1 ([[ p ]]p g) K (respPerm p g phi)
... | splitting ._ ._ K0 K1 p' phi0 phi1 = preservePerm T _ p' (fundamental t1 K0 _ phi0 K1 ([[ t2 ]]t _) (fundamental t2 K1 _ phi1))
fundamental nil           K g phi = phi
fundamental cons          K g phi rewrite nilPerm phi = \ K0 s0 psi0 K1 s1 psi1 -> K0 , K1 , permRefl _ , psi0 , psi1
fundamental (foldr {S}{T} t1 t2) K g phi rewrite nilPerm phi = foldright-welltyped {T} {S} _ _ (fundamental t1 nil <> permNil) (fundamental t2 nil <> permNil)
fundamental (cmp {T})     K g phi rewrite nilPerm phi = compare-welltyped T
fundamental (tensor {_} {G0} {G1} p t1 t2) K g phi with makeSplitting G0 G1 ([[ p ]]p g) K (respPerm p g phi)
... | splitting ._ ._ K0 K1 p' phi0 phi1 = K0 , K1 , p' , fundamental t1 K0 _ phi0 , fundamental t2 K1 _ phi1
fundamental (pm {_} {G0} {G1} {S} {T} {U} p t1 t2) K g phi with makeSplitting G0 G1 ([[ p ]]p g) K (respPerm p g phi)
... | splitting ._ ._ K0 K1 p' phi0 phi1 with fundamental t1 K0 _ phi0 
... | K01 , K02 , p'' , phi01 , phi02 = preservePerm U _ (permTrans (permTrans (permSymm (permAssoc K01 K02 K1)) (permAppL p'')) p')
                                      (fundamental t2 (K01 ++ (K02 ++ K1)) _ (K01 , K02 ++ K1 , permRefl _ , phi01 , K02 , K1 , permRefl _ , phi02 , phi1))
fundamental (t1 & t2)     K g phi  = fundamental t1 K g phi , fundamental t2 K g phi
fundamental (proj1 t)     K g phi  = fst (fundamental t K g phi)
fundamental (proj2 t)     K g phi  = snd (fundamental t K g phi)

isPermutation : (t : nil |- (LIST KEY -o LIST KEY)) -> (l : List Nat) -> ([[ t ]]t <> l) >< l
isPermutation t l with fundamental t nil <> permNil l l (listRep l)
...               | x rewrite ++nil l = repList l ([[ t ]]t <> l) x
