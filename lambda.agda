module lambda where

open import Data.String
open import Data.Bool
open import Relation.Binary.Core
open import Data.Empty

V = String

data List (A : Set) : Set where
 []    : List A
 _::_  : A -> List A -> List A

_∈_ : V -> List V -> Bool
x ∈ [] = false
x ∈ (y :: ys) with x == y
... | true = true
... | false = x ∈ ys


data Expr : Set where
 Var   : V -> Expr
 App   : Expr -> Expr -> Expr
 Lamb  : V -> Expr -> Expr



_+++_ : List V -> List V -> List V
[]        +++ ys = ys
ys        +++ [] = ys
(x :: xs) +++ (y :: ys) with x == y
... | true = x :: (xs +++ ys)
... | false = x :: ( y :: ( xs +++ ys))

_-_ : List V -> V -> List V
[]        - s = []
(x :: xs) - s with x == s
... | true = xs - s
... | false = x :: (xs - s)


FreeVList : Expr -> List V
FreeVList (Var s) = s :: []
FreeVList (App e1 e2) = FreeVList e1 +++ FreeVList e2 
FreeVList (Lamb s e1) = FreeVList e1 - s


data _FreeV_ : V -> Expr -> Set where
  var : {x y : V} -> x ≡ y ->
         x FreeV (Var x)
  appl : {x : V} {e e' : Expr} -> x FreeV e ->
         x FreeV (App e e')
  appr : {x : V} {e e' : Expr} -> x FreeV e' ->
         x FreeV (App e e')
  abs  : {x y : V} {e : Expr} -> x FreeV e -> (x ≡ y -> ⊥) ->
         x FreeV (Lamb y e)

data _NotFreeV_ : V -> Expr -> Set where
  var : {x y : V} -> (x ≡ y -> ⊥) ->
           x NotFreeV (Var y)
  appl : {x : V} {e e' : Expr} -> x NotFreeV e -> x NotFreeV e' ->
           x NotFreeV (App e e')
  absB : {x : V} {e : Expr} ->
            x NotFreeV (Lamb x e)
  absI : {x y : V} {e : Expr} -> x NotFreeV e ->
            x NotFreeV (Lamb y e)
