module lambda where

open import Data.String
open import Data.Bool

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

FreeV : Expr -> List V
FreeV (Var s) = s :: []
FreeV (App e1 e2) = FreeV e1 +++ FreeV e2 
FreeV (Lamb s e1) = FreeV e1 - s
