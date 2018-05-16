module lambda where

open import Data.String
open import Data.Bool

data List (A : Set) : Set where
 []    : List A
 _::_  : A -> List A -> List A


data Expr : Set where
 Var   : String -> Expr
 App   : Expr -> Expr -> Expr
 Lamb  : String -> Expr -> Expr



_+++_ : List String -> List String -> List String
[]        +++ ys = ys
ys        +++ [] = ys
(x :: xs) +++ (y :: ys) with x == y
... | true = x :: (xs +++ ys)
... | false = x :: ( y :: ( xs +++ ys))

_-_ : List String -> String -> List String
[]        - s = []
(x :: xs) - s with x == s
... | true = xs - s
... | false = x :: (xs - s)

FreeV : Expr -> List String
FreeV (Var s) = s :: []
FreeV (App e1 e2) = FreeV e1 +++ FreeV e2 
FreeV (Lamb s e1) = FreeV e1 - s
