module substitution where

open import lambda
open import Data.String


data subst : Set where
 _⟶_ : String -> Expr -> subst


_/_ : Expr -> subst -> Expr
Var v / δ = {!!}
(App e e') / δ = {!!}
(Lamb v e) / δ = {!!}
