module substitution where

open import lambda
open import Data.String

{-
data subst : Set where
 _⟶_ : String -> Expr -> subst
 -}

subst = String -> Expr

_/_ : Expr -> subst -> Expr
Var v / δ = δ v
(App e e') / δ = App (e / δ) (e' / δ)
(Lamb v e) / δ = ?
