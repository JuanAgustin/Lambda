module substitution where

open import lambda
open import Data.String
open import Data.Product
open import Data.Bool

{-
data subst : Set where
 _⟶_ : String -> Expr -> subst
 -}

Δ = V -> Expr

_+_ : Δ -> (V × Expr) -> Δ
(δ + ( x , M )) y with x == y
... | true = M
... | false = δ y

_/_ : Expr -> Δ -> Expr
Var v / δ = δ v
(App e e') / δ = App (e / δ) (e' / δ)
(Lamb x e) / δ = Lamb y (e / (δ + (x , Var y)))
  where y = ?
