module substitution  where



open import lambda
open import Data.String
open import Data.Product
open import Data.Bool


module Subst (fresh : V -> List V -> V) where


    {-
    data subst : Set where
     _⟶_ : String -> Expr -> subst
     -}
    
    Δ = V -> Expr

    idd : Δ
    idd x = Var x


    _+_ : Δ -> (V × Expr) -> Δ
    (δ + ( x , M )) y with x == y
    ... | true = M
    ... | false = δ y
    
    FreeVSubs : Δ -> List V -> List V
    FreeVSubs δ [] = []
    FreeVSubs δ (x :: xs) = FreeV (δ x) +++ FreeVSubs δ xs
    
    _/_ : Expr -> Δ -> Expr
    Var v / δ = δ v
    (App e e') / δ = App (e / δ) (e' / δ)
    (Lamb x e) / δ = Lamb y (e / (δ + (x , Var y)))
      where y = fresh x (FreeVSubs δ (FreeV e - x))

{-
module Reduction where

  open import Subst
-}

{-

    data _∼_ : Expr -> Expr -> Set where
      var : {x : V} ->
          (Var x) ∼ (Var x)
      app : {e e' g g' : Expr} -> e ∼ e' -> g ∼ g' ->
          (App e g) ∼ (App e' g')
      lam : {e e' : Expr} {x x' y : V}  ->
          y ∈ (x :: FreeV e) ≟ false -> y ∈ (x' :: FreeV e') ≟ false ->
          e / (idd + (x, Var y)) ∼ e' / (idd + (x', Var y)) ->
          (Lamb x e) ∼ (Lamb x' e')
-}
    data _⟶_ : Expr -> Expr -> Set where
      β-reduction : {e e' : Expr} {x : V} ->
                  App (Lamb x e) e ⟶ (e / (idd + (x , e')))
  
