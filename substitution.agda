module substitution  where



open import lambda
open import Data.String
open import Data.Product
open import Data.Bool
open import Relation.Binary.Core
open import Data.Empty

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
    FreeVSubs δ (x :: xs) = FreeVList (δ x) +++ FreeVSubs δ xs
    
    _/_ : Expr -> Δ -> Expr
    Var v / δ = δ v
    (App e e') / δ = App (e / δ) (e' / δ)
    (Lamb x e) / δ = Lamb y (e / (δ + (x , Var y)))
      where y = fresh x (FreeVSubs δ (FreeVList e - x))

{-
module Reduction where

  open import Subst
-}



    data _∼_ : Expr -> Expr -> Set where
      var : {x : V} ->
          (Var x) ∼ (Var x)
      app : {e e' g g' : Expr} -> e ∼ e' -> g ∼ g' ->
          (App e g) ∼ (App e' g')
      lam : {e e' : Expr} {x x' y : V} ->
            (y FreeV (Lamb x e) -> ⊥) -> (y FreeV (Lamb x' e') -> ⊥) ->
            (e / (idd + (x , Var y))) ∼ (e' / (idd + (x' , Var y))) ->
            (Lamb x e) ∼ (Lamb x' e')

{-
      lam : {e e' : Expr} {x x' y : V}  ->
           y ∈ (x :: FreeV e) ≡ false -> y ∈ (x' :: FreeV e') ≡ false ->
           (e / (idd + (x , Var y))) ∼ (e' / (idd + (x' , Var y))) ->
           (Lamb x e) ∼ (Lamb x' e')
-}

{-⊥   bot ℙt -}

    data _⟶_ : Expr -> Expr -> Set where
      β-reduction : {e e' : Expr} {x : V} ->
                   App (Lamb x e) e' ⟶ (e / (idd + (x , e')))
      Renaming    : {e₀ e₁ e₁' : Expr} ->
                    e₀ ⟶ e₁ ->
                    e₁ ∼ e₁' ->
                    e₀ ⟶ e₁'
      Ctx_AppL    : {e₀ e₁ e : Expr} -> e₀ ⟶ e₁ ->
                   App e₀ e ⟶ App e₁ e
      Ctx_AppR    : {e₀ e₁ e : Expr} -> e₀ ⟶ e₁ ->
                   App e e₀ ⟶ App e e₁
      Ctx_Lamb    : {e₀ e₁ : Expr} {x : V} -> e₀ ⟶ e₁ ->
                    Lamb x e₀ ⟶ Lamb x e₁
      

    data _⟶*_ : Expr -> Expr -> Set where
      Reflex  : {e₀ e₁ : Expr} ->
               e₀ ∼ e₁ ->
               e₀ ⟶* e₁
      Transit : {e₀ e₁ e₂ : Expr} ->
                e₀ ⟶* e₁ ->
                e₁ ⟶* e₂ ->
                e₀ ⟶* e₂
      CBase   : {e₀ e₁ : Expr} ->
                e₀ ⟶ e₁ ->
                e₀ ⟶* e₁
      
    ex1 : {y : V} -> (Var y) ⟶* (Var y)
    ex1 = Reflex (var)

{-
    ex2 : {x y z : V} -> (App (Lamb x (Var y)) (Lamb z (Var z))) ⟶* Var y
    ex2 = CBase {!β-reduction!}
-}

    ex2 : {x y z : V} -> (App (Lamb x (Var y)) (Lamb z (Var z))) ⟶ Var y
    ex2 = {!β-reduction !}

