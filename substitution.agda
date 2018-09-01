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
      CtxAppL    : {e₀ e₁ e : Expr} -> e₀ ⟶ e₁ ->
                   App e₀ e ⟶ App e₁ e
      CtxAppR    : {e₀ e₁ e : Expr} -> e₀ ⟶ e₁ ->
                   App e e₀ ⟶ App e e₁
      CtxLamb    : {e₀ e₁ : Expr} {x : V} -> e₀ ⟶ e₁ ->
                    Lamb x e₀ ⟶ Lamb x e₁
      

    data _⟶*_ : Expr -> Expr -> Set where
      Reflex  : {e₀ e₁ : Expr} ->
               (p : e₀ ∼ e₁) ->
               e₀ ⟶* e₁
      Transit : {e₀ e₁ e₂ : Expr} ->
                e₀ ⟶* e₁ ->
                e₁ ⟶* e₂ ->
                e₀ ⟶* e₂
      CBase   : {e₀ e₁ : Expr} ->
                e₀ ⟶ e₁ ->
                e₀ ⟶* e₁

    data _⇉_ : Expr -> Expr -> Set where
      Var     : {x : V} ->
                Var x ⇉ Var x
      Appl    : {M M' N N' : Expr} ->
                M ⇉ M' -> N ⇉ N' ->
               App M N ⇉ App M' N'
      Lamb    : {M M' : Expr} {x : V} ->
                M ⇉ M' ->
                Lamb x M ⇉ Lamb x M'
      AppLamb : {M M' N N' : Expr} {x : V} ->
                M ⇉ M' -> N ⇉ N' ->
                App (Lamb x M) N ⇉ (M' / (idd + (x , N')))
      Equiv   : {M M' M'' : Expr} ->
                M ⇉ M' -> M' ∼ M'' ->
                M ⇉ M''

    data _⇉₀_ : Expr -> Expr -> Set where
      Var     : {x : V} ->
                Var x ⇉₀ Var x
      Appl    : {M M' N N' : Expr} ->
                M ⇉₀ M' -> N ⇉₀ N' ->
                App M N ⇉₀ App M' N'
      Lamb    : {M M' : Expr} {x : V} ->
                M ⇉₀ M' ->
                Lamb x M ⇉₀ Lamb x M'
      AppLamb : {M M' N N' : Expr} {x : V} ->
                M ⇉₀ M' -> N ⇉₀ N' ->
                App (Lamb x M) N ⇉₀ (M' / (idd + (x , N')))


    --lemma9 : {e e' : Expr} {x : V} -> e ⟶* e' -> x FreeV e' -> x FreeV e
    --lemma9 = {!!}

    open import Relation.Binary
    open import Relation.Unary
    open import Data.Product

    EquivProp : (M : Expr) → M ∼ M
    EquivProp M = {!!}


    lemmaAbs⟶* :  ∀ {M M' x} → M ⟶* M' → Lamb x M ⟶* Lamb x M'
    lemmaAbs⟶* (Reflex p) = CBase (CtxLamb {!!})
    lemmaAbs⟶* (Transit p p₁) = Transit (lemmaAbs⟶* p) (lemmaAbs⟶* p₁)
    lemmaAbs⟶* (CBase x₁) = CBase (CtxLamb x₁)

    lemmaApp⟶* : ∀ {M M' N N'} → M ⟶* M' → N ⟶* N' → App M N ⟶* App M' N'
    lemmaApp⟶* p₁ p₂ = {!!}

{- INTENTE CON ESTO, PERO A MEDIDA QUE FUI AVANZANDO PENSE QUE NO ERA EL CAMINO
    lemmaAppLamb⟶* : ∀ {M M' N N' x} → M ⟶* M' → N ⟶* N' → App (Lamb x M) N ⟶* (M' / (idd + (x , N')))
    lemmaAppLamb⟶* (Reflex p) (Reflex p₁) = {!!}
    lemmaAppLamb⟶* (Reflex p) (Transit p₂ p₃) = {!!}
    lemmaAppLamb⟶* (Reflex p) (CBase x₁) = {!!} 
    lemmaAppLamb⟶* (Transit {M} {e} {M'} p₁ p₃) (Reflex p) = {!!}
    lemmaAppLamb⟶* (Transit p₁ p₃) (Transit p₂ p₄) = {!!}
    lemmaAppLamb⟶* (Transit p₁ p₃) (CBase x₁) = {!!}
    lemmaAppLamb⟶* (CBase x₁) (Reflex p) = {!!}
    lemmaAppLamb⟶* (CBase x₁) (Transit p₂ p₃) = {!!}
    lemmaAppLamb⟶* (CBase x₁) (CBase x₂) = {!!} 
-}
    ⇉⊆⟶* : {M N : Expr} -> M ⇉ N -> M ⟶* N
    ⇉⊆⟶* Var = Reflex var
    ⇉⊆⟶* (Appl {M} {M'} {N} {N'} M⇉M' N⇉N') = lemmaApp⟶* (⇉⊆⟶* M⇉M') (⇉⊆⟶* N⇉N')
    ⇉⊆⟶* (Lamb {M} {M'} {x} M⇉M') = lemmaAbs⟶* (⇉⊆⟶* M⇉M')
    ⇉⊆⟶* (AppLamb {M} {M'} {N} {N'} {x} M⇉M' N⇉N') = {!!}
    ⇉⊆⟶* (Equiv {M} {M'} {M''} M⇉M' M'∼M'') = Transit (⇉⊆⟶* M⇉M') (Reflex M'∼M'')
