------------------------------------------------------------------------
-- Variational Satisfiability Solver
--
--
-- Evaluation module, we mimick action in the solver with a list holding
-- references that are considered to be processed
------------------------------------------------------------------------

module Vsat.Evaluation where

open import Data.String using (String; _≈_; _==_; _≟_;_++_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_;subst;_≗_;cong)
open import Data.List using (List; _∷_; []; _++_;lookup;length;any)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-insert)
import Data.List.Relation.Unary.Any as A using (lookup)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Bool.Show using (show)
open import Function using (_$_;_∘_;id)
open import Data.Empty using (⊥;⊥-elim)
open import Relation.Nullary using (¬_)

import Data.List.Membership.DecPropositional as DecPropMembership

open import Utils.Base
open import Vpl.Base
open import Vsat.Lang
open import Vsat.Accumulation

open DecPropMembership _≟_
open import Data.List.Relation.Unary.Any using (here; there;Any)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)

--------------------------- Primitive Operations -------------------------------
Γ-assert : Context → Context
Γ-assert (∁ || Γ || Δ ⊢ (refIL nm))        = ∁ || nm ∷ Γ || Δ ⊢ ●
Γ-assert (∁ || Γ || Δ ⊢ (symIL (sRef nm))) = ∁ || nm ∷ Γ || Δ ⊢ ●
Γ-assert (∁ || Γ || Δ ⊢ (litIL nm))        = ∁ || (show nm) ∷ Γ || Δ ⊢ ●
Γ-assert s                                 = s


--------------------------- Evaluation Definition -----------------------------
infixl 2 _↣_

data _↣_  : Context → Context → Set where
  --------------- Computation Rules ------------------
  ev-unit : ∀ {∁ Γ Δ}
    → ∁ || Γ || Δ ⊢ ● ↣ ∁ || Γ || Δ ⊢ ●

  ev-term : ∀ {∁ Γ Δ t}
    ----------------
    → ∁ || Γ || Δ ⊢ (litIL t) ↣ Γ-assert (∁ || Γ || Δ ⊢ (litIL t))

  ev-sym : ∀ {∁ Γ Δ s}
    ----------------
    → ∁ || Γ || Δ ⊢ (symIL (sRef s)) ↣ Γ-assert (∁ || Γ || Δ ⊢ (symIL (sRef s)))

  ev-ref : ∀ {∁ Γ Δ r}
    ----------------
    → ∁ || Γ || Δ ⊢ (refIL r) ↣ Γ-assert (∁ || Γ || Δ ⊢ (refIL r))

  ev-chc : ∀ {∁ Γ Δ d l r}
    ----------------
    → ∁ || Γ || Δ ⊢ chcIL d l r ↣ ∁ || Γ || Δ ⊢ chcIL d l r

  ev-ul : ∀ {∁ Γ Δ r}
    ----------------
    → ∁ || Γ || Δ ⊢ andIL ● r ↣ ∁ || Γ || Δ ⊢ r

  ev-ur : ∀ {∁ Γ Δ l}
    ----------------
    → ∁ || Γ || Δ ⊢ andIL l ● ↣ ∁ || Γ || Δ ⊢ l

  --------------- Congruence Rules ------------------
  ev-neg : ∀ {∁ Γ Δ Δ′ v v′}
    → ∁ || Γ || Δ ⊢ negIL v ↦ ∁ || Γ || Δ′ ⊢ v′           -- notice accumulation arrow
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL v ↣ ∁ || Γ || Δ′ ⊢ v′

  ev-or : ∀ {∁ Γ Δ Δ₁ Δ₂ l l′ r r′}
    → ∁ || Γ || Δ  ⊢ l ↦ ∁ || Γ || Δ₁ ⊢ l′                -- notice accumulation arrow
    → ∁ || Γ || Δ₁ ⊢ r ↦ ∁ || Γ || Δ₂ ⊢ r′                -- notice accumulation arrow
    ----------------------
    → ∁ || Γ || Δ ⊢ orIL l r ↣ ∁ || Γ || Δ₂ ⊢ orIL l′ r′

  ev-and : ∀ {∁ Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ l l′ r r′}
    → ∁ || Γ || Δ  ⊢ l ↦ ∁ || Γ₁ || Δ₁ ⊢ l′              -- with ∧ we do not shift to accumulation
    → ∁ || Γ₁ || Δ₁ ⊢ r ↦ ∁ || Γ₂ || Δ₂ ⊢ r′
    ----------------------
    → ∁ || Γ || Δ ⊢ andIL l r ↣ ∁ || Γ₂ || Δ₂ ⊢ andIL l′ r′


---------------------- Reflexive Transitive Closure -----------------------------
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→e⟨_⟩_
infixr 2 _—→a⟨_⟩_
infix  3 _∎

data _—↠_ : Context → Context → Set where
  _∎ : ∀ M
    ---------------
    → M —↠ M

  _—→e⟨_⟩_ : ∀ L {M N}
    → L ↣ M
    → M —↠ N
    ---------------
    → L —↠ N

  _—→a⟨_⟩_ : ∀ L {M N}
    → L ↦ M
    → M —↠ N
    ---------------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
  ---------
  → M —↠ N
begin M—↠N = M—↠N

module ev-testing where

  _₁ : ∀ {∁ Γ Δ a}
    → ∁ || Γ || Δ ⊢ refIL a
    -- —↠ ∁ || s-neg a ∷ Γ || (s-neg a , sNeg (sRef (→sym a))) ∷ (a , sRef (→sym a)) ∷ Δ ⊢ ●
    —↠ ∁ || a ∷ Γ || Δ ⊢ ●
  _₁ {∁} {Γ} {Δ} {a} =
    begin
      (∁ || Γ || Δ ⊢ refIL a)
      —→e⟨ ev-ref ⟩
      ∁ || a ∷ Γ || Δ ⊢ ●
      ∎

  _₂ : ∀ {∁ Γ a}
    → ∁ || Γ || [] ⊢ negIL (refIL a)
    —↠ ∁ || s-neg (→sym a) ∷ Γ || (s-neg (→sym a) , sNeg (sRef (→sym a))) ∷ (a , sRef (→sym a)) ∷ [] ⊢ ●
  _₂ {∁} {Γ} {a} =
    begin
      ∁ || Γ || [] ⊢ negIL (refIL a)
      —→e⟨ ev-neg $ acc-neg (acc-gen λ())  ⟩
      ∁ || Γ || (a , sRef (→sym a)) ∷ [] ⊢ negIL (s-ref (→sym a))
      —→a⟨ acc-neg-s ⟩
      ∁ || Γ || (s-neg (→sym a) , sNeg (sRef (→sym a))) ∷ (a , sRef (→sym a)) ∷ [] ⊢ s-ref (s-neg (→sym a))
      —→e⟨ ev-sym  ⟩
      ∁ || s-neg (→sym a) ∷ Γ || (s-neg (→sym a) , sNeg (sRef (→sym a))) ∷ (a , sRef (→sym a)) ∷ [] ⊢ ●
      ∎
