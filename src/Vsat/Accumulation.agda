------------------------------------------------------------------------
-- Variational Satisfiability Solver
--
--
-- Accumulation module, we mimick action in the symbolic store with a Symbolic
-- datatype and a context
------------------------------------------------------------------------

module Vsat.Accumulation where

open import Data.String using (String; _≈_; _==_; _≟_;_++_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_;subst;_≗_;cong)
open import Data.List using (List; _∷_; []; _++_;lookup;length;any)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-insert)
import Data.List.Relation.Unary.Any as A using (lookup)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Bool using (Bool;true;false;T;if_then_else_)
open import Function using (_$_;_∘_;id)
open import Data.Empty using (⊥;⊥-elim)
open import Relation.Nullary using (¬_)

import Data.List.Membership.DecPropositional as DecPropMembership

open import Utils.Base
open import Vpl.Base
open import Vsat.Lang

open DecPropMembership _≟_
open import Data.List.Relation.Unary.Any using (here; there;Any)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)

Δ-spawn : Context → Context
Δ-spawn (∁ || Γ || store ⊢ (refIL nm)) = ∁ || Γ || Δ' ⊢ (symIL $ sRef nm)
  where
  new : String
  new = fresh nm

  Δ' : Δ
  Δ' = (nm , sRef new) ∷ store
Δ-spawn s = s

Δ-ref : ∀ {store : Context} {name : Reference} → { name∈store : True (name ∈? symNames store) } → Context
Δ-ref {∁ || Γ || b ⊢ a} {name∈store = name∈store} = ∁ || Γ || b ⊢ (symIL ∘ sRef ∘ A.lookup ∘ toWitness $ name∈store)

-- | to negate a symbol we lookup the symbol and negate it in the store,
-- | possible creating a new symbolic reference if needed
Δ-negate : Context → Context
Δ-negate ∅ = ∅
Δ-negate (∁ || Γ || st ⊢ (negIL (symIL a@(sRef s)))) = ∁ || Γ || Δ′ ⊢ (symIL ∘ sRef $ s′-ref)
  where
  s′ : Symbolic
  s′ = sNeg a

  s′-ref : Reference
  s′-ref = "¬" Data.String.++ s

  s′∈Δ : Bool
  s′∈Δ = any (s′-ref ==_) $ names st

  Δ′ : Δ
  Δ′ = if s′∈Δ then st else (s′-ref , s′) ∷ st

Δ-negate st = st

Δ-or : Context → Context
Δ-or (∁ || Γ || st ⊢ orIL (symIL l@(sRef s₁)) (symIL r@(sRef s₂))) = ∁ || Γ || Δ′ ⊢ symIL s
  where
  s-ref : Reference
  s-ref =  s₁ Data.String.++ "∨" Data.String.++ s₂

  s : Symbolic
  s = sOr l r

  s∈Δ : Bool
  s∈Δ = any (s-ref ==_) $ names st

  Δ′ : Δ
  Δ′ = if s∈Δ then st else (s-ref , s) ∷ st
Δ-or st = st

Δ-and : Context → Context
Δ-and (∁ || Γ || st ⊢ andIL (symIL l@(sRef s₁)) (symIL r@(sRef s₂))) = ∁ || Γ || Δ′ ⊢ symIL s
  where
  s-ref : Reference
  s-ref =  s₁ Data.String.++ "∨" Data.String.++ s₂

  s : Symbolic
  s = sAnd l r

  s∈Δ : Bool
  s∈Δ = any (s-ref ==_) $ names st

  Δ′ : Δ
  Δ′ = if s∈Δ then st else (s-ref , s) ∷ st
Δ-and st = st

-- | accumulation
infixl 5 _↦_

data _↦_  : Context → Context → Set where
--------------- Computation Rules ------------------
  acc-unit : ∀ {∁ Γ Δ}
    ----------------
    → ∁ || Γ || Δ ⊢ ● ↦ ∁ || Γ || Δ ⊢ ●

  acc-sym : ∀ {∁ Γ Δ s}
    ----------------
    → ∁ || Γ || Δ ⊢ symIL s ↦ ∁ || Γ || Δ ⊢ symIL s

  acc-gen : ∀ {∁ Γ Δ r}
    → r ∉ (names Δ)
    ----------------------
    → ∁ || Γ || Δ ⊢ refIL r ↦ Δ-spawn (∁ || Γ || Δ ⊢ refIL r)

  acc-ref : ∀ {∁ Γ Δ}  {r : Reference}
    → { name∈store : True (r ∈? (names Δ)) }
    ---------------------
    → ∁ || Γ || Δ ⊢ refIL r ↦ Δ-ref {∁ || Γ || Δ ⊢ refIL r} {r} {name∈store}

  acc-neg : ∀ {∁ Γ Δ s}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (symIL s) ↦ Δ-negate (∁ || Γ || Δ ⊢ negIL (symIL s))

  acc-C : ∀ {∁ Γ Δ d l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ chcIL d l r ↦ ∁ || Γ || Δ ⊢ chcIL d l r

  acc-Neg-C : ∀ {∁ Γ Δ d l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (chcIL d l r) ↦ ∁ || Γ || Δ ⊢ chcIL d (vNeg l) (vNeg r) -- notice negation is translated back to VPL

  acc-SOr : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ orIL (symIL l) (symIL r) ↦  Δ-or (∁ || Γ || Δ ⊢ orIL (symIL l) (symIL r))

  acc-SAnd : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ andIL (symIL l) (symIL r) ↦ Δ-and (∁ || Γ || Δ ⊢ andIL (symIL l) (symIL r))

--------------- Congruence Rules ------------------
  acc-DM-Or : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (orIL l r) ↦  ∁ || Γ || Δ ⊢ andIL (negIL l) (negIL r)

  acc-DM-And : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (andIL l r) ↦  ∁ || Γ || Δ ⊢ orIL (negIL l) (negIL r)

  acc-VOr : ∀ {∁ Γ Δ Δ₁ Δ₂ l r l′ r′}
    → ∁ || Γ || Δ  ⊢ l ↦ ∁ || Γ || Δ₁ ⊢ l′
    → ∁ || Γ || Δ₁ ⊢ r ↦ ∁ || Γ || Δ₂ ⊢ r′
    ----------------------
    → ∁ || Γ || Δ ⊢ orIL l r ↦ ∁ || Γ || Δ₂ ⊢ orIL l′ r′

  acc-VAnd : ∀ {∁ Γ Δ Δ₁ Δ₂ l r l′ r′}
    → ∁ || Γ || Δ  ⊢ l ↦ ∁ || Γ || Δ₁ ⊢ l′
    → ∁ || Γ || Δ₁ ⊢ r ↦ ∁ || Γ || Δ₂ ⊢ r′
    ----------------------
    → ∁ || Γ || Δ ⊢ andIL l r ↦ ∁ || Γ || Δ₂ ⊢ andIL l′ r′

module ↦-properties where
  Δ-cong : ∀ {Δ₁ Δ₂ : Δ} (f : Δ → Δ) →  Δ₁ ≡ Δ₂ → f Δ₁ ≡ f Δ₂
  Δ-cong f Δ₁≡Δ₂ = cong f Δ₁≡Δ₂

  cong-acc-ctx : ∀ {a b : (Δ × IL)} (f : (Δ × IL) → (Δ × IL)) → a ≡ b → f a ≡ f b
  cong-acc-ctx f a≡b = cong f a≡b

  -- TODO: ↦ should be congruent

module acc-testing where
  _₁ : ∀ {∁ Γ}
    → ∁ || Γ || ("b", sRef "b") ∷ ("a" , sRef "a") ∷ [] ⊢ orIL (negIL (symIL (sRef "a"))) (symIL (sRef "b"))
    ↦ ∁ || Γ || ("¬a" , sNeg (sRef "a")) ∷ ("b", sRef "b") ∷ ("a" , sRef "a") ∷ [] ⊢ orIL (symIL (sRef "¬a")) (symIL (sRef "b"))
  _₁ = acc-VOr acc-neg acc-sym

  _₂ : ∀ {∁ Γ}
    →  ∁ || Γ || [] ⊢ orIL (symIL (sRef "a")) (symIL (sRef "b"))
     ↦ ∁ || Γ || ("a∨b" , sOr (sRef "a") (sRef "b")) ∷ [] ⊢ symIL (sOr (sRef "a") (sRef "b"))
  _₂ = acc-SOr

  -- _₃ : ([] , refIL "a") ↦ (("a" , sRef "s_a") ∷ [] , symIL (sRef "a"))
  --    → ([] , refIL "b") ↦ (("b" , sRef "s_b") ∷ [] , symIL (sRef "b"))
  --   ------------------------------------------------------
  --   → ([] , orIL (negIL (refIL "a")) (refIL "b"))
  --   ↦ (("a" , sRef "s_a") ∷ ("b", sRef "s_b") ∷ [] , orIL (negIL (symIL (sRef "a"))) (symIL (sRef "b")))
     -- → ([] , orIL (negIL (symIL (sRef "a"))) (symIL (sRef "b")))
     -- ↦ (("¬a" , sNeg (sRef "a")) ∷ [] , orIL (symIL (sRef "¬a")) (symIL (sRef "b")))
  -- _₃ a b = acc-VOr {!!} (↦-properties.Δ-cong (∈-insert ("a" , sRef "s_a") ∷ []) b)
  -- _₃ a b = acc-VOr {!!} {!!}

  _₄ : ∀ {∁ Γ} → ∁ || Γ || [] ⊢ refIL "a" ↦ ∁ || Γ || ("a" , sRef "s_a") ∷ [] ⊢ symIL (sRef "a")
  _₄ = acc-gen λ ()

  _₅ : ∀ {∁ Γ}
    → ∁ || Γ || ("b" , sRef "s_b") ∷ [] ⊢ refIL "a"
    ↦ ∁ || Γ || ("a" , sRef "s_a") ∷ ("b" , sRef "s_b") ∷ [] ⊢ symIL (sRef "a")
  _₅ = acc-gen go
    where go : "a" ∉ names (("b", sRef "s_b") ∷ [])
          go (here ())
          go (there ())
