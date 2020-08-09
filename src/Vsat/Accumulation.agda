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

--------------------------- Primitive Operations -------------------------------
Δ-spawn : Context → Context
Δ-spawn (∁ || Γ || store ⊢ (refIL nm)) = ∁ || Γ || Δ' ⊢ (symIL $ sRef nm)
  where
  new : Reference
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
Δ-negate (∁ || Γ || st ⊢ (negIL (symIL a@(sRef s)))) = ∁ || Γ || Δ′ ⊢ s-ref s′-ref
  where
  s′ : Symbolic
  s′ = sNeg a

  s′-ref : Reference
  s′-ref = s-neg s

  s′∈Δ : Bool
  s′∈Δ = any (s′-ref ==_) $ names st

  Δ′ : Δ
  Δ′ = if s′∈Δ then st else (s′-ref , s′) ∷ st

Δ-negate st = st

Δ-or : Context → Context
Δ-or (∁ || Γ || st ⊢ orIL (symIL l@(sRef s₁)) (symIL r@(sRef s₂))) = ∁ || Γ || Δ′ ⊢ s-ref sref
  where
  sref : Reference
  sref =  s-or s₁ s₂

  s : Symbolic
  s = sOr l r

  -- s∈Δ : Bool
  -- s∈Δ = any (s-ref ==_) $ names st

  Δ′ : Δ
  -- Δ′ = if s∈Δ then st else (s-ref , s) ∷ st
  Δ′ = (sref , s) ∷ st
Δ-or st = st

Δ-and : Context → Context
Δ-and (∁ || Γ || st ⊢ andIL (symIL l@(sRef s₁)) (symIL r@(sRef s₂))) = ∁ || Γ || Δ′ ⊢ s-ref sref
  where
  sref : Reference
  sref = s-and s₁ s₂

  s : Symbolic
  s = sAnd l r

  s∈Δ : Bool
  s∈Δ = any (sref ==_) $ names st

  Δ′ : Δ
  Δ′ = if s∈Δ then st else (sref , s) ∷ st
Δ-and st = st


--------------------------- Accumulation Definition -----------------------------
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

  acc-neg-s : ∀ {∁ Γ Δ s}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (symIL s) ↦ Δ-negate (∁ || Γ || Δ ⊢ negIL (symIL s))

  acc-c : ∀ {∁ Γ Δ d l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ chcIL d l r ↦ ∁ || Γ || Δ ⊢ chcIL d l r

  acc-neg-c : ∀ {∁ Γ Δ d l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (chcIL d l r) ↦ ∁ || Γ || Δ ⊢ chcIL d (vNeg l) (vNeg r) -- notice negation is translated back to VPL

  acc-sor : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ orIL (s-ref l) (s-ref r) ↦  Δ-or (∁ || Γ || Δ ⊢ orIL (s-ref l) (s-ref r))

  acc-sand : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ andIL (symIL l) (symIL r) ↦ Δ-and (∁ || Γ || Δ ⊢ andIL (symIL l) (symIL r))

--------------- Congruence Rules ------------------
  acc-dm-or : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (orIL l r) ↦  ∁ || Γ || Δ ⊢ andIL (negIL l) (negIL r)

  acc-dm-and : ∀ {∁ Γ Δ l r}
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL (andIL l r) ↦  ∁ || Γ || Δ ⊢ orIL (negIL l) (negIL r)

  acc-neg : ∀ {∁ Γ Δ Δ₁ Δ₂ v v′}
    → ∁ || Γ || Δ  ⊢ v ↦ ∁ || Γ || Δ₁ ⊢ v′
    ----------------------
    → ∁ || Γ || Δ ⊢ negIL v ↦ ∁ || Γ || Δ₂ ⊢ negIL v′

  acc-vor : ∀ {∁ Γ Δ Δ₁ Δ₂ l r l′ r′}
    → ∁ || Γ || Δ  ⊢ l ↦ ∁ || Γ || Δ₁ ⊢ l′
    → ∁ || Γ || Δ₁ ⊢ r ↦ ∁ || Γ || Δ₂ ⊢ r′
    ----------------------
    → ∁ || Γ || Δ ⊢ orIL l r ↦ ∁ || Γ || Δ₂ ⊢ orIL l′ r′

  acc-vand : ∀ {∁ Γ Δ Δ₁ Δ₂ l r l′ r′}
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
    ↦ ∁ || Γ || ("s_¬a" , sNeg (sRef "a")) ∷ ("b", sRef "b") ∷ ("a" , sRef "a") ∷ [] ⊢ orIL (symIL (sRef "s_¬a")) (symIL (sRef "b"))
  _₁ = acc-vor acc-neg-s acc-sym

  _₂ : ∀ {∁ Γ}
    →  ∁ || Γ || [] ⊢ orIL (symIL (sRef "a")) (symIL (sRef "b"))
    ↦ ∁ || Γ || ("s_a∨b" , sOr (sRef "a") (sRef "b")) ∷ [] ⊢ s-ref (s-or "a" "b")
  _₂ = acc-sor

  _ₙ : ∀ {∁ Γ}
    →  ∁ || Γ || [] ⊢ negIL (refIL "a")
    ↦ ∁ || Γ || ("a" , sRef "a") ∷ [] ⊢ negIL (symIL (sRef "a"))
    → ∁ || Γ || ("a" , sRef "a") ∷ [] ⊢ negIL (symIL (sRef "a"))
    ↦ ∁ || Γ || ("s_¬a" , sNeg (sRef "a")) ∷ ("a" , sRef "a") ∷ [] ⊢ s-ref "s_¬a"
  _ₙ a = acc-neg-s

  _₃ : ∀ {∁ Γ Δ Δ₁ Δ₂ Δ₃ a a′ a′′ b b′}
    → ∁ || Γ || Δ ⊢ orIL (negIL (refIL a)) (refIL b)
    ↦ ∁ || Γ || Δ₁ ⊢ orIL (negIL (refIL a)) (s-ref b′)

    → ∁ || Γ || Δ₁ ⊢ orIL (negIL (refIL a)) (s-ref b′)
    ↦ ∁ || Γ || Δ₂ ⊢ orIL (negIL (s-ref a′)) (s-ref b′)

    → ∁ || Γ || Δ₂ ⊢ orIL (negIL (s-ref a′)) (s-ref b′)
    ↦ ∁ || Γ || Δ₃ ⊢ orIL (s-ref a′′) (s-ref b′)

    → ∁ || Γ || Δ₃ ⊢ orIL (s-ref a′′) (s-ref b′)
    ↦ ∁ || Γ || (s-or a′′ b′ , sOr (sRef a′′) (sRef b′)) ∷ Δ₃ ⊢ s-ref (s-or a′′ b′)
  _₃ a b c = acc-sor

  x  : ∀ {∁ Γ Δ a b}
     → ∁ || Γ || Δ ⊢ orIL (s-ref a) (s-ref b)
     ↦ ∁ || Γ || (s-or a b , sOr (sRef a) (sRef b)) ∷ Δ ⊢ s-ref (s-or a b)
  x = acc-sor

  _₄ : ∀ {∁ Γ} → ∁ || Γ || [] ⊢ refIL "a" ↦ ∁ || Γ || ("a" , sRef "s_a") ∷ [] ⊢ symIL (sRef "a")
  _₄ = acc-gen λ ()

  _₅ : ∀ {∁ Γ}
    → ∁ || Γ || ("b" , sRef "s_b") ∷ [] ⊢ refIL "a"
    ↦ ∁ || Γ || ("a" , sRef "s_a") ∷ ("b" , sRef "s_b") ∷ [] ⊢ symIL (sRef "a")
  _₅ = acc-gen go
    where go : "a" ∉ names (("b", sRef "s_b") ∷ [])
          go (here ())
          go (there ())
