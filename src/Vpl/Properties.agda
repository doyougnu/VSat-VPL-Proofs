------------------------------------------------------------------------
-- Properties of Variational Propositional Logic
--
--
-- Module to proove properties of vpl
------------------------------------------------------------------------

module Vpl.Properties where

import Data.List.Membership.DecPropositional as DecPropMembership
import Data.List.Relation.Binary.Subset.Propositional as Sub
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.String using (String; _≈_; _==_; _≟_)
open import Data.List as L using (List; _∷_; []; _++_; take)
open import Data.Product
open import Data.Sum
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; if_then_else_;true;false; _∧_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using ()
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open DecPropMembership _≟_
open Sub using (_⊆_)

open import Vpl.Base
open import C2.Base

------------------------------------------------------------------------
-------------------- Total/Partial Configurations ----------------------
------------------------------------------------------------------------

data Total : Vpl → List (String × Bool) → Set where
  istotal : ∀ {v : Vpl} {conf : List (String × Bool)}
    → (dimensions v) ⊆ (names conf)
    ------------------------------
    → Total v conf

data Partial : Vpl → List (String × Bool) → Set where
  isPartial : ∀ {v : Vpl} {conf : List (String × Bool)}
    → ¬ (Total v conf)
    ------------------------------
    → Partial v conf

test : Vpl
test = vAnd (chc "A" (vRef "a") (vRef "b")) (vRef "c")

c : List (String × Bool)
c = ("B", false) L.∷ ("A", true) L.∷ L.[]

lem₁ : Total test c
lem₁ = istotal λ p → there (∈-++⁺ˡ p)

------------------------------------------------------------------------
-------------------- Plain or Variational Formulas----------------------
------------------------------------------------------------------------
data plain_ : Vpl → Set where
 pl-t : ∀ {b : Bool } → plain (vLit b)
 pl-r : ∀ {s : String} → plain (vRef s)

 pl-neg : ∀ {v : Vpl}
         → plain v
         --------------
         → plain (vNeg v)

 pl-or  : ∀ {v₁ v₂ : Vpl}
         → plain v₁ → plain v₂
         -----------------
         → plain (vOr v₁ v₂)

 pl-and : ∀ {v₁ v₂ : Vpl}
           → plain v₁ → plain v₂
           -----------------
           → plain (vAnd v₁ v₂)

chc¬plain : ∀ {v₁ v₂ : Vpl} {d : String} → ¬ (plain (chc d v₁ v₂))
chc¬plain ()

neg¬plain : ∀ {v : Vpl} → ¬ (plain v) → ¬ (plain vNeg v)
neg¬plain ¬f (pl-neg v) = ¬f v

or¬plain : ∀ {l r : Vpl} → ¬ (plain l) ⊎ ¬ (plain r) → ¬ plain (vOr l r)
or¬plain (inj₁ ¬l) (pl-or l r) = ¬l l
or¬plain (inj₂ ¬r) (pl-or l r) = ¬r r

and¬plain : ∀ {l r : Vpl} → ¬ (plain l) ⊎ ¬ (plain r) → ¬ plain (vAnd l r)
and¬plain (inj₁ ¬l) (pl-and l r) = ¬l l
and¬plain (inj₂ ¬r) (pl-and l r) = ¬r r

plain? : ∀ (v : Vpl) → Dec (plain v)
plain? (vLit x)      = yes pl-t
plain? (vRef x)      = yes pl-r
plain? (vNeg x) with plain? x
...                | yes a = yes (pl-neg a)
...                | no ¬a = no (neg¬plain ¬a)
plain? (vOr l r) with plain? l | plain? r
-- writing the redundant cases to appease agda-mode
...                 | no p     | no _     = no (or¬plain (inj₁ p))
...                 | no p     | yes _    = no (or¬plain (inj₁ p))
...                 | yes _    | no p     = no (or¬plain (inj₂ p))
...                 | yes l₁   | yes r₁   = yes (pl-or l₁ r₁)
plain? (vAnd l r) with plain? l | plain? r
...                 | no p     | no _     = no (and¬plain (inj₁ p))
...                 | no p     | yes _    = no (and¬plain (inj₁ p))
...                 | yes _    | no p     = no (and¬plain (inj₂ p))
...                 | yes l₁   | yes r₁   = yes (pl-and l₁ r₁)
plain? (chc d l r) = no chc¬plain

------------------------------------------------------------------------
-------------------- VPL embeds C₂ -------------------------------------
------------------------------------------------------------------------
-- TODO: not sure this is needed for proofs
-- open import Relation.Binary.Embedding.Base

-- vpl≲C₂ : ∀ {c : C₂} {v : Vpl} → {!!}
-- vpl≲C₂ {c} {v} =
--   record
--   { to = {!!}
--   ; from = {!!}
--   ; from∘to = {!!}
--   }

------------------------------------------------------------------------
-------------------- VPL is Variation Preserving -----------------------
------------------------------------------------------------------------
-- A function is variation preseving if `∀ {v : Vpl} {c : List (String × Bool)}, {f : C₂ →
-- [B]} {g : Vpl → B₁}, where B₁ is a variational result of g` the following
-- holds `map f ∘ configure c v ≡ configure c ∘ g v` or as a diagram

-- v  --- configure c ---→ List B
-- |                        |
-- |                        |
-- g                        map f
-- |                        |
-- |                        |
-- ↓                        ↓
-- B₁ --- configure c ---→ [C]

-- infix 3 v-preserving
-- record v-preserving_
--   (v : Vpl)
--   (c : List (String × Bool))
--   (B C B₁ : Set)
--   : Set where
--   field
--     to-plain : B → C
--     to-var   : ∀ (v : Vpl) → B₁
--     preseves : ∀ {v : Vpl} {c : List (String × Bool)} → configure c ∘ to-var ≡ to-plain ∘ configure c
-- open v-preserving_
