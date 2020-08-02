------------------------------------------------------------------------
-- Variational Propositional Logic
--
--
-- The type for vpl and configuration definitions. We choose a deep embedding to
-- stay close to haskell and for well-defined configuration semantics
------------------------------------------------------------------------

module Vpl.Base where

open import Data.Bool using (Bool; if_then_else_;true;false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.String using (String; _==_)
open import Data.Nat as ℕ using (ℕ; suc; _+_; zero)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List as L using (List; _∷_; []; _++_)

data Vpl : Set where
  vLit  : Bool   → Vpl
  vRef  : String → Vpl
  vNeg  : Vpl    → Vpl
  vAnd  : Vpl → Vpl → Vpl
  vOr   : Vpl → Vpl → Vpl
  chc  : String → Vpl → Vpl → Vpl

-- | Count the non-unique dimensions
dimCount : Vpl → ℕ.ℕ
dimCount (chc d l r) = suc (dimCount l + dimCount r)
dimCount (vAnd l r)  = dimCount l + dimCount r
dimCount (vOr l r)   = dimCount l + dimCount r
dimCount (vNeg e)    = dimCount e
dimCount _           = zero

-- | A projection from a vpl formula to a vector of dimensions
dimensions : Vpl → List String
dimensions (chc d l r) = d L.∷ dimensions l L.++ dimensions r
dimensions (vAnd  l r) = dimensions l L.++ dimensions r
dimensions (vOr   l r) = dimensions l L.++ dimensions r
dimensions (vNeg  s)   = dimensions s
dimensions (vLit _)    = L.[]
dimensions (vRef _)    = L.[]

names : List (String × Bool) → List String
names = L.map proj₁

-- Seems like the standard agda way to lookup an element is to use a setoid,
-- Any, and losing a witness. I'm not committed to it yet
get : {A : Set} → (A → Bool) → List A → Maybe A
get _ [] = nothing
get p (x ∷ xs) with p x
...            | true = just x
...            | false = get p xs

-- | Configuration of a vpl formula, if ∃ dimension ∈ (f : Vpl) s.t. dimension ∉
-- | Configuration then the choice is preserved
configure : List (String × Bool) → Vpl → Vpl
-- computation rule
configure conf (chc dim l r) with get (λ x → (proj₁ x) == dim) conf
...                          | nothing        = (chc dim (configure conf l) (configure conf r))
...                          | just selection = if proj₂ selection
                                                then configure conf l
                                                else configure conf r
-- congruence rules
configure c (vAnd l r) = vAnd (configure c l) (configure c r)
configure c (vOr l r)  = vOr (configure c l) (configure c r)
configure _ x = x
