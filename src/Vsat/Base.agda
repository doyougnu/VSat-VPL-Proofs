------------------------------------------------------------------------
-- Variational Satisfiability Solver
--
--
-- Core algorithms and inference rules for Vsat
------------------------------------------------------------------------

module Vsat.Base where

open import Data.String using (String; _==_)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Bool using (Bool;true;false)

open import Utils.Base
open import Vpl.Base

------------------------------------------------------------------------
-------------------- Type Synonyms -------------------------------------
------------------------------------------------------------------------
Id : Set
Id = String

Dimension : Set
Dimension = String

Symbolic : Set
Symbolic = String

Reference : Set
Reference = String

-- | A configuration is a mapping of dimensions to booleans
Config : Set
Config = List (Dimension × Bool)

-- | Γ is the context representing the base solver. We simulate the base solver
-- | using a set of references. For any reference, r, if r ∈ Γ then r has been
-- | sent to the base solver. Note that we assume Γ processes references,
-- | symbolic references and literals
Γ : Set
Γ = List String

Δ : Set
Δ = List (Reference × Symbolic)

------------------------------------------------------------------------
------------------------ Symbolic Store Primitives ---------------------
------------------------------------------------------------------------

Δ-spawn : Δ → String → (Δ × Symbolic)
Δ-spawn store nm = (Δ' , nm)
  where
  new : String
  new = fresh nm

  Δ' : Δ
  Δ' = (nm , new) ∷ store

Δ-ref : Δ → Reference → Maybe Symbolic
-- Δ-ref store nm = get (_== nm)
-- use find and throw away the proof

-- | accumulation
-- data _↦_  : Context → Vpl → Set where
--   acc-gen : ∀ {}
