------------------------------------------------------------------------
-- Variational Satisfiability Solver
--
--
-- Language definition for IL and symbolics
------------------------------------------------------------------------

module Vsat.Lang where

open import Data.Product
open import Data.List
open import Data.String
open import Data.Bool

open import Vpl.Base
open import Utils.Base

------------------------------------------------------------------------
-------------------- Intemediate Lang ----------------------------------
------------------------------------------------------------------------
Dimension : Set
Dimension = String

Reference : Set
Reference = String

-- have to make a data type for symbolic in order to _unwind_ the variational
-- cores
data Symbolic : Set where
  sRef : String → Symbolic
  sLit : Bool   → Symbolic
  sNeg : Symbolic → Symbolic
  sOr  : Symbolic → Symbolic → Symbolic
  sAnd : Symbolic → Symbolic → Symbolic

data IL : Set where
  ●     : IL
  refIL : Reference → IL
  symIL : Symbolic  → IL
  litIL : Bool      → IL
  negIL : IL → IL
  andIL : IL → IL → IL
  orIL  : IL → IL → IL
  chcIL : String → Vpl → Vpl → IL

-- | A configuration is a mapping of dimensions to booleans
∁ : Set
∁ = List (Dimension × Bool)

-- | Γ is the context representing the base solver. We simulate the base solver
-- | using a set of references. For any reference, r, if r ∈ Γ then r has been
-- | sent to the base solver. Note that we assume Γ processes references,
-- | symbolic references and literals
Γ : Set
Γ = List String

-- | the symbolic store, we associate Reference with symbolics but will also use
-- | Symbolic × Symbolic when needed such as Δ-negate
Δ : Set
Δ = List (Reference × Symbolic)


-- | a context is a triple of the configuration, the symbolic store and the
-- | solver memory. In the paper we split the triple for each operation, so
-- | accumulation only knows about Δ and evaluation only knows about Δ | Γ. Here
-- | we include it everywhere for ease of proofs.
data Context : Set where
  ∅ : Context
  _||_||_⊢_ : ∁ → Γ → Δ → IL → Context

symNames : Context → List Reference
symNames ∅ = []
symNames (_ || _ || s ⊢ _) = names s


-- data _—↠_ : Context → Context → Set where
--   _∎ : ∀ M
--     ---------------
--     → M —↠ M

--   _—→⟨_⟩_ : ∀ L {M N}
--     → L ↣ M
--     → M —↠ N
--     ---------------
--     → L —↠ N
