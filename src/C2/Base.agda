------------------------------------------------------------------------
-- Classic propositional logic
--
--
------------------------------------------------------------------------

module C2.Base where

open import Data.Bool
open import Data.String

data C₂ : Set where
  cLit   : Bool → C₂
  cRef   : String → C₂
  cNeg   : C₂ → C₂
  cAnd   : C₂ → C₂ → C₂
  cOr    : C₂ → C₂ → C₂
