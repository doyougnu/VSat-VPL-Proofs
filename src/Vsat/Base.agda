------------------------------------------------------------------------
-- Variational Satisfiability Solver
--
--
-- Core algorithms and inference rules for Vsat
------------------------------------------------------------------------

module Vsat.Base where

-- open import Data.String using (String; _≈_; _==_; _≟_;_++_)
-- open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_;subst;_≗_;cong)
-- open import Data.List using (List; _∷_; []; _++_;lookup;length;any)
-- open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-insert)
-- import Data.List.Relation.Unary.Any as A using (lookup)
-- open import Data.Product using (_×_; proj₁; proj₂; _,_)
-- open import Data.Bool using (Bool;true;false;T;if_then_else_)
-- open import Function using (_$_;_∘_;id)
-- open import Data.Empty using (⊥;⊥-elim)
-- open import Relation.Nullary using (¬_)

-- import Data.List.Membership.DecPropositional as DecPropMembership

-- open import Utils.Base
-- open import Vpl.Base

------------------------------------------------------------------------
------------------------ Symbolic Store Primitives ---------------------
------------------------------------------------------------------------
