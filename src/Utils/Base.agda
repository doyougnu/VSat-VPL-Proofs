------------------------------------------------------------------------
-- Utilities
--
--
-- Utilities to ease working with contexts and product and other stuff
------------------------------------------------------------------------

module Utils.Base where

open import Data.String as S using (String; _++_)
open import Data.Bool using (Bool; if_then_else_;true;false)
open import Data.Product using (_×_; proj₁; proj₂;_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List as L using (List; _∷_; []; _++_)

-- Seems like the standard agda way to lookup an element is to use a setoid,
-- Any, and losing a witness. I'm not committed to it yet
get : {A : Set} → (A → Bool) → List A → Maybe A
get _ [] = nothing
get p (x ∷ xs) with p x
...            | true = just x
...            | false = get p xs

-- technically this should generate a UUID for each input, but for our purposes
-- we can just prepend an "s_" and move on
fresh : S.String → S.String
fresh name = "s_" S.++ name

names : ∀ {B : Set} → List (String × B) → List String
names = L.map proj₁

symbols : List (String × String) → List String
symbols = L.map proj₁

onSnd : ∀ {B : Set} → (B → B) → List (String × B) → List (String × B)
onSnd f = L.map (λ x → (proj₁ x , f (proj₂ x)))
