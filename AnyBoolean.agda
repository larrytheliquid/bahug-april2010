module AnyBoolean where
open import Data.Bool
open import Data.Nat
open import Data.List hiding (any)
open import Relation.Binary.PropositionalEquality

any : {A : Set} → (A → Bool) → List A → Bool
any _ [] = false
any p (x ∷ xs) with p x
... | true = true
... | false = any p xs

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

test-any-even-true : 
  any even (7 ∷ 22 ∷ 39 ∷ []) ≡ true
test-any-even-true = refl

test-any-even-false : 
  any even (7 ∷ 23 ∷ 39 ∷ []) ≡ false
test-any-even-false = refl

test-any-odd-true : 
  any odd (8 ∷ 23 ∷ 40 ∷ []) ≡ true
test-any-odd-true = refl

test-any-odd-false : 
  any odd (8 ∷ 22 ∷ 40 ∷ []) ≡ false
test-any-odd-false = refl
