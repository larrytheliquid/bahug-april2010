module AnyBoolean where
open import Data.Bool
open import Data.Nat
open import Data.List hiding (any)
open import Relation.Binary.PropositionalEquality

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

test-6-even : even 6 ≡ true
test-6-even = refl

odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

test-5-odd : odd 5 ≡ true
test-5-odd = refl

any : {A : Set} → (A → Bool) → List A → Bool
any _ [] = false
any p (x ∷ xs) with p x
... | true = true
... | false = any p xs

test-any-even-true : 
  any even (3 ∷ 6 ∷ 9 ∷ []) ≡ true
test-any-even-true = refl

test-any-even-false : 
  any even (3 ∷ 7 ∷ 9 ∷ []) ≡ false
test-any-even-false = refl

test-any-odd-true : 
  any odd (4 ∷ 7 ∷ 10 ∷ []) ≡ true
test-any-odd-true = refl

test-any-odd-false : 
  any odd (4 ∷ 8 ∷ 10 ∷ []) ≡ false
test-any-odd-false = refl
