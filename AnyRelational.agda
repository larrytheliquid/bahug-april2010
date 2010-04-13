module AnyRelational where
open import Data.Bool
open import Data.Nat
open import Data.List hiding (any)
open import Relation.Binary.PropositionalEquality

Pred : Set → Set₁
Pred A = A → Set

data Any {A : Set} (P : Pred A) : List A → Set where
  here :  ∀ {x xs} → P x      → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

data Even : ℕ → Set where
  zero : Even 0
  suc : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  zero : Odd 1
  suc : {n : ℕ} → Odd n → Odd (suc (suc n))
