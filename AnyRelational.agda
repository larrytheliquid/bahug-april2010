module AnyRelational where
open import Data.Function
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.List hiding (any)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to dec-map)
open import Relation.Binary.PropositionalEquality

Pred : Set → Set₁
Pred A = A → Set

_∈_ : {A : Set} → A → Pred A → Set
a ∈ P = P a

data Even : ℕ → Set where
  zero : Even 0
  suc : {n : ℕ} → Even n → Even (suc (suc n))

6-Even : 6 ∈ Even
6-Even = suc (suc (suc zero))

data Odd : ℕ → Set where
  zero : Odd 1
  suc : {n : ℕ} → Odd n → Odd (suc (suc n))

5-Odd : 5 ∈ Odd
5-Odd = suc (suc zero)

data Any {A : Set} (P : Pred A) : List A → Set where
  here :  ∀ {x xs} → x ∈ P    → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

test-any-even : Any Even (3 ∷ 6 ∷ 9 ∷ [])
test-any-even = there (here 6-Even)

test-any-odd : Any Odd (3 ∷ 5 ∷ 10 ∷ [])
test-any-odd = there (here 5-Odd)

U : {A : Set} → Pred A
U _ = ⊤

42-U : 42 ∈ U
42-U = tt

true-U : true ∈ U
true-U = tt

Universal : {A : Set} → Pred A → Set
Universal P = ∀ a → a ∈ P

U-Universal : {A : Set} → Universal {A} U
U-Universal _ = tt

_∪_ : {A : Set} → Pred A → Pred A → Pred A
P ∪ Q = λ a → P a ⊎ Q a

evenOrOdd : Universal (Even ∪ Odd)
evenOrOdd 0 = inj₁ zero
evenOrOdd 1 = inj₂ zero
evenOrOdd (suc n) with evenOrOdd n
... | inj₁ p = inj₂ (evenSucOdd p) where
  evenSucOdd : ∀ {n} → Even n → Odd (suc n)
  evenSucOdd zero = zero
  evenSucOdd (suc n) = suc (evenSucOdd n)
... | inj₂ p = inj₁ (oddSucEven p) where
  oddSucEven : ∀ {n} → Odd n → Even (suc n)
  oddSucEven zero = suc zero
  oddSucEven (suc n) = suc (oddSucEven n)

∁ : {A : Set} → Pred A → Pred A
∁ P = λ a → ¬ (P a)

_⇒_ : {A : Set} → Pred A → Pred A → Set
P ⇒ Q = ∀ {a} → P a → Q a

even⇒¬odd : Even ⇒ ∁ Odd
even⇒¬odd zero = λ()
even⇒¬odd (suc e) with even⇒¬odd e
even⇒¬odd (suc e) | f = λ o → f (predOdd o) where
  predOdd : ∀ {n} → Odd (suc (suc n)) → Odd n
  predOdd (suc n) = n

∅ : {A : Set} → Pred A
∅ _ = ⊥

_∉_ : {A : Set} → A → Pred A → Set
a ∉ P = ¬ (a ∈ P)

42-¬∅ : 42 ∉ ∅
42-¬∅ ()

true-¬∅ : true ∉ ∅
true-¬∅ ()

Empty : {A : Set} → Pred A → Set
Empty P = ∀ a → a ∉ P

∅-Empty : {A : Set} → Empty {A} ∅
∅-Empty _ ()

∁∅-Universal : {A : Set} → Universal {A} (∁ ∅)
∁∅-Universal _ ()

∁U-Empty : {A : Set} → Empty {A} (∁ U)
∁U-Empty _ ∁U = ∁U tt

test-any-6≡ : Any ( _≡_ 6) (3 ∷ 6 ∷ 9 ∷ [])
test-any-6≡ = there (here refl)

find : ∀ {A : Set} {P : Pred A} {as : List A} → 
       Any P as → ∃ (λ a → Any (_≡_ a) as × a ∈ P)
find (here p) = _ , (here refl , p)
find (there ps) = Data.Product.map id 
                  (Data.Product.map there id)
                  (find ps)

-- test-any-even : Any Even (3 ∷ 6 ∷ 9 ∷ [])
-- test-any-even = there (here (suc (suc (suc zero))))

-- 6-found : proj₁ (find test-any-even) ≡ 6
-- 6-found = refl

-- 6-Even : 6 ∈ Even
-- 6-Even = proj₂ (proj₂ (find test-any-even))

-- test-any-6≡ : Any (_≡_ 6) (3 ∷ 6 ∷ 9 ∷ [])
-- test-any-6≡ = proj₁ (proj₂ (find test-any-even))


tail : ∀ {A x xs} {P : Pred A} → x ∉ P → Any P (x ∷ xs) → Any P xs
tail ¬p (here  p) = ⊥-elim (¬p p)
tail ¬p (there ps) = ps

any : {A : Set} {P : Pred A} →
      (∀ x → Dec (x ∈ P)) → (xs : List A) → Dec (Any P xs)
any f [] = no λ()
any f (x ∷ xs) with f x
any f (x ∷ xs) | yes p = yes (here p)
any f (x ∷ xs) | no ¬p = dec-map (there , tail ¬p) (any f xs)
