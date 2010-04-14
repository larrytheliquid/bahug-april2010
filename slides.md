!SLIDE

   Another any
===================
Relationship advice
-------------------

!SLIDE
        even : ℕ → Bool
        even zero = true
        even (suc zero) = false
        even (suc (suc n)) = even n

        test-6-even : even 6 ≡ true
        test-6-even = refl        

!SLIDE
        odd : ℕ → Bool
        odd zero = false
        odd (suc zero) = true
        odd (suc (suc n)) = odd n

        test-5-odd : odd 5 ≡ true
        test-5-odd = refl

!SLIDE
        any : {A : Set} → (A → Bool) → List A → Bool
        any _ [] = false
        any p (x ∷ xs) with p x
        ... | true = true
        ... | false = any p xs

!SLIDE
        test-any-even-true : 
          any even (3 ∷ 6 ∷ 9 ∷ []) ≡ true
        test-any-even-true = refl

        test-any-even-false : 
          any even (3 ∷ 7 ∷ 9 ∷ []) ≡ false
        test-any-even-false = refl

!SLIDE
        test-any-odd-true : 
          any odd (4 ∷ 7 ∷ 10 ∷ []) ≡ true
        test-any-odd-true = refl

        test-any-odd-false : 
          any odd (4 ∷ 8 ∷ 10 ∷ []) ≡ false
        test-any-odd-false = refl

!SLIDE
        data Even : ℕ → Set where
          zero : Even 0
          suc : {n : ℕ} → Even n → Even (suc (suc n))

        6-Even : Even 6
        6-Even = suc (suc (suc zero))

!SLIDE
        Pred : Set → Set₁
        Pred A = A → Set

        _∈_ : {A : Set} → A → Pred A → Set
        a ∈ P = P a

        6-Even : 6 ∈ Even
        6-Even = suc (suc (suc zero))

!SLIDE
        data Odd : ℕ → Set where
          zero : Odd 1
          suc : {n : ℕ} → Odd n → Odd (suc (suc n))

        5-Odd : 5 ∈ Odd
        5-Odd = suc (suc zero)

!SLIDE
        data Any {A : Set} (P : Pred A) : 
               List A → Set where
          here :  ∀ {x xs} → x ∈ P → Any P (x ∷ xs)
          there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

!SLIDE
        test-any-even : Any Even (3 ∷ 6 ∷ 9 ∷ [])
        test-any-even = there (here 6-Even)

        test-any-odd : Any Odd (3 ∷ 5 ∷ 10 ∷ [])
        test-any-odd = there (here 5-Odd)

!SLIDE

<div style="display: none;">

And now for a brief excursion into more fun with relations
