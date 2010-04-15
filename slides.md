!SLIDE

  any other way
===================
relationship advice
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
        U : {A : Set} → Pred A
        U _ = ⊤

        42-U : 42 ∈ U
        42-U = tt

        true-U : true ∈ U
        true-U = tt

<div style="display: none;">

And now for a brief intermezzo of more fun with relations

!SLIDE
        Universal : {A : Set} → Pred A → Set
        Universal P = ∀ a → a ∈ P

        U-Universal : {A : Set} → Universal {A} U
        U-Universal _ = tt

!SLIDE
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

!SLIDE
        ∅ : {A : Set} → Pred A
        ∅ _ = ⊥

        _∉_ : {A : Set} → A → Pred A → Set
        a ∉ P = ¬ (a ∈ P)

        42-¬∅ : 42 ∉ ∅
        42-¬∅ ()

        true-¬∅ : true ∉ ∅
        true-¬∅ ()

!SLIDE
        ∁ : {A : Set} → Pred A → Pred A
        ∁ P = λ a → ¬ (P a)

        _⇒_ : {A : Set} → Pred A → Pred A → Set
        P ⇒ Q = ∀ {a} → P a → Q a

        predOdd : ∀ {n} → Odd (suc (suc n)) → Odd n
        predOdd (suc n) = n

        even⇒¬odd : Even ⇒ ∁ Odd
        even⇒¬odd zero = λ()
        even⇒¬odd (suc e) with even⇒¬odd e
        even⇒¬odd (suc e) | f = λ o → f (predOdd o)

!SLIDE
        Empty : {A : Set} → Pred A → Set
        Empty P = ∀ a → a ∉ P

        ∅-Empty : {A : Set} → Empty {A} ∅
        ∅-Empty _ ()

        ∁∅-Universal : {A : Set} → Universal {A} (∁ ∅)
        ∁∅-Universal _ ()

        ∁U-Empty : {A : Set} → Empty {A} (∁ U)
        ∁U-Empty _ ∁U = ∁U tt

!SLIDE
        6-Even : 6 ∈ Even
        6-Even = suc (suc (suc zero))

        test-any-even : Any Even (3 ∷ 6 ∷ 9 ∷ [])
        test-any-even = there (here 6-Even)

        test-any-6≡ : Any (_≡_ 6) (3 ∷ 6 ∷ 9 ∷ [])
        test-any-6≡ = there (here refl)

!SLIDE
        data Σ (A : Set) (B : A → Set) : Set where
          _,_ : (x : A) (y : B x) → Σ A B

        _×_ : ∀ (A : Set) (B : Set) → Set
        A × B = Σ A (λ _ → B)

        ∃ : ∀ {A : Set} → (A → Set) → Set
        ∃ = Σ _

!SLIDE
        find : ∀ {A : Set} {P : Pred A} {as : List A} → 
               Any P as → ∃ (λ a → 
                   Any (_≡_ a) as × a ∈ P)
        find (here p) = _ , (here refl , p)
        find (there ps) = Data.Product.map id 
                          (Data.Product.map there id)
                          (find ps)

!SLIDE
        test-any-even : Any Even (3 ∷ 6 ∷ 9 ∷ [])
        test-any-even = there (here (suc (suc (suc zero))))

        6-found : proj₁ (find test-any-even) ≡ 6
        6-found = refl

        6-Even : 6 ∈ Even
        6-Even = proj₂ (proj₂ (find test-any-even))

        test-any-6≡ : Any (_≡_ 6) (3 ∷ 6 ∷ 9 ∷ [])
        test-any-6≡ = proj₁ (proj₂ (find test-any-even))

!SLIDE
        data Dec (P : Set) : Set where
          yes : P   → Dec P
          no  : ¬ P → Dec P

        _⇔_ : Set → Set → Set
        P ⇔ Q = (P → Q) × (Q → P)

        dec-map : {P Q : Set} → P ⇔ Q → Dec P → Dec Q
        dec-map eq (yes p) = yes (proj₁ eq p)
        dec-map eq (no ¬p) = no (¬p ∘ proj₂ eq)

!SLIDE
        tail : ∀ {A x xs} {P : Pred A} → 
               x ∉ P → Any P (x ∷ xs) → Any P xs
        tail ¬p (here  p) = ⊥-elim (¬p p)
        tail ¬p (there ps) = ps

        any : {A : Set} {P : Pred A} →
              (∀ x → Dec (x ∈ P)) →
              (xs : List A) →
              Dec (Any P xs)
        any f [] = no λ()
        any f (x ∷ xs) with f x
        any f (x ∷ xs) | yes p = yes (here p)
        any f (x ∷ xs) | no ¬p = dec-map 
          (there , tail ¬p) (any f xs)

!SLIDE
        Dec-Even : ∀ n → Dec (n ∈ Even)
        Dec-Even zero = yes zero
        Dec-Even (suc zero) = no λ()
        Dec-Even (suc n) with Dec-Even n
        ... | yes p = no (even¬Consecutive p)
        ... | no ¬p = yes (¬even¬Consecutive ¬p)

!SLIDE
        predEven : ∀ {n} →
                   Even (suc (suc n)) → Even n
        predEven (suc n) = n

        even¬Consecutive : ∀ {n} →
                           n ∈ Even → suc n ∉ Even
        even¬Consecutive zero = λ ()
        even¬Consecutive (suc n) with even¬Consecutive n
        ... | ¬p = λ e → ¬p (predEven e)

        postulate
          ¬even¬Consecutive : ∀ {n} →
                              n ∉ Even → suc n ∈ Even
