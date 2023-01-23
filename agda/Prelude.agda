{-# OPTIONS --rewriting #-}

--
-- Prelude.agda - Some base definitions
--

module Prelude where

  open import Agda.Primitive public

  record ⊤ : Set where
    constructor tt

  {-# BUILTIN UNIT ⊤ #-}

  record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  uncurry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
            (φ : (a : A) → (b : B a) → C) →
            Σ A B → C
  uncurry φ (a , b) = φ a b

  curry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
          (ψ : Σ A B → C) →
          (a : A) → (b : B a) → C
  curry ψ a b = ψ (a , b)

  infix 30 _==_

  data _==_ {i} {A : Set i} (a : A) : A → Set i where
    idp : a == a

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL idp #-}

  transport : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) → P a₀ → P a₁
  transport P idp x = x

  sym : ∀ {i} {A : Set i} {a₀ a₁ : A} (p : a₀ == a₁) → a₁ == a₀
  sym idp = idp

  etrans : ∀ {i} {A : Set i} {a₀ a₁ a₂ : A} → a₀ == a₁ → a₁ == a₂ → a₀ == a₂
  etrans idp idp = idp

  proof-irrelevance : ∀ {a} {A : Set a} {x y : A} (p q : x == y) → p == q
  proof-irrelevance idp idp = idp

  elimtransport : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) (q : a₀ == a₁) (r : p == q)  (x : P a₀) → transport P p x == transport P q x
  elimtransport P p .p idp x = idp

  tr! : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) (q : a₀ == a₁) (x : P a₀) → transport P p x == transport P q x
  tr! P p q x = elimtransport P p q (proof-irrelevance p q) x

  tr² : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ a₂ : A} (p : a₀ == a₁) (q : a₁ == a₂) (x : P a₀) → transport P q (transport P p x) == transport P (etrans p q) x
  tr² P idp idp x = idp

  tr³ : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ a₂ a₃ : A} (p₀ : a₀ == a₁) (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (x : P a₀) → transport P p₂ (transport P p₁ (transport P p₀ x)) == transport P (etrans p₀ (etrans p₁ p₂)) x
  tr³ P idp idp idp x = idp

  tr⁴ : ∀{i j} {A : Set i} (P : A → Set j) {a₀ a₁ a₂ a₃ a₄ : A} (p₀ : a₀ == a₁) (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (p₃ : a₃ == a₄) (x : P a₀) → transport P p₃ (transport P p₂ (transport P p₁ (transport P p₀ x))) == transport P (etrans p₀ (etrans p₁ (etrans p₂ p₃))) x
  tr⁴ P idp idp idp idp x = idp


  hfiber : ∀ {i} {A B : Set i} (f : A → B) (b : B) → Set i
  hfiber {A = A} f b = Σ A (λ a → f a == b)

  PathOver : ∀ {i j} {A : Set i} (B : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) (b₉ : B a₀) (b₁ : B a₁) → Set j
  PathOver B idp b₀ b₁ = b₀ == b₁

  infix 30 PathOver
  syntax PathOver B p u v =
    u == v [ B ↓ p ]

  Σ-r : ∀ {i j k} {A : Set i} {B : A → Set j} (C : Σ A B → Set k) → A → Set (j ⊔ k)
  Σ-r {A = A} {B = B} C a = Σ (B a) (λ b → C (a , b))

  Σ-in : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k) → A → Set (j ⊔ k)
  Σ-in {A = A} {B = B} C a = Σ (B a) (λ b → C a b)

  infix 30 _↦_

  postulate
    _↦_ : ∀ {i} {A : Set i} → A → A → Set i

  {-# BUILTIN REWRITE _↦_ #-}


  data bool : Set where
    true  : bool
    false : bool

  data ⊥ : Set where


  if_then_else : ∀ {a} {A : Set a} →  bool → A → A → A
  if true then A else B = A
  if false then A else B = B

  _≤_ : ℕ → ℕ → bool
  O ≤ n₁ = true
  S n₀ ≤ O = false
  S n₀ ≤ S n₁ = n₀ ≤ n₁

  min : ℕ → ℕ → ℕ
  min n₀ n₁ with n₀ ≤ n₁
  min n₀ n₁ | true = n₀
  min n₀ n₁ | false = n₁

  ≤S : ∀ (n₀ n₁ : ℕ) → (n₀ ≤ n₁) == true → (n₀ ≤ S n₁) == true
  ≤S O n₁ x = idp
  ≤S (S n₀) O ()
  ≤S (S n₀) (S n₁) x = ≤S n₀ n₁ x

  S≤S : ∀ (n₀ n₁ : ℕ) → (n₀ ≤ n₁) == true → (S n₀ ≤ S n₁) == true
  S≤S n₀ n₁ x = x
