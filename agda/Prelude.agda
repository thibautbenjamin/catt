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

  
