{-# OPTIONS --without-K --rewriting #-}

open import Prelude

module Syntax where

data Con           : (n : ℕ) → Set
Ctx : Set
Ctx = Σ ℕ Con
data Ty            : Ctx → Set
data Tm            : {Γ : Ctx} (A : Ty Γ) → Set
data Sub           : Ctx → Ctx → Set




𝔻 : (n : ℕ) → Con n
dangling : {n : ℕ} (Γ : Con n) → Sub (n , Γ) (n , 𝔻 n)

_[_]T : ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
_[_]tm : ∀ {Γ Δ} {A : Ty Γ} (t : Tm A) (σ : Sub Δ Γ)  → Tm (A [ σ ]T)

_≃_ : ∀ (Γ Δ : Ctx) {γ : Sub Δ Γ} {δ : Sub Γ Δ} → Set


-- Type theory for globular sets
data Con where
  Start     : Con (O)
  Ext       : ∀ {n : ℕ} (Γ : Con (n)) → Con (S n)
  Drop      : ∀ {n : ℕ} (Γ : Con (S n)) → Con n

Ext' : Ctx → Ctx
Ext' Γ = (S (fst Γ) , Ext (snd Γ))

data Ty where
  ⇒/_         : ∀ {n} {Δ} (σ : Sub Δ (n , 𝔻 n)) → Ty Δ

data Sub where
  id          : ∀ {Γ} → Sub Γ Γ
  _∘_         : ∀ {Γ Δ Θ} (δ : Sub Θ Δ) (γ : Sub Δ Γ) → Sub Θ Γ
  Drop        : ∀ {n} (Γ : Con (S n)) → Sub (S n , Γ) (n , Drop Γ)
  Drop-       : ∀ {n} (Γ : Con (S n)) → Sub (n , Drop Γ) (S n , Γ)
  π₁          : ∀ (Γ : Ctx) → Sub (Ext' Γ) Γ
  _,_         : ∀ {Γ Δ} (γ : Sub Δ Γ) (a : Tm ((⇒/ (dangling (snd Γ))) [ γ ]T))  → Sub Δ (Ext' Γ)  

data Tm where
--  π₂ : ∀ {Γ} (A : Ty Γ) → Tm {Γ , A} (A [ π₁ ]T)

postulate
  -- category structure
  idl : ∀ {Γ Δ} {γ : Sub Δ Γ} → (γ ∘ id) == γ
  idr : ∀ {Γ Δ} {γ : Sub Δ Γ} → (id ∘ γ) == γ
  assoc : ∀ {Γ Δ Θ Φ} {γ : Sub Δ Γ} {δ : Sub Θ Δ} {θ : Sub Φ Θ} → (θ ∘ (δ ∘ γ)) == ((θ ∘ δ) ∘ γ)
  -- skeleton
  iso : ∀ {n} {Γ : Con (S n)} → ((S n , Γ) ≃ (n , (Drop Γ))) {Drop- Γ} {Drop Γ}


𝔻 O = Start
𝔻 (S n) = Ext (𝔻 n)

dangling Start = id
dangling (Ext Γ) = {!!}
dangling (Drop Γ) = {!!}

_≃_ Γ Δ {γ} {δ} = {!((γ ∘ δ) == id) ^ ((δ ∘ γ) == id)!}

_[_]T {Γ} {Δ} (⇒/ σ₁) σ = ⇒/ (σ ∘ σ₁)

_[_]tm = {!!}
