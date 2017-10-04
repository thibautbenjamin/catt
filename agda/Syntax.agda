{-# OPTIONS --without-K --rewriting #-}

open import Prelude

module Syntax where 

data Con           : Set
data Ty            : Con → Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data Sub           : Con → Con → Set
data isContr       : Con → Set
-- data isPs          : Con → Set

infix 4 _⇒_
infixl 5 _,_ 

suspend : Con → Con

id : ∀{Γ} → Sub Γ Γ

_∘_ : ∀ {Γ Δ Θ} (δ : Sub Θ Δ) (σ : Sub Δ Γ) → (Sub Θ Γ)
-- ∘Nl : ∀ {Γ Δ} (σ : Sub Δ Γ) → id ∘ σ == σ
-- ∘Nr : ∀ {Γ Δ} (σ : Sub Δ Γ) → σ ∘ id == σ
-- ∘A : ∀ {Γ Δ Θ Ξ} (σ : Sub Δ Γ) (δ : Sub Θ Δ) (λ : Sub Ξ Θ) → λ ∘ (δ ∘ σ) == (λ ∘ δ) ∘ σ

_[_]T : ∀ {Γ Δ} (A : Ty Γ) (σ : Sub Δ Γ) → Ty Δ
compT : ∀ {Γ Δ Θ} (A : Ty Γ) (σ : Sub Δ Γ) (δ : Sub Θ Δ) → (A [ δ ∘ σ ]T) == ((A [ σ ]T ) [ δ ]T) 

_[_]tm : ∀ {Γ Δ} {A : Ty Γ} (t : Tm A) (σ : Sub Δ Γ)  → Tm (A [ σ ]T)
-- comptm : ∀ {Γ Δ Θ} {A : Ty Γ} (t : Tm A) (σ : Sub Δ Γ) (δ : Sub Θ Δ) → (transport (compT A σ δ) ((t [ σ ]tm ) [ δ ]tm)) == (t [ δ ∘ σ ]tm)

data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
  
data Ty where
  *     : {Γ : Con} → Ty Γ
  _⇒_  : {Γ : Con}{A : Ty Γ}(a b : Tm A) → Ty Γ


-- No identity substitution? empty context is not the terminal context?
-- data Sub where
--   _,_  : ∀{Γ Δ}(δ : Sub Γ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) → Sub Γ (Δ , A)
--   π₁ : ∀ {Γ} {A : Ty Γ} → Sub (Γ , A) Γ

data Sub where
  _,_ : ∀{Γ Δ} (δ : Sub Γ Δ) {A : Ty Δ}(a : Tm (A [ δ ]T)) → Sub Γ (Δ , A)
  ∅  : ∀ {Γ} → Sub Γ ε
  π₁ : ∀ {Γ} {A : Ty Γ} → Sub (Γ , A) Γ

-- idT : ∀{Γ}{A} → A [ id ]T == A
-- idtm : ∀{Γ}{A}{t} → t [ id ]tm == t


data Tm where
  coh : ∀ {Γ Δ} → (A : Ty Γ) → (σ : Sub Δ Γ) → isContr Γ → Tm (A [ σ ]T)
  π₂ : ∀ {Γ} (A : Ty Γ) → Tm {Γ , A} (A [ π₁ ]T)

data isContr where
  c*   : isContr (ε , *)
  ext   : ∀ {Γ} {A} → isContr (Γ , A) → isContr (Γ , A , A [ π₁ ]T , ((π₂ A) [ π₁ ]tm ⇒ π₂ (A [ π₁ ]T)))

-- data isPs where
--   c* : isPs (ε , *)
--   Σ : ∀ {Γ} → isPs Γ → isPs (suspend Γ)


id {ε} = ∅
id {Γ , A} = (π₁ , π₂ A)

_[_]T {Γ} {Δ} * σ = *
_[_]T {Γ} {Δ} (a ⇒ b) σ = (a [ σ ]tm) ⇒ (b [ σ ]tm)

compT * σ δ = idp
compT (a ⇒ b) σ δ = {!!}



-- comp A (σ , a) δ = {!!}
-- comp * π₁ δ = refl
-- comp (a ⇒ b) π₁ δ = cong {!!} {!!}
-- comp A ∅ δ = {!!}


δ ∘ (σ , a) = ((δ ∘ σ) , {!a [ δ ]tm!} )
δ ∘ π₁ = {!!}
δ ∘ ∅ = ∅

∘Nl = {!!}
∘Nr = {!!}
∘A = {!!}

idT = {!!}

-- _[_]tm : ∀ {Γ Δ} {A : Ty Γ} (t : Tm A) (σ : Sub Δ Γ)  → Tm (A [ σ ]T)
_[_]tm {Δ} {Θ} (coh {Γ} .{Δ} A δ isc) σ = transport Tm (compT A δ σ) (coh {Γ} A (σ ∘ δ) isc)
_[_]tm (π₂ A) π₁ = {!!}
_[_]tm (π₂ A) (σ , B) = {!!}

  -- coh : ∀ {Γ Δ} → (A : Ty Γ) → (σ : Sub Δ Γ) → isContr Γ → Tm (A [ σ ]T)


idtm = {!!}
-- comptm = ?


suspend ε = ((ε , *), *)
suspend (Γ , A) = (suspend Γ , ({!!} ⇒ {!!}))

