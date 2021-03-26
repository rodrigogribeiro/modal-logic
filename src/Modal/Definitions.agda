

module Modal.Definitions where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Sum
open import Level renaming (suc to lsuc)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- definition of formulas

data Form (n : ℕ) : Set where
  `var : Fin n → Form n
  `not : Form n → Form n
  _`∧_ : Form n → Form n → Form n
  _`∨_ : Form n → Form n → Form n
  _`⊃_ : Form n → Form n → Form n
  ■_   : Form n → Form n
  ◆_   : Form n → Form n


-- definition of a frame

record Frame (l : Level) : Set (lsuc l)  where
  constructor ⟪_,_⟫
  field
    W  : Set l
    R  : W → W → Set l

open Frame

-- definition of a model

record Model (l : Level) : Set (lsuc l) where
  constructor ⟨_,_⟩
  field
    frame : Frame l
    φ     : ∀ {n} → Fin n → (W frame) → Set l

open Model


-- formula valuation in a world

_∶_⊩_ : ∀ {l}{n : ℕ}(M : Model l) → W (frame M) → Form n → Set l
M ∶ w ⊩ `var x = φ M x w
M ∶ w ⊩ `not A = ¬ (M ∶ w ⊩ A)
M ∶ w ⊩ (A `∧ A') = (M ∶ w ⊩ A) × (M ∶ w ⊩ A')
M ∶ w ⊩ (A `∨ A') = (M ∶ w ⊩ A) ⊎ (M ∶ w ⊩ A')
M ∶ w ⊩ (A `⊃ A') = M ∶ w ⊩ A → M ∶ w ⊩ A'
M ∶ w ⊩ (■ A) = ∀ {w' : W (frame M)} → R (frame M) w w' → M ∶ w' ⊩ A
M ∶ w ⊩ (◆ A) = ∃ (λ w' → R (frame M) w w' × M ∶ w' ⊩ A)


-- definition of truth in a model

_⊩_ : ∀ {l n} → Model l → Form n → Set l
M ⊩ A = ∀ {w : W (frame M)} → M ∶ w ⊩ A

-- definition of a theory

Theory : (n : ℕ) → Set
Theory n = List (Form n)

_⊨_ : ∀ {l n} → Model l → Theory n → Set l
M ⊨ Γ = All (M ⊩_) Γ


-- definition of entailment

_∶_⊢_ : ∀ {l n} → Model l → Theory n → Form n → Set l
M ∶ Γ ⊢ φ = M ⊨ Γ → M ⊩ φ


-- properties

variable n : ℕ
variable Γ : Theory n
variable l : Level
variable M : Model l

exact-deduction : ∀ {φ : Form n} → φ ∈ Γ → M ∶ Γ ⊢ φ
exact-deduction (here refl) (px ∷ M⊨Γ) = px
exact-deduction (there p) (px ∷ M⊨Γ) = exact-deduction p M⊨Γ


reflexive-deduction : ∀ {φ : Form n} → M ∶ (φ ∷ Γ) ⊢ φ
reflexive-deduction M⊨Γ  = exact-deduction (here refl) M⊨Γ


theory-union-split : ∀ {δ : Theory n} → M ⊨ (Γ ++ δ) → M ⊨ Γ × M ⊨ δ
theory-union-split M⊨Γ++δ = ++⁻ _ M⊨Γ++δ
