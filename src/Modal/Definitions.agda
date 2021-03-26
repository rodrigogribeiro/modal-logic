

module Modal.Definitions where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
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

-- if something is in a theory then it is provable

exact-deduction : ∀ {φ : Form n} → φ ∈ Γ → M ∶ Γ ⊢ φ
exact-deduction (here refl) (px ∷ M⊨Γ) = px
exact-deduction (there p) (px ∷ M⊨Γ) = exact-deduction p M⊨Γ

reflexive-deduction : ∀ {φ : Form n} → M ∶ (φ ∷ Γ) ⊢ φ
reflexive-deduction M⊨Γ  = exact-deduction (here refl) M⊨Γ

-- spliting a theory

theory-union-split : ∀ {δ : Theory n} → M ⊨ (Γ ++ δ) → M ⊨ Γ × M ⊨ δ
theory-union-split M⊨Γ++δ = ++⁻ _ M⊨Γ++δ

-- deduction is transitive

transitive-deduction : ∀ {φ ψ ϕ δ} → M ∶ φ ∷ Γ ⊢ ψ →
                                     M ∶ ψ ∷ δ ⊢ ϕ →
                                     M ∶ (φ ∷ Γ ++ δ) ⊢ ϕ
transitive-deduction {δ = δ} M⊨φ∷Γ⊢ψ M⊨ψ∷δ⊢ϕ M⊨ψ∷Γ++δ with theory-union-split {δ = δ} M⊨ψ∷Γ++δ
...| M⊨ψ∷Γ , M⊨δ = M⊨ψ∷δ⊢ϕ (M⊨φ∷Γ⊢ψ M⊨ψ∷Γ ∷ M⊨δ)


-- exchange property

exchange : ∀ {φ ψ ϕ} → M ∶ (φ ∷ ψ ∷ Γ) ⊢ ϕ → M ∶ (ψ ∷ φ ∷ Γ) ⊢ ϕ
exchange M∶φ∷ψ∷Γ⊢ϕ (px ∷ px₁ ∷ M⊨ψφΓ) = M∶φ∷ψ∷Γ⊢ϕ (px₁ ∷ px ∷ M⊨ψφΓ)

-- lifting permutations to membership

permutation-∈ : ∀ {A : Set l}{xs ys : List A} →
                xs ↭ ys → ∀ {p : A} → (p ∈ xs → p ∈ ys) × (p ∈ ys → p ∈ xs)
permutation-∈ xs⇔ys = ∈-resp-↭ xs⇔ys , ∈-resp-↭ (↭-sym xs⇔ys)


-- derivation is preserved by permutations

transpose-deduction : ∀ {δ φ} → Γ ↭ δ → M ∶ Γ ⊢ φ → M ∶ δ ⊢ φ
transpose-deduction refl M∶Γ⊢φ M⊨δ = M∶Γ⊢φ M⊨δ
transpose-deduction (prep x Γ⇔δ) M∶Γ⊢φ (px ∷ M⊨δ)
  = M∶Γ⊢φ (px ∷ All-resp-↭ (↭-sym Γ⇔δ) M⊨δ)
transpose-deduction (_↭_.swap x y Γ⇔δ) M∶Γ⊢φ (px ∷ px₁ ∷ M⊨δ)
  = M∶Γ⊢φ (px₁ ∷ px ∷ All-resp-↭ (↭-sym Γ⇔δ) M⊨δ)
transpose-deduction (_↭_.trans Γ⇔δ Γ⇔δ₁) M∶Γ⊢φ M⊨δ with All-resp-↭ (↭-sym Γ⇔δ₁) M⊨δ
...| M⊨ys = M∶Γ⊢φ (All-resp-↭ (↭-sym Γ⇔δ) M⊨ys)

idempotence : ∀ {φ ψ} → M ∶ φ ∷ φ ∷ Γ ⊢ ψ → M ∶ φ ∷ Γ ⊢ ψ
idempotence MφφΓ⊢ψ (px ∷ M⊨φΓ) = MφφΓ⊢ψ (px ∷ px ∷ M⊨φΓ)
