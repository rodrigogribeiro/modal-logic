

module Modal.Definitions where

open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Level renaming (suc to lsuc)
open import Relation.Nullary

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


-- formula valuation in a model

_∶_⊩_ : ∀ {l}{n : ℕ}(M : Model l) → W (frame M) → Form n → Set l
M ∶ w ⊩ `var x = φ M x w
M ∶ w ⊩ `not A = ¬ (M ∶ w ⊩ A)
M ∶ w ⊩ (A `∧ A') = (M ∶ w ⊩ A) × (M ∶ w ⊩ A')
M ∶ w ⊩ (A `∨ A') = (M ∶ w ⊩ A) ⊎ (M ∶ w ⊩ A')
M ∶ w ⊩ (A `⊃ A') = M ∶ w ⊩ A → M ∶ w ⊩ A'
M ∶ w ⊩ (■ A) = ∀ {w' : W (frame M)} → R (frame M) w w' → M ∶ w ⊩ A
M ∶ w ⊩ (◆ A) = ∃ (λ w' → R (frame M) w w' × M ∶ w' ⊩ A)


-- definition of truth in a model

_⊩_ : ∀ {l n} → Model l → Form n → Set l
M ⊩ A = ∀ {w : W (frame M)} → M ∶ w ⊩ A
