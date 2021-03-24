

module Modal.Deduction {l}(W : Set l) where

open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.Nat
open import Data.Product hiding (swap)
open import Data.Sum hiding (swap)
open import Function
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Modal.Definitions W

-- derivation for the shallow encoding

Ctx : Set (lsuc l)
Ctx = List Pred

_▷_ : Ctx → W → Set (lsuc l)
[] ▷ _ = ⊤
(p ∷ G) ▷ w = p w × (G ▷ w)

infix 4 _⊢_

_⊢_ : Ctx → Pred → Set (lsuc l)
G ⊢ p = ∀ w → G ▷ w → p w

-- structural properties

`cut : ∀ {p q G} → (q ∷ G) ⊢ p → G ⊢ q → G ⊢ p
`cut qp q w Gw = qp w (q w Gw , Gw)

postulate `weakening : ∀ {G1 G2 p} → G1 ⊆ G2 → G1 ⊢ p → G2 ⊢ p
postulate `exchange : ∀ {G1 G2 p} → G1 ↭ G2 → G1 ⊢ p → G2 ⊢ p
postulate `derives-≡ : ∀ {p q} → [ p ] ⊢ q → [ q ] ⊢ p → p ≡ q

-- logic rules for the shallow embedding

`⊤-intro : ∀ {G} → G ⊢ `⊤
`⊤-intro {G} = λ w _ → tt

`⊥-elim : ∀ {G p} → (`⊥ ∷ G) ⊢ p
`⊥-elim {G} {p} = λ w k → ⊥-elim (proj₁ k)

`assumption : ∀ {G p} → p ∈ G → G ⊢ p
`assumption (here refl) = λ w → proj₁
`assumption (there p) w (xw , xs▷w) = `assumption p w xs▷w

`fst : ∀ {G p} → (p ∷ G) ⊢ p
`fst = `assumption (here refl)

`snd : ∀ {G p q} → q ∷ p ∷ G ⊢ p
`snd = `assumption (there (here refl))

-- rules for conjunction

`∧-intro : ∀ {G p q} → G ⊢ p → G ⊢ q → G ⊢ (p `∧ q)
`∧-intro p1 p2 = λ w z → p1 w z , p2 w z

`∧-elim : ∀ {G p q r} → p ∷ q ∷ G ⊢ r → (p `∧ q) ∷ G ⊢ r
`∧-elim pf w ((p , q) , Gw) = pf w (p , (q , Gw))

`∧-elim-left : ∀ {G p q r} → p ∷ G ⊢ r → (p `∧ q) ∷ G ⊢ r
`∧-elim-left pf w ((p , q) , Gw) = pf w (p , Gw)

`∧-elim-right :  ∀ {G p q r} → q ∷ G ⊢ r → (p `∧ q) ∷ G ⊢ r
`∧-elim-right pf w ((p , q) , Gw) = pf w (q , Gw)

`∧-derives-commutes : ∀ {p q} → [ p `∧ q ] ⊢ q `∧ p
`∧-derives-commutes w ((p , q) , tt) = q , p

`∧-commutes : ∀ {p q} → p `∧ q ≡ q `∧ p
`∧-commutes = `derives-≡ `∧-derives-commutes `∧-derives-commutes

`∧-assoc : ∀ {p q r} → (p `∧ (q `∧ r)) ≡ ((p `∧ q) `∧ r)
`∧-assoc = `derives-≡ lemma1 lemma2
  where
    lemma1 : ∀ {a b c} → [ a `∧ (b `∧ c) ] ⊢ ((a `∧ b) `∧ c)
    lemma1 = `∧-intro (`∧-intro (`∧-elim  λ w → proj₁)
                                (λ w z → proj₁ (proj₂ (proj₁ z))))
                      (λ w z → proj₂ (proj₂ (proj₁ z)))

    lemma2 : ∀ {a b c} → [ ((a `∧ b) `∧ c) ] ⊢ a `∧ (b `∧ c)
    lemma2 = `∧-intro (λ w z → proj₁ (proj₁ (proj₁ z)))
                      (`∧-elim (`∧-intro (λ w z → proj₂ (proj₁ z))
                                         (λ w z → proj₁ (proj₂ z))))

`⊤-`∧ : ∀ {p} → `⊤ `∧ p ≡ p
`⊤-`∧ = `derives-≡ (`∧-elim (λ w z → proj₁ (proj₂ z)))
                    (`∧-intro `⊤-intro (λ w → proj₁))

`⊥-`∧ : ∀ {p} → `⊥ `∧ p ≡ `⊥
`⊥-`∧ = `derives-≡ (`∧-elim (λ w z → lift (lower (proj₁ z))))
                   `⊥-elim


-- rules for disjunction

`∨-intro-left : ∀ {G p q} → G ⊢ p → G ⊢ (p `∨ q)
`∨-intro-left p w k = inj₁ (p w k)

`∨-intro-right : ∀ {G p q} → G ⊢ q → G ⊢ (p `∨ q)
`∨-intro-right q w k = inj₂ (q w k)

`∨-elim : ∀ {G p q r} → p ∷ G ⊢ r → q ∷ G ⊢ r → (p `∨ q) ∷ G ⊢ r
`∨-elim pr qr w (inj₁ x , G▷w) = pr w (x , G▷w)
`∨-elim pr qr w (inj₂ y , G▷w) = qr w (y , G▷w)

`∨-derives-commutes : ∀ {p q} → [ p `∨ q ] ⊢ q `∨ p
`∨-derives-commutes w (inj₁ x , tt) = inj₂ x
`∨-derives-commutes w (inj₂ y , tt) = inj₁ y

`∨-commutes : ∀ {p q} → p `∨ q ≡ q `∨ p
`∨-commutes = `derives-≡ `∨-derives-commutes `∨-derives-commutes

`∨-assoc : ∀ {p q r} → p `∨ (q `∨ r) ≡ ((p `∨ q) `∨ r)
`∨-assoc = `derives-≡ lemma1 lemma2
    where
      lemma1 : ∀ {p q r} → [ p `∨ (q `∨ r) ] ⊢ ((p `∨ q) `∨ r)
      lemma1 = `∨-elim (`∨-intro-left (`∨-intro-left (λ _ → proj₁)))
                       (`∨-elim (`∨-intro-left (`∨-intro-right (λ _ → proj₁)))
                                (`∨-intro-right (λ _ → proj₁)))

      lemma2 :  ∀ {p q r} → [ ((p `∨ q) `∨ r) ] ⊢  p `∨ (q `∨ r)
      lemma2 = `∨-elim (`∨-elim (λ w z → inj₁ (proj₁ z))
                                (`∨-intro-right (λ w z → inj₁ (proj₁ z))))
                       (`∨-intro-right (`∨-intro-right (λ _ → proj₁)))

`⊥-`∨ : ∀ {p} → `⊥ `∨ p ≡ p
`⊥-`∨ = `derives-≡ (`∨-elim `⊥-elim λ _ → proj₁)
                   (λ w z → inj₂ (proj₁ z))

`⊤-`∨ : ∀ {p} → `⊤ `∨ p ≡ `⊤
`⊤-`∨ = `derives-≡ `⊤-intro (`∨-intro-left `⊤-intro)


-- distributivity

distr-`∨-`∧ : ∀ {p q r} → (p `∨ q) `∧ r ≡ (p `∧ r) `∨ (q `∧ r)
distr-`∨-`∧ = `derives-≡ (`∧-elim (`∨-elim (`∨-intro-left (`∧-intro `fst `snd))
                                            (`∨-intro-right (`∧-intro `fst `snd))))
                         (`∨-elim (`∧-elim (`∧-intro (`∨-intro-left `fst) `snd))
                                  (`∧-elim (`∧-intro (`∨-intro-right `fst) `snd)))

distr-`∧-`∨ : ∀ {p q r} → (p `∧ q) `∨ r ≡ (p `∨ r) `∧ (q `∨ r)
distr-`∧-`∨ = `derives-≡ (`∨-elim (`∧-elim (`∧-intro (`∨-intro-left `fst)
                                                     (`∨-intro-left `snd)))
                                  (`∧-intro (`∨-intro-right `fst)
                                            (`∨-intro-right `fst)))
                          (`∧-elim (`∨-elim (`exchange (swap _ _ _↭_.refl)
                                                       (`∨-elim (`∨-intro-left (`∧-intro `snd `fst))
                                                                (`∨-intro-right `fst)))
                                            (`∨-intro-right `fst)))

-- implication

`⟶-intro : ∀ {G p q} → p ∷ G ⊢ q → G ⊢ (p `⟶ q)
`⟶-intro pf w Gw pw = pf w (pw , Gw)

`⟶-elim : ∀ {G p q} → G ⊢ p → (p `⟶ q) ∷ G ⊢ q
`⟶-elim pf w (pqf , Gw) = pqf (pf w Gw)

`modus-ponens : ∀ {G p q r} → G ⊢ p → q ∷ G ⊢ r → (p `⟶ q) ∷ G ⊢ r
`modus-ponens pf qrf w (pqf , Gw) = qrf w ((pqf (pf w Gw)) , Gw)

-- existential quantifier

`∃-intro : ∀ {A : Set}{f : A → Pred}{x G} → G ⊢ (f x) → G ⊢ (`∃ f)
`∃-intro {x = x} pfx w Gw = x , pfx w Gw

`∃-elim : ∀ {A : Set}{f : A → Pred}{G p} →
          (∀ (x : A) → f x ∷ G ⊢ p)      →
          `∃ f ∷ G ⊢ p
`∃-elim hyp w ((x , fx) , Gw) = hyp x w (fx , Gw)

-- universal quantifier

`∀-intro : ∀ {A : Set}{f : A → Pred}{G} →
           (∀ (x : A) → G ⊢ f x) → G ⊢ `∀ f
`∀-intro hyp w Gw = λ x → hyp x w Gw


`∀-elim : ∀ {A}{x : A}{f : A → Pred}{G p} →
          f x ∷ G ⊢ p → `∀ f ∷ G ⊢ p
`∀-elim {x = x} fp w (fxw , Gw) = fp w (fxw x , Gw)
