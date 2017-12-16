module LCS where

open import Level using (zero)
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function using (_on_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Induction.Nat
open import Induction.WellFounded

longest : List ℕ → List ℕ → List ℕ
longest xs ys with length xs ≤? length ys
... | yes len[xs]≤len[ys] = ys
... | no  len[xs]>len[ys] = xs

LCS : List ℕ → List ℕ → List ℕ
LCS [] ys = []
LCS (_ ∷ _) [] = []
LCS xxs@(x ∷ xs) yys@(y ∷ ys) with x ≟ y
... | yes x≡y = x ∷ LCS xs ys
... | no  x≢y = longest (LCS xxs ys) (LCS xs yys)

infix 4 _⊑_

data _⊑_ : List ℕ → List ℕ → Set where
  empty : ∀ {xs} → [] ⊑ xs
  here  : ∀ {x xs ys} → xs ⊑ ys → x ∷ xs ⊑ x ∷ ys
  there : ∀ {y xs ys} → xs ⊑ ys → xs ⊑ y ∷ ys

_is-common-subseq-of_ : List ℕ → List ℕ × List ℕ → Set
zs is-common-subseq-of (xs , ys) = (zs ⊑ xs) × (zs ⊑ ys)

longest-either : (P : List ℕ → Set){xs ys : List ℕ} → P xs → P ys → P (longest xs ys)
longest-either P {xs} {ys} Pxs Pys with length xs ≤? length ys
... | yes len[xs]≤len[ys] = Pys
... | no  len[xs]>len[ys] = Pxs

LCS[xs,ys]⊑xs : ∀ xs ys → LCS xs ys ⊑ xs
LCS[xs,ys]⊑xs [] ys = empty
LCS[xs,ys]⊑xs (x ∷ xs) [] = empty
LCS[xs,ys]⊑xs (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes refl = here (LCS[xs,ys]⊑xs xs ys)
... | no  x≢y
  = longest-either (_⊑ x ∷ xs) (LCS[xs,ys]⊑xs (x ∷ xs) ys) (there (LCS[xs,ys]⊑xs xs (y ∷ ys)))

LCS[xs,ys]⊑ys : ∀ xs ys → LCS xs ys ⊑ ys
LCS[xs,ys]⊑ys [] ys = empty
LCS[xs,ys]⊑ys (x ∷ xs) [] = empty
LCS[xs,ys]⊑ys (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes refl = here (LCS[xs,ys]⊑ys xs ys)
... | no  x≢y
  = longest-either (_⊑ y ∷ ys) (there (LCS[xs,ys]⊑ys (x ∷ xs) ys)) (LCS[xs,ys]⊑ys xs (y ∷ ys))

theorem1 : ∀ xs ys → LCS xs ys is-common-subseq-of (xs , ys)
theorem1 xs ys = LCS[xs,ys]⊑xs xs ys , LCS[xs,ys]⊑ys xs ys

monotone-⊑-≤ : ∀ x y → x ⊑ y → length x ≤ length y
monotone-⊑-≤ .[] y empty = z≤n
monotone-⊑-≤ .(_ ∷ _) .(_ ∷ _) (here {_} {xs} {ys} xs⊑ys) = s≤s (monotone-⊑-≤ xs ys xs⊑ys)
monotone-⊑-≤ x .(_ ∷ _) (there {_} {_} {ys} x⊑ys) with monotone-⊑-≤ x ys x⊑ys
... | len[x]≤len[ys] = ≤-trans len[x]≤len[ys] (n≤1+n (length ys))

sum-length : {A : Set} → (List A × List A) → ℕ
sum-length (xs , ys) = length xs + length ys

infix 4 _⊰_

_⊰_ : {A : Set} → Rel (List A × List A) Level.zero
_⊰_ = _<_ on sum-length

⊰-well-founded : {A : Set} → Well-founded (_⊰_ {A})
⊰-well-founded = Inverse-image.well-founded sum-length <-well-founded

module _ {ℓ} {A} where
  open All (⊰-well-founded {A}) ℓ public renaming (wfRec-builder to ⊰-rec-builder ; wfRec to ⊰-rec)

⊰-left : ∀ {A} (x : A) → (xs ys : List A) → (xs , ys) ⊰ (x ∷ xs , ys)
⊰-left x xs ys = ≤-reflexive refl

⊰-right : ∀ {A} (y : A) → (xs ys : List A) → (xs , ys) ⊰ (xs , y ∷ ys)
⊰-right y xs ys = ≤-reflexive (sym  lem )
  where
    open ≡-Reasoning
    lem : sum-length (xs , y ∷ ys) ≡ suc (sum-length (xs , ys))
    lem =
      begin
        length xs + length (y ∷ ys)
      ≡⟨ refl ⟩
        length xs + suc (length ys)
      ≡⟨ +-suc (length xs) (length ys) ⟩
        suc (length xs + length ys)
      ∎

⊰-both :  ∀ {A} (x y : A) → (xs ys : List A) → (xs , ys) ⊰ (x ∷ xs , y ∷ ys)
⊰-both x y xs ys = <-trans lem1 lem2
  where
    lem1 : (xs , ys) ⊰ (x ∷ xs , ys)
    lem1 = ⊰-left y xs ys
    lem2 : (x ∷ xs , ys) ⊰ (x ∷ xs , y ∷ ys)
    lem2 = ⊰-right y (y ∷ xs) ys

P : ∀ p → Set
P (xs , ys) = ∀ zs → zs is-common-subseq-of (xs , ys) → length zs ≤ length (LCS xs ys)

step : ∀ p → (∀ q → q ⊰ p → P q) → P p
step ([] , _) rec .[] (empty , _) = z≤n
step (x ∷ xs , ys) rec zs prf = {!!}

theorem2 : ∀ xs ys zs → zs is-common-subseq-of (xs , ys) → length zs ≤ length (LCS xs ys)
theorem2 xs ys = ⊰-rec P step (xs , ys)

