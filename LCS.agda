module LCS where

open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Nullary

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

LCS[xs,ys]⊑xs : ∀ xs ys → LCS xs ys ⊑ xs
LCS[xs,ys]⊑xs = {!!}

LCS[xs,ys]⊑ys : ∀ xs ys → LCS xs ys ⊑ ys
LCS[xs,ys]⊑ys = {!!}

theorem1 : ∀ xs ys → LCS xs ys is-common-subseq-of (xs , ys)
theorem1 xs ys = LCS[xs,ys]⊑xs xs ys , LCS[xs,ys]⊑ys xs ys
