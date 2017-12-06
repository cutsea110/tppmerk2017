module LCS where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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

x⊑y→len[x]≤len[y] : ∀ x y → x ⊑ y → length x ≤ length y
x⊑y→len[x]≤len[y] .[] y empty = z≤n
x⊑y→len[x]≤len[y] .(_ ∷ _) .(_ ∷ _) (here {_} {xs} {ys} xs⊑ys) = s≤s (x⊑y→len[x]≤len[y] xs ys xs⊑ys)
x⊑y→len[x]≤len[y] x .(_ ∷ _) (there {_} {_} {ys} x⊑ys) with x⊑y→len[x]≤len[y] x ys x⊑ys
... | len[x]≤len[ys] = ≤-trans len[x]≤len[ys] (n≤1+n (length ys))

theorem2 : ∀ xs ys zs → zs is-common-subseq-of (xs , ys) → length zs ≤ length (LCS xs ys)
theorem2 xs ys zs (zs⊑xs , zs⊑ys) = {!!}
