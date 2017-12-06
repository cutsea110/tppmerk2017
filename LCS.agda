module LCS where

open import Data.Nat
open import Data.List
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
