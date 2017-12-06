module LCS where

open import Data.Nat
open import Data.List

LCS : List ℕ → List ℕ → List ℕ
LCS [] ys = []
LCS (_ ∷ _) [] = []
LCS (x ∷ xs) (y ∷ ys) with x ≟ y
... | p = ?
