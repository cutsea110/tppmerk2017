module LCS where

open import Data.Nat
open import Data.List
open import Relation.Nullary

LCS : List ℕ → List ℕ → List ℕ
LCS [] ys = []
LCS (_ ∷ _) [] = []
LCS (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes x≡y = {!!}
... | no  x≢y = {!!}
