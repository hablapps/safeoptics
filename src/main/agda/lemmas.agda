{-# OPTIONS --verbose=10 #-}

module lemmas where

  open import Data.Nat
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
  
  +-suc : (n₁ n₂ : ℕ) -> (n₁ + (1 + n₂)) ≡ (1 + (n₁ + n₂))
  +-suc zero n2 = refl
  +-suc (suc n1) n2 rewrite +-suc n1 n2 = refl
