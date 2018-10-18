{-# OPTIONS --verbose=10 #-}

module inorderF where

  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)

  open import trees
  open import optics
  open import lemmas  
  
  inorderTreeF : {A : Set} -> (t : Tree A) -> Vec A (#nodes t) × (Vec A (#nodes t) -> Tree A) 
  inorderTreeF empty = ([] , λ _ -> empty)
  inorderTreeF {A} (node t₁ x t₂) with inorderTreeF t₁ | inorderTreeF t₂ 
  ...                                | (g₁ , p₁)       | (g₂ , p₂) =
    (g₁ ++ (x ∷ g₂) , λ v -> node (p₁ (take n₁ v)) (head (drop n₁ v)) (righttree v))
    where
      n  = #nodes (node t₁ x t₂)
      n₁ = #nodes t₁
      n₂ = #nodes t₂
      righttree :  Vec A n -> Tree A
      righttree v rewrite +-suc n₁ n₂ = p₂ (drop (1 + n₁) v)
    
  inorderF : {A : Set} -> TraversalF (Tree A) (Tree A) A A
  inorderF = record{ extract = (#nodes , inorderTreeF) }

  module tests where
    tree1 : Tree ℕ
    tree1 = node (node empty 1 empty) 3 empty

    open Traversal
  
