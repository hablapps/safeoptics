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
  
  inorder : {A : Set} -> TraversalF (Tree A) (Tree A) A A #nodes
  inorder {A} = record{ get = inorderGet ; put = inorderPut }
    where
      inorderGet : {A : Set} -> (t : Tree A) -> Vec A (#nodes t)
      inorderGet empty = []
      inorderGet (node t₁ x t₂) = inorderGet t₁ ++ (x ∷ inorderGet t₂)

      inorderPut : {A : Set} -> (t : Tree A) -> Vec A (#nodes t) -> Tree A
      inorderPut empty _ = empty
      inorderPut {A} (node t₁ x t₂) v =
        node (p₁ (take n₁ v)) (head (drop n₁ v)) (p₂ (drop 1 (drop n₁ v))) -- (righttree v)
        where
          p₁ = inorderPut t₁
          p₂ = inorderPut t₂
          n₁ = #nodes t₁
          -- n  = #nodes (node t₁ x t₂)
          -- n₂ = #nodes t₂
          -- righttree :  Vec A n -> Tree A
          -- righttree v rewrite +-suc n₁ n₂ = p₂ (drop (1 + n₁) v)

  module tests where
    tree1 : Tree ℕ
    tree1 = node (node empty 1 (leaf 2)) 3 (node (leaf 4) 5 (leaf 6))

    open TraversalF

    inorder1 : Vec ℕ 6
    inorder1 = get inorder tree1

    tree2 : Tree ℕ
    tree2 = put inorder tree1 (6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  
