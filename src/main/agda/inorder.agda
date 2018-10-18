{-# OPTIONS --verbose=10 #-}

module inorder where
  
  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)

  open import trees
  open import optics
  open import lemmas  

  inorderTree : {A : Set} -> Tree A -> Σ[ n ∈ ℕ ] Vec A n × (Vec A n -> Tree A) 
  inorderTree empty = (0 , ([] , λ _ -> empty))
  inorderTree {A} (node t x t₁) with inorderTree t | inorderTree t₁ 
  ...                              | (n₁ , (g₁ , p₁)) | (n₂ , (g₂ , p₂)) =
    (n₁ + (1 + n₂) , (g₁ ++ (x ∷ g₂) ,
      λ v -> node (p₁ (take n₁ v)) (head (drop n₁ v)) (righttree v)))
      where
        righttree :  Vec A (n₁ + (1 + n₂)) -> Tree A
        -- righttree v = p₂ (drop 1 (drop n₁ v))
        righttree v rewrite +-suc n₁ n₂ = p₂ (drop (1 + n₁) v)
    
  inorder : {A : Set} -> Traversal (Tree A) (Tree A) A A
  inorder = record{ extract = inorderTree }

  module tests where
    tree1 : Tree ℕ
    tree1 = node (node empty 1 empty) 3 empty

    open Traversal
  
    inorder1 : Vec ℕ 2
    inorder1 = get inorder tree1 
  
    updatedinorder1 : Tree ℕ
    updatedinorder1 = put inorder tree1  (2 ∷ 3 ∷ [])

