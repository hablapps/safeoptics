{-# OPTIONS --verbose=10 #-}

module leafs where

  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)

  open import trees
  open import optics
  open import lemmas  
 
  leafsTree : {A : Set} -> Tree A -> ∃[ n ] (Vec A n × (Vec A n -> Tree A))
  leafsTree empty = 0 , ([] , λ _ -> empty)
  leafsTree (node empty root empty) =
    (1 , (root ∷ [] , λ v -> node empty (head v) empty))
  leafsTree {A} (node left root right) with leafsTree left | leafsTree right
  ...                                     | (n1 , (g1 , p1)) | (n2 , (g2 , p2)) =
     (n1 + n2 , (g1 ++ g2 , λ v -> node (p1 (take n1 v)) root (p2 (drop n1 v))))

  leafs : {A : Set} -> Traversal (Tree A) (Tree A) A A
  leafs = record{ extract = leafsTree }

  module tests where
    tree1 : Tree ℕ
    tree1 = node (node empty 1 empty) 3 empty

    open Traversal
  
    leafs1 : Vec ℕ 1
    leafs1 = get leafs tree1
  
    updatedleafs1 : Tree ℕ
    updatedleafs1 = put leafs (node tree1 5 tree1) (2 ∷ 5 ∷ [])
  
