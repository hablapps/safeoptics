{-# OPTIONS --verbose=10 #-}

module leafsF where

  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)

  open import trees
  open import optics
  open import lemmas  

  leafsTreeF : {A : Set} -> (t : Tree A) -> Vec A (#leafs t) × (Vec A (#leafs t) -> Tree A) 
  leafsTreeF empty = ([] , λ _ -> empty)
  -- leafsTreeF (node empty root empty) = (root ∷ [] , λ { (hd ∷ []) -> node empty hd empty })
  leafsTreeF {A} (node t₁ x t₂) with t₁ | t₂
  ...                              | empty | empty = (x ∷ [] , λ { (hd ∷ []) -> node empty hd empty })
  leafsTreeF _ | node t11 x1 t12 | t2 with leafsTreeF (node t11 x1 t12) | leafsTreeF t2
  ...                                                  | (g₁ , p₁)     | (g₂ , p₂) =
      -- (g₁ ++ g₂ , λ v -> node (p₁ (take n₁ v)) x (p₂ (drop n₁ v)))
      ({!!} , λ v -> node (p₁ {!!}) x1 (p₂ {!!}))
      where
        n₁ = #leafs (node t11 x1 t12)
        n₂ = #leafs t2
  leafsTreeF (node t₁ x t₂)                   | _ | (node _ _ _) with leafsTreeF t₁ | leafsTreeF t₂ 
  ...                                                    | (g₁ , p₁)     | (g₂ , p₂) =
      -- (g₁ ++ g₂ , λ v -> node (p₁ (take n₁ v)) x (p₂ (drop n₁ v)))
      ({!!} , λ v -> node (p₁ {!!}) x (p₂ {!!}))
      where
        n₁ = #leafs t₁
        n₂ = #leafs t₂
    
  module tests where
    tree1 : Tree ℕ
    tree1 = node (node empty 1 empty) 3 empty

    open Traversal
