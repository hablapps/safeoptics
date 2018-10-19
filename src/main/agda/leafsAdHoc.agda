{-# OPTIONS --verbose=10 #-}

module leafsAdHoc where

  open import Data.Bool
  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)

  open import trees
  open import optics
  open import lemmas  
  
  record Leafs (A : Set) : Set where
    field
      get : (s : Tree A) -> Vec A (#leafs s)
      put : (s : Tree A) -> Vec A (#leafs s) -> Tree A

  update : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update empty _ = empty
  update (node t1 x t2) v with isLeaf (node t1 x t2)
  ...                         | true = node empty (head v) empty
  ...                         | false = node (update t1 (take (#leafs t1) v)) x (update t2 (drop (#leafs t1) v))

  update' : {A : Set} -> (s : Tree A) -> Vec A (#leafs'' s) -> Tree A
  update' empty _ = empty
  update' (node t1 x t2) v with isLeaf'' (node t1 x t2)
  ...                         | yes = {!!} -- node empty (head v) empty
  ...                         | no = {!!} -- node (update' t1 (take (#leafs' t1) v)) x (update' t2 (drop (#leafs' t1) v))

  update'' : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update'' t v with isLeaf'' t
  update'' empty [] | no = empty
  update'' (node .empty x .empty) (x₁ ∷ v) | yes = node empty x₁ empty
  update'' (node t x t₁) v | no = {!!} -- node (update t (take (#leafs t) v)) x (update t₁ (drop (#leafs t) v))

  update''' : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update''' empty _ = empty
  update''' (node t x t₁) v with isLeaf'' (node t x t₁)
  ...                          | yes = node empty (head v) empty
  ...                          | noL = node (update''' t (take (#leafs t) v)) x empty
  ...                          | noR = node empty x (update''' t (take (#leafs t) v))
  ...                          | noLR = node (update''' t (take (#leafs t) v)) x (update''' t₁ (drop (#leafs t) v))

  foo : {A : Set } -> Tree A -> ℕ
  foo t with isLeaf'' t 
  foo .(node empty _ empty) | yes = zero
  foo .empty | noE = {!!}
  foo .(node (node _ _ _) _ empty) | noL = {!!}
  foo .(node empty _ (node _ _ _)) | noR = {!!}
  foo .(node (node _ _ _) _ (node _ _ _)) | noLR = {!!} 
{-
  update : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update empty _ =
    empty
  update (node empty x empty) (x₁ ∷ v) =
    node empty x₁ empty 
  update (node empty x (node s₁ x₁ s₂)) v =
    node empty x (update (node s₁ x₁ s₂) v)
  update (node (node s x₁ s₂) x empty) v rewrite +-zero (#leafs (node s x₁ s₂)) =
    node (update (node s x₁ s₂) v) x empty
  update (node (node s x₁ s₂) x (node s₁ x₂ s₃)) v =
    {!!} -- node (update (node s x₁ s₂) (take (#leafs (node s x₁ s₂)) v)) x (update (node s₁ x₂ s₃) (drop (#leafs (node s x₁ s₂)) v))
-}


{-
  update : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update empty v = {!!} -- empty
  update (node empty x empty) v = {!!} -- node empty y empty
  update (node t₁ x t₂) v = {!!}
-}


{-
  update : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update empty _ =
    empty
  update (node t₁ x t₂) v with t₁ | t₂
  update (node t₁ x t₂) (x2 ∷ []) | empty | empty = node empty x2 empty 
  update (node t₁ x t₂) v | empty | node x2 x₁ x3 = 
    node empty x (update (node x2 x₁ x3) v)
  update (node t₁ x t₂) v | node x1 x₁ x3 | x2 = {!!}
-}
  
