module trees where

  data Tree (A : Set) : Set where
    empty : Tree A
    node : Tree A -> A -> Tree A -> Tree A

  open import Data.Nat

  leaf : {A : Set} -> A -> Tree A
  leaf a = node empty a empty

  #nodes : {A : Set} -> Tree A -> ℕ
  #nodes empty = 0
  #nodes (node t x t₁) = (#nodes t) + (1 + (#nodes t₁))

  -- Plain version
  
  #leafs' : {A : Set} -> Tree A -> ℕ
  #leafs' empty = zero
  #leafs' (node empty x empty) = 1
  #leafs' (node t x t₁) = #leafs' t + #leafs' t₁

  -- Version with boolean function isLeaf
  
  open import Data.Bool
  isLeaf : {A : Set} -> Tree A -> Bool
  isLeaf (node empty _ empty) = true
  isLeaf _ = false

  #leafs : {A : Set} -> Tree A -> ℕ
  #leafs empty = zero 
  #leafs (node t x t₁) with isLeaf (node t x t₁)
  ...                   | true = 1
  ...                   | false = #leafs t + #leafs t₁
  
  -- Version with view isLeaf 
  
  data IsLeaf (A : Set) : Tree A -> Set where
    yes : {x : A} -> IsLeaf A (node empty x empty)
    noE : IsLeaf A empty
    noL : {x x1 : A} -> {l1 r1 : Tree A} -> IsLeaf A (node (node l1 x1 r1) x empty)
    noR : {x x1 : A} -> {l1 r1 : Tree A} -> IsLeaf A (node empty x (node l1 x1 r1))
    noLR : {x x1 x2 : A} -> {l1 l2 r1 r2 : Tree A} -> IsLeaf A (node (node l1 x1 r1) x (node l2 x2 r2))

  isLeaf'' : {A : Set} -> (t : Tree A) -> IsLeaf A t
  isLeaf'' empty = noE
  isLeaf'' (node empty _ empty) = yes
  isLeaf'' (node empty x (node l1 x1 r1)) = noR
  isLeaf'' (node (node l1 x1 r1) x empty) = noL
  isLeaf'' (node (node l1 x1 r1) x (node l2 x2 r2)) = noLR

  #leafs'' : {A : Set} -> Tree A -> ℕ
  #leafs'' t with isLeaf'' t 
  #leafs'' empty | no = zero 
  #leafs'' (node .empty x .empty) | yes = 1
  #leafs'' (node t x t₁) | no = #leafs'' t + #leafs'' t₁
 



    
{-
  #leafs : {A : Set} -> Tree A -> ℕ
  #leafs empty = zero
  #leafs (node empty x empty) = 1
  #leafs (node empty x (node t₁ x₁ t₂)) = #leafs (node t₁ x₁ t₂)
  #leafs (node (node t x₁ t₂) x empty) = #leafs (node t x₁ t₂)
  #leafs (node (node t x₁ t₂) x (node t₁ x₂ t₃)) = #leafs (node t x₁ t₂) + #leafs (node t₁ x₂ t₃)
-}


{-
  #leafs : {A : Set} -> Tree A -> ℕ
  #leafs empty = zero
  #leafs (node t x t₁) with #leafs t | #leafs t₁
  ...                     | 0       | 0        = 1
  ...                     | n1      | n2       = n1 + n2
-}


{-
  #leafs : {A : Set} -> Tree A -> ℕ
  #leafs empty = zero
  #leafs (node t1 x t2) with t1 | t2 
  ...                   | empty | empty = 1
  ...                   | _     | _ = #leafs t1 + #leafs t2 
-}

