module trees where

  data Tree (A : Set) : Set where
    empty : Tree A
    node : Tree A -> A -> Tree A -> Tree A

  open import Data.Nat

  #nodes : {A : Set} -> Tree A -> ℕ
  #nodes empty = 0
  #nodes (node t x t₁) = (#nodes t) + (1 + (#nodes t₁))

  #leafs : {A : Set} -> Tree A -> ℕ
  #leafs empty = zero
  -- #leafs (node empty x empty) = 1
  #leafs (node t x t₁) with t | t₁
  ...                     | empty | empty = 1
  ...                     | _     | _ = (#leafs t) + (#leafs t₁)

