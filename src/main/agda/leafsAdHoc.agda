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

  -- PLAIN VERSION
  
  get : {A : Set} -> (s : Tree A) -> Vec A (#leafs s)
  get empty = []
  get (node s x s₁) with isLeaf (node s x s₁)
  ...                  | true = x ∷ []
  ...                  | false = get s ++ get s₁

  update : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  update empty _ = empty
  update (node t1 x t2) v with isLeaf (node t1 x t2)
  update _ (head ∷ []) | true = node empty head empty
  ...                  | false = node updated1 x updated2
    where 
      updated1 = update t1 (take (#leafs t1) v)
      updated2 = update t2 (drop (#leafs t1) v)

  GetLeafs : (A : Set) -> Set
  GetLeafs A = (s : Tree A) -> Vec A (#leafs s)

  UpdateLeafs : (A : Set) -> Set
  UpdateLeafs A = (s : Tree A) -> Vec A (#leafs s) -> Tree A

  Leafs : {A : Set} -> GetLeafs A × UpdateLeafs A
  Leafs = (get , update)

  -- VERSION WITH VIEWS
  
  updateView : {A : Set} -> (s : Tree A) -> Vec A (#leafsView s) -> Tree A
  updateView empty _ = empty
  updateView (node t x t₁) v with isLeafView (node t x t₁)
  ...                          | yes = node empty (head v) empty
  ...                          | noL = node (updateView t (take (#leafsView t) v)) x empty
  ...                          | noR = node empty x (updateView t (take (#leafsView t) v))
  ...                          | noLR = node (updateView t (take (#leafsView t) v)) x (updateView t₁ (drop (#leafsView t) v))


  updateViewPat : {A : Set} -> (s : Tree A) -> Vec A (#leafsPat s) -> Tree A
  updateViewPat empty _ = empty
  updateViewPat (node t x t₁) v with isLeafView (node t x t₁)
  ...                          | yes = node empty (head v) empty
  ...                          | noL = node (updateViewPat t (take (#leafsPat t) v)) x empty
  ...                          | noR = node empty x (updateViewPat t (take (#leafsPat t) v))
  ...                          | noLR = node (updateViewPat t (take (#leafsPat t) v)) x (updateViewPat t₁ (drop (#leafsPat t) v))


  updateViewNoPat : {A : Set} -> (s : Tree A) -> Vec A (#leafs s) -> Tree A
  updateViewNoPat empty _ = empty
  updateViewNoPat (node t x t₁) v with isLeafView (node t x t₁)
  ...                          | yes = node empty (head v) empty
  ...                          | noL = node (updateViewNoPat t (take (#leafs t) v)) x empty
  ...                          | noR = node empty x (updateViewNoPat t (take (#leafs t) v))
  ...                          | noLR = node (updateViewNoPat t (take (#leafs t) v)) x (updateViewNoPat t₁ (drop (#leafs t) v))


