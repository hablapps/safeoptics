{-# OPTIONS --verbose=10 #-}

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

  {- Inorder traversal -}

  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  open import Data.Fin using (fromℕ)
  open import optics

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
  
  +-suc : (n₁ n₂ : ℕ) -> (n₁ + (1 + n₂)) ≡ (1 + (n₁ + n₂))
  +-suc zero n2 = refl
  +-suc (suc n1) n2 rewrite +-suc n1 n2 = refl
    
  inorderTree : {A : Set} -> Tree A -> Σ[ n ∈ ℕ ] Vec A n × (Vec A n -> Tree A) 
  inorderTree empty = (0 , ([] , λ _ -> empty))
  inorderTree {A} (node t x t₁) with inorderTree t | inorderTree t₁ 
  ... | (n₁ , (g₁ , p₁)) | (n₂ , (g₂ , p₂)) =
    (n₁ + (1 + n₂) , (g₁ ++ (x ∷ g₂) ,
      λ v -> node (p₁ (take n₁ v)) (head (drop n₁ v)) (righttree v)))
      where
        righttree :  Vec A (n₁ + (1 + n₂)) -> Tree A
        -- righttree v = p₂ (drop 1 (drop n₁ v))
        righttree v rewrite +-suc n₁ n₂ = p₂ (drop (1 + n₁) v)
    
  inorder : {A : Set} -> Traversal (Tree A) (Tree A) A A
  inorder = record{ extract = inorderTree }

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

  leafsTree : {A : Set} -> Tree A -> ∃[ n ] (Vec A n × (Vec A n -> Tree A))
  leafsTree empty = 0 , ([] , λ _ -> empty)
  leafsTree (node empty root empty) =
    (1 , (root ∷ [] , λ v -> node empty (head v) empty))
  leafsTree {A} (node left root right) with leafsTree left | leafsTree right
  ...                                     | (n1 , (g1 , p1)) | (n2 , (g2 , p2)) =
     (n1 + n2 , (g1 ++ g2 , λ v -> node (p1 (take n1 v)) root (p2 (drop n1 v))))

  leafs : {A : Set} -> Traversal (Tree A) (Tree A) A A
  leafs = record{ extract = leafsTree }

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
  
    inorder1 : Vec ℕ 2
    inorder1 = get inorder tree1 
  
    updatedinorder1 : Tree ℕ
    updatedinorder1 = put inorder tree1  (2 ∷ 3 ∷ [])

    leafs1 : Vec ℕ 1
    leafs1 = get leafs tree1
  
    updatedleafs1 : Tree ℕ
    updatedleafs1 = put leafs (node tree1 5 tree1) (2 ∷ 5 ∷ [])
  
  module laws where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

    inorder-laws : {A : Set} -> TraversalLaws (Tree A) A inorder
    inorder-laws {A} = record {
      get-put-law = prf
      } where
      open Traversal inorder
      prf : (s : Tree A) -> (put s) (get s) ≡ s
      prf empty = refl
      prf (node s x s₁) = {!-t 15!}
      {-
      begin
      (put (node s x s₁)) (get (node s x s₁))
                 ∎ 
      -}
