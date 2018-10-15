{-# OPTIONS --verbose=10 #-}

module trees where


  data Tree (A : Set) : Set where
    empty : Tree A
    node : Tree A -> A -> Tree A -> Tree A

  {- Inorder traversal -}

  open import Data.Nat
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
  ...                              | (n₁ , (g₁ , p₁)) | (n₂ , (g₂ , p₂)) =
    (n₁ + (1 + n₂) , (g₁ ++ (x ∷ g₂) ,
      λ v -> node (p₁ (take n₁ v)) (head (drop n₁ v)) (righttree v)))
      where
        righttree :  Vec A (n₁ + (1 + n₂)) -> Tree A
        -- righttree v = p₂ (drop 1 (drop n₁ v))
        righttree v rewrite +-suc n₁ n₂ = p₂ (drop (1 + n₁) v)
    
  inorder : {A : Set} -> Traversal (Tree A) (Tree A) A A
  inorder = record{ extract = inorderTree }
                            
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

{-
open import Data.Maybe
open import Agda.Builtin.Sigma 
open import Data.Nat
open import Data.Vec renaming ( _∷_ to _::_ )
open import Data.Product

extractLeafs : forall {A B} -> (A -> B) -> Tree A -> Σ[ n ∈ ℕ ] Vec A n × (Vec B n -> Tree B)
extractLeafs _ t[] = (0 , ([] , \_ -> t[]))
extractLeafs _ t[ t[] , a , t[] ] = (1 , (a :: [] , \v -> t[ t[] , head v , t[] ]))
extractLeafs h t[ l , a , r ] with extractLeafs h l | extractLeafs h r
... | (n , (leafsl , putleafsl)) | (m , (leafsr , putleafsr)) =
  (n + m ,
    (leafsl ++ leafsr ,
      \v -> t[ putleafsl (take n v) , h a , putleafsr (drop n v) ]))

#leafs : forall {A} -> Tree A -> ℕ
#leafs t[] = 0
#leafs t[ t , x , t₁ ] = #leafs t + #leafs t₁

-}

