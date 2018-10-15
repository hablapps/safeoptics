module optics where

  open import Function
  open import Data.Nat
  open import Data.Vec
  open import Agda.Builtin.Sigma
  open import Data.Product
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
 
  record Traversal (S T A B : Set) : Set where
    field
      extract : S -> Σ[ n ∈ ℕ ] Vec A n × (Vec B n -> T)

    get : (s : S) -> Vec A (fst (extract s))
    get = fst ∘ snd ∘ extract

    put : (s : S) -> Vec B (fst (extract s)) -> T
    put = snd ∘ snd ∘ extract


  record TraversalLaws (S A : Set) (t : Traversal S S A A): Set where
    open Traversal t public
    field
      get-put-law : (s : S) -> (put s) (get s) ≡ s
      -- put-get-law : (s : S) -> (v : Vec A (fst (Traversal.extract t s))) ->
      --  (Traversal.get t (Traversal.put t s v)) ≡ {!!}

