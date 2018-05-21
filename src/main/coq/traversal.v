Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.VectorDef.

Open Scope string_scope.
Open Scope nat_scope.


(* Traversal definition and methods *)

Record result T A B := mkResult
{ n : nat
; get : t A n 
; put : t B n -> T
}.
Arguments mkResult [T A B].
Arguments n [T A B].
Arguments get [T A B].
Arguments put [T A B].

Definition traversal S T A B := S -> result T A B.

Definition getAll {S T A B} (tr : traversal S T A B) (s : S) : t A (n (tr s)) :=
  get (tr s).

Definition putAll {S T A B} (tr : traversal S T A B) (s : S) : (t B (n (tr s))) -> T :=
  put (tr s).


(* Examples *)

(* First & last traversal *)

Inductive person : Type :=
 | mkPerson : string -> string -> nat -> person.

Definition nameTr : traversal person person string string := (fun s => 
  match s with
  | mkPerson first last age => mkResult _
      (cons _ first _ (cons _ last _ (nil _)))
      (fun bs => mkPerson (hd bs) (hd (tl bs)) (age))
  end).

Example get_names :
  getAll nameTr (mkPerson "john" "doe" 40) = 
  cons string "john" 1 (cons string "doe" 0 (nil string)).
Proof. auto. Qed.

Example put_names :
  putAll nameTr (mkPerson "john" "doe" 40) (cons _ "jane" _ (cons _ "roe" _ (nil _))) =
  mkPerson "jane" "roe" 40.
Proof. auto. Qed.

(* Vector traversal *)

Definition vectorTr {A B n} : traversal (t A n) (t B n) A B :=
  fun s => mkResult _ s id.

Example get_as : forall B,
  @getAll _ _ _ B vectorTr (cons _ 1 _ (cons _ 2 _ (nil _))) =
  cons _ 1 _ (cons _ 2 _ (nil _)).
Proof. auto. Qed.

Example set_bs :
  putAll vectorTr (cons _ 1 _ (cons _ 2 _ (nil _))) (cons _ "a" _ (cons _ "b" _ (nil _))) =
  (cons _ "a" _ (cons _ "b" _ (nil _))).
Proof. auto. Qed.

(* Tree traversal *)

Inductive tree (A : Type) : Type :=
  | leaf : tree A
  | node : tree A -> A -> tree A -> tree A.

Property leq_n_Snplusm : forall n m, n <= S n + m.
Proof.
  intros.
  rewrite PeanoNat.Nat.add_succ_comm.
  apply PeanoNat.Nat.le_add_r.
Qed.

Fixpoint preorderTr {A B} (s : tree A) : result (tree B) A B := 
  match s with
  | leaf _ => mkResult 0 (nil _) (fun _ => leaf _)
  | node _ l a r => mkResult _
      (append (cons _ a _ (get (preorderTr l))) (get (preorderTr r)))
      (fun bs =>
        let lb := put (preorderTr l) (take _ (leq_n_Snplusm _ _) bs) in
        let rb := put (preorderTr r) (rev (take _ (Plus.le_plus_r _ _) (rev bs))) in
        let b  := last (take (S (n (@preorderTr A B l))) (Plus.le_plus_l _ _) bs) in
        node _ lb b rb)
  end.

Example preorderGet_node : 
  @getAll _ _ _ nat preorderTr (node _ (node _ (leaf _) 0 (leaf _)) 1 (node _ (leaf _) 2 (leaf _))) =
  cons _ 1 _ (cons _ 0 _ (cons _ 2 _ (nil _))).
Proof. auto. Qed.

Example preorderPut_node :
  putAll preorderTr (node _ (node _ (leaf _) 0 (leaf _)) 1 (node _ (leaf _) 2 (leaf _))) (cons _ 1 _ (cons _ 0 _ (cons _ 2 _ (nil _)))) =
  node _ (node _ (leaf _) 0 (leaf _)) 1 (node _ (leaf _) 2 (leaf _)).
Admitted.

Example preorderPut_node' :
  put (preorderTr (node _ (leaf _) 1 (node _ (leaf _) 2 (leaf _)))) (cons _ 0 _ (cons _ 2 _ (nil _))) =
  (node _ (leaf _) 0 (node _ (leaf _) 2 (leaf _))).
Admitted.


Require Import ZArith.

Example plus_O_mnO : 
  forall m n, m + n = 0 -> m = 0 /\ n = 0.
Proof.
  intros.
  constructor; induction n0; auto.
  - rewrite (plus_n_O m).
    apply H.
  - rewrite <- plus_n_Sm in H.
    inversion H. 
  - rewrite <- plus_n_Sm in H.
    inversion H.
Qed.

Example two_pow_n : 
  forall n, 2 ^ n <> 0.
Proof.
  induction n0; simpl; auto.
  unfold not in *.
  rewrite <- plus_n_O.
  intros.
  apply plus_O_mnO in H.
  destruct H.
  apply (IHn0 H).
Qed.

Example pred_notO_plus : 
  forall n m, n <> 0 -> pred (n + m) = pred n + m.
Proof.
  intros.
  destruct n0; simpl; auto.
  now destruct H.
Qed.

Example adhoc_nat : 
  forall n, pred (2 ^ n) + S (pred (2 ^ n)) = pred (2 ^ S n).
Proof.
  intros.
  rewrite Nat.succ_pred.
  - destruct n0; simpl; auto.
    repeat rewrite <- plus_n_O.
    assert (G : 2 ^ n0 + 2 ^ n0 <> 0).
    { unfold not.
      intros.
      destruct n0.
      + inversion H.
      + apply plus_O_mnO in H.
        destruct H.
        now apply two_pow_n in H.
    }
    now rewrite (pred_notO_plus (2 ^ n0 + 2 ^ n0) (2 ^ n0 + 2 ^ n0)).
  - apply two_pow_n.
Qed.

Inductive stree (A : Type) : nat -> Type :=
  | leaf : stree A 0
  | node {m} : stree A m -> A -> stree A m -> stree A (S m).

Property adhoc_vec : 
  forall A n, t A (pred (2 ^ n) + S (pred (2 ^ n))) -> t A (pred (2 ^ S n)).
Proof. intros. now rewrite <- adhoc_nat. Qed.

Fixpoint inorder {A m} (tr : stree A m) : t A (pred (2 ^ m)) :=
  match tr with
  | leaf _ => nil _
  | node _ l a r => adhoc_vec _ _ (append (inorder l) (cons _ a _ (inorder r)))
  end.

Example inorder_leaf : inorder (leaf nat) = nil nat.
Proof. auto. Qed.

Example inorder_node : inorder (node _ (node _ (leaf _) 0 (leaf _)) 1 (node _ (leaf _) 2 (leaf _))) =
                       cons _ 0 _ (cons _ 1 _ (cons _ 2 _ (nil _))).
(* XXX: ops, don't know how to expand [adhoc_vec] *)
Admitted.

Example inorderTr {A B m} : traversal (stree A m) (stree B m) A B := fun s => 
  match s with
  | leaf _ => mkResult 0 (nil A) (fun _ => leaf B)
  | node _ l a r => mkResult _ (inorder (node _ l a r)) (_)
  end.

(* Doesn't compile! (which is great) *)

(*
Example put_names :
  putAll nameTr (mkPerson "john" "doe" 40) (cons _ "jane" _ (nil _)) =
  mkPerson "jane" "roe" 40.
Example get_names' :
  getAll nameTr (mkPerson "john" "doe" 40) = 
  (cons string "john" 0 (nil string)).
*)
