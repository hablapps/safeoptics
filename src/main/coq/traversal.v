Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.VectorDef.

Open Scope string_scope.
Open Scope nat_scope.
Open Scope program_scope.


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

Definition traversal' S A := traversal S S A A.

Class Functor f :=
{ fmap : forall A B, (A -> B) -> f A -> f B }.

Class FunctorDec f `{Functor f} :=
{ functor_id : forall A, fmap A _ id = id
; functor_compose : forall A B C (f : B -> C) (g : A -> B), 
    fmap _ _ (f ∘ g) = fmap _ _ f ∘ fmap _ _ g
}.

Class Comonad w `{FunctorDec w} :=
{ extract A (wa : w A) : A
; duplicate A (wa : w A) : w (w A)
}.

Class ComonadDec w `{Comonad w} :=
{ comonad_1 : forall A, extract _ ∘ duplicate A = id
; comonad_2 : forall A, fmap _ _ (extract _) ∘ duplicate A = id
; comonad_3 : forall A, duplicate _ ∘ duplicate A = fmap _ _ (duplicate _) ∘ duplicate _
}.

Definition BiStore A B T := result T A B.

Instance Functor_BiStore {A B} : Functor (BiStore A B) :=
{ fmap _ _ f res := mkResult (n res) (get res) (f ∘ put res) }.

Instance FunctorDec_BiStore {A B} : FunctorDec (BiStore A B).
Proof.
  constructor; auto.
  intros.
  apply functional_extensionality.
  intros.
  now destruct x.
Qed.

(* Notice the unique input [A] *)
Instance Comonad_BiStore {A} : Comonad (BiStore A A) :=
{ extract _ wa := put wa (get wa)
; duplicate _ wa := mkResult (n wa) (get wa) (fun bs => 
    mkResult (n wa) bs (fun bs2 => put wa bs2))
}.

Instance ComonadDec_BiStore {A} : ComonadDec (BiStore A A).
Proof. 
  constructor; 
    intros; 
    apply functional_extensionality; 
    intros; 
    now destruct x.
Qed.

Record traversalDec {S A} (tr : traversal' S A) :=
{ extractCoalg   : extract _   ∘ tr = id
; duplicateCoalg : duplicate _ ∘ tr = fmap _ _ tr ∘ tr
}.

(* XXX: these laws hold, but can't be defined at their own *)
(*
Record traversalDec {S A} (tr : traversal S S A A) :=
{ getPut : forall s, put (tr s) (get (tr s)) = s
; putGet : forall s v, get (tr (put (tr s) v)) = v
; putPut : forall s v1 v2, put (tr (put (tr s) v1)) v2 = put (tr s) v2
; wtf    : forall s v, n (tr s) = n (tr (put (tr s) v))
}.
*)

Definition getAll {S T A B} (tr : traversal S T A B) (s : S) : t A (n (tr s)) :=
  get (tr s).

Definition putAll {S T A B} (tr : traversal S T A B) (s : S) : (t B (n (tr s))) -> T :=
  put (tr s).

(* Examples *)

(* First & last traversal *)

Inductive person : Type :=
 | mkPerson : string -> string -> nat -> person.

Definition nameTr : traversal' person string := (fun s => 
  match s with
  | mkPerson first last age => mkResult _
      (cons _ first _ (cons _ last _ (nil _)))
      (fun bs => mkPerson (hd bs) (hd (tl bs)) (age))
  end).

(* XXX: don't know how to destruct vector (ill-typed error) *)
(*
Property cons_proof : 
  forall A (x : t A 1), x = cons _ (hd x) 0 (nil _).
Proof.
  intros.
  destruct x.
Qed.

Definition nameTrDec : traversalDec (nameTr).
Proof.
  constructor.
  - unfold compose.
    apply functional_extensionality.
    intros.
    now destruct x.
  - unfold compose.
    apply functional_extensionality.
    intros.
    destruct x.
    simpl.
    f_equal.
    unfold compose.
    apply functional_extensionality.
    intros.
    simpl.
    f_equal.
    destruct x.
Qed.
*)

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
