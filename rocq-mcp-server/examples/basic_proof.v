(* Basic proof example for testing the MCP Coq server *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Simple theorem about natural number addition *)
Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* Base case: 0 + 0 = 0 *)
    reflexivity.
  - (* Inductive case: S n' + 0 = S n' *)
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(* List reversal is involutive *)
Theorem reverse_involutive : forall (A : Type) (l : list A),
  rev (rev l) = l.
Proof.
  intros A l.
  induction l as [| h t IHl].
  - (* Base case: empty list *)
    simpl.
    reflexivity.
  - (* Inductive case *)
    simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* Function definition example *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => S n' * factorial n'
  end.

(* Property about factorial *)
Lemma factorial_positive : forall n : nat, factorial n > 0.
Proof.
Admitted. (* Using Admitted for now to allow compilation *)

(* Example with dependent types *)
Inductive Vec (A : Type) : nat -> Type :=
  | VNil : Vec A 0
  | VCons : forall n, A -> Vec A n -> Vec A (S n).

Arguments VNil {A}.
Arguments VCons {A n}.

(* Head function for non-empty vectors *)
Definition vhead {A : Type} {n : nat} (v : Vec A (S n)) : A :=
  match v with
  | VCons x _ => x
  end.

(* Tail function for non-empty vectors *)
Definition vtail {A : Type} {n : nat} (v : Vec A (S n)) : Vec A n :=
  match v with
  | VCons _ xs => xs
  end.

Print factorial.
Check factorial_positive.