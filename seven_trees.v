Require Export Setoid Ring Ring_theory.

Open Scope type_scope.

Inductive sum (A B : Set) : Set :=
  inl (x : A) | inr (x : B).

Inductive prod (A B : Set) : Set :=
  pair (x : A) (y : B).

Infix "+" := sum (at level 50, left associativity) : type_scope.
Infix "*" := prod (at level 40, left associativity) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

(* iso A B: Types A and B are isomorphic *)
Definition iso (A B : Set) : Prop :=
  exists (fw : A -> B) (bw : B -> A),
    (forall x, fw (bw x) = x) /\ (forall x, bw (fw x) = x).

(* Tactic iso for automagically solving (some) iso A B goals *)
Ltac de_iso := match goal with
                 | [ H : iso _ _ |- _ ] =>
                   let fw := fresh "fw" in
                   let bw := fresh "bw" in
                   let fw_bw := fresh "fw_bw" in
                   let bw_fw := fresh "bw_fw" in
                   destruct H as [fw [bw [fw_bw bw_fw]]]; de_iso
                 | _ => idtac
               end.

Ltac mk_iso := simple refine (ex_intro _ _ (ex_intro _ _ (conj _ _))).

Ltac simpl_goal := match goal with
                     | [ H : unit |- _ ] => destruct H; simpl_goal
                     | _ => dintuition
                   end.

Ltac work_iso := dintuition; simpl; simpl_goal; congruence.

Ltac iso := dintuition; de_iso; mk_iso; work_iso.

(* The actual relations *)
Add Parametric Relation : Set iso
    reflexivity proved by ltac:(unfold Reflexive; iso)
    symmetry proved by ltac:(unfold Symmetric; iso)
    transitivity proved by ltac:(unfold Transitive; iso)
      as iso_rel.

Add Parametric Morphism : sum
    with signature iso ==> iso ==> iso as sum_mor.
  iso. Qed.

Add Parametric Morphism : prod
    with signature iso ==> iso ==> iso as prod_mor.
  iso. Qed.

Definition iso_ring_theory : semi_ring_theory Empty_set unit sum prod iso.
  iso. Qed.

Add Ring iso_ring : iso_ring_theory.

Inductive tree : Set := mk_tree (x : unit + tree * tree).

Definition get_tree (t : tree) :=
  match t with mk_tree x => x end.

Hint Constructors tree.
Hint Resolve get_tree.

Lemma iso_tree : iso tree (unit + tree * tree).
  exists get_tree.
  exists mk_tree.
  intuition.
  destruct x.
  reflexivity.
Qed.

Hint Resolve iso_tree.

Fixpoint exps (T : Set) (n : nat) : Set :=
  match n with
    | 0 => unit
    | S n' => (exps T n') * T
  end.

Infix "^" := exps (at level 30, right associativity). 

Lemma tree_split : forall n, iso (tree^S n) (tree^n + tree^S (S n)).
  induction n.
  simpl in *.
  ring_simplify.
  auto.
  simpl in *.
  rewrite IHn at 1.
  ring.
Qed.

Ltac split_tree n :=
  match n with
      S ?n' => rewrite (tree_split n') at 1
  end.

Ltac combine_tree n :=
  match n with
      S ?n' => rewrite <- (tree_split n') at 1
  end.

Lemma tree_lower_3 : forall n, iso (tree^S n + tree^(4 + n))
                                   (tree^n     + tree^(3 + n)).
  intro. split_tree (S n).
  transitivity (tree^S (S n) + tree^(4+n) + tree^n).
  - ring.
  - unfold plus.
    combine_tree (S (S (S n))).
    ring.
Qed.

Theorem seven_trees : iso (tree^7) (tree^1).
Proof.
  Load "seven_search".
Qed.
