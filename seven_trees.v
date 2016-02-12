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

Lemma unit_unique : forall x : unit, x = tt.
  destruct x; reflexivity.
Qed.
  
(* Tactic iso for automagically solving (some) iso A B goals *)
Ltac prepare_iso := pose proof unit_unique; unfold iso in *.
Ltac mk_iso := simple refine (ex_intro _ _ (ex_intro _ _ (conj _ _))).
Ltac work_iso := intuition; simpl in *; congruence.
Ltac simpl_exists := match goal with
                       | H : exists _, _ |- _ => destruct H; simpl_exists
                       | |- _ => intuition
                     end.
Ltac iso := prepare_iso; intuition; simpl_exists; mk_iso; work_iso.

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
  split; iso. Qed.

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
  intro.
  simpl.
  rewrite iso_tree at 2.
  ring.
Qed.

Ltac split_tree n :=
  match n with
      S ?n' => rewrite (tree_split n') at 1
  end.

Theorem seven_trees : iso (tree^7) (tree^1).
Proof.
  Load "seven_search".
Qed.
