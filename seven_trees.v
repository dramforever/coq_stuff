(* coq 8.5 *)
Require Export Setoid Ring Ring_theory.

(* iso A B: Types A and B are isomorphic *)
Definition iso (A B : Type) : Prop :=
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
Add Parametric Relation : Type iso
    reflexivity proved by ltac:(unfold Reflexive; iso)
    symmetry proved by ltac:(unfold Symmetric; iso)
    transitivity proved by ltac:(unfold Transitive; iso)
      as iso_rel.

Add Parametric Morphism : sum
    with signature iso ==> iso ==> iso as sum_mor_pp.
  iso. Qed.

Add Parametric Morphism : prod
    with signature iso ==> iso ==> iso as prod_mor.
  iso. Qed.

Definition iso_ring_theory : semi_ring_theory Empty_set unit sum prod iso.
  iso. Qed.

(* This one does not work, but I don't know why *)
Add Ring iso_ring : iso_ring_theory.
(* Error: cannot find setoid relation *)

Inductive tree := leaf | branch (l r : tree).

Lemma iso_tree : iso tree (unit + tree * tree).
  mk_iso.
  - intro t.
    exact match t with
            | leaf => inl tt
            | branch lc rc => inr (lc, rc)
          end.
  - intro m.
    exact match m with
            | inl tt => leaf
            | inr (lc, rc) => branch lc rc
          end.
  - repeat simpl_goal.
  - repeat simpl_goal.
    destruct x; reflexivity.
Qed.

Lemma tree_split : forall n, iso (tree^S n) (tree^n + tree^S (S n)).
Qed.

Ltac spl := eapply tree_split.

(* 
  7
= 6 8
= 6 9 7
= 5 7 9 7
= 5 8 7
= 4 6 8 7
= 4 7 7
= 3 5 7 7
= 3 6 7
= 2 4 6 7
= 2 5 7
= 1 3 5 7
= 1 3 6
= 1 2 4 6
= 1 2 5
= 1 1 3 5
= 1 1 4
= 1 0 2 4
= 1 0 3
= 0 2
= 1 

*)


Theorem seven_trees : iso (tree^7) tree.
Proof.
  tr.
  { spl. }
  tr.
  { snd. spl. }
  tr.
  { snd. swp. }
  tr.
  { asc. }
  do 4 (tr; [ do 2 fst; spl |];
        tr; [ fst; sym; eapply sum_assoc |];
        tr; [ fst; snd; sym; eapply tree_split |]).
  
  tr; [ sym; eapply sum_assoc |].
  tr; [ snd; sym; eapply tree_split |].
  tr; [ fst; spl |].

  do 3 (tr; [ fst; snd; spl |];
        tr; [ fst; asc |];
        tr; [ sym; eapply sum_assoc |];
        tr; [ snd; sym; eapply tree_split |]).

  tr; [ fst; swp |].
  tr; [ sym; eapply sum_assoc |].
  tr; [ snd; sym; eapply tree_split |].
  tr; [ sym; eapply tree_split |].
  simpl.
  tr; [ swp |].
  unt.
Qed.
