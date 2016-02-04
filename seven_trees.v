Require Export Program.

Record iso (A B : Type) :=
  mk_iso
    {
      fw : A -> B;
      bw : B -> A;

      fw_bw: forall x, fw (bw x) = x;
      bw_fw: forall x, bw (fw x) = x
    }.

Ltac de_iso := match goal with
                 | [ H : iso _ _ |- _ ] => destruct H; de_iso
                 | _ => idtac
               end.

Ltac mk_iso := refine {| fw := _ |}.

Ltac simpl_goal := match goal with
                     | [ H : Empty_set |- _ ] => destruct H
                     | [ H : () |- _ ] => destruct H; simpl_goal
                     | _ => dintuition
                   end.

Ltac work_iso := intuition; simpl; simpl_goal; congruence.

Ltac iso := intuition; de_iso; mk_iso; work_iso.

Definition iso_refl {A}: iso A A.
  iso. Defined.

Definition iso_trans {A} {B} {C}: iso A B -> iso B C -> iso A C.
  iso. Defined.

Definition iso_sym {A} {B}: iso A B -> iso B A.
  iso. Defined.

Definition prod_unit {A}: iso (A * ()) A.
  iso. Defined.

Definition prod_swap {A} {B}: iso (A * B) (B * A).
  iso. Defined.

Definition prod_fst {A} {B} {C}: iso A B -> iso (A * C) (B * C).
  iso. Defined.

Definition prod_snd {A} {B} {C}: iso A B -> iso (C * A) (C * B).
  iso. Defined.

Definition prod_assoc {A} {B} {C}: iso (A * (B * C)) (A * B * C).
  iso. Defined.

Definition sum_swap {A} {B}: iso (A + B) (B + A).
  iso. Defined.

Definition sum_fst {A} {B} {C}: iso A B -> iso (A + C) (B + C).
  iso. Defined.

Definition sum_snd {A} {B} {C}: iso A B -> iso (C + A) (C + B).
  iso. Defined.

Definition sum_empty {A} : iso (A + Empty_set) A.
  iso. Defined.

Definition sum_assoc {A} {B} {C}: iso (A + (B + C)) (A + B + C).
  iso. Defined.

Definition prod_sum {A} {B} {C}: iso (C * (A + B)) (C * A + C * B).
  iso. Defined.

Inductive tree : Type :=
  leaf | branch (lc rc : tree).

Definition iso_tree : iso tree (() + (tree * tree)).
  refine
    {| fw := fun tr => match tr with
                         | leaf => inl tt
                         | branch lc rc => inr (pair lc rc)
                       end;

       bw := fun x => match x with
                        | inl tt => leaf
                        | inr (pair lc rc) => branch lc rc
                      end
    |}; dintuition; simpl_goal.
  
  - destruct x; reflexivity.
Defined.

Ltac tr := eapply iso_trans.

Ltac fst := match goal with
              | [ |- iso (_ * _) _ ] => eapply prod_fst
              | [ |- iso (_ + _) _ ]=> eapply sum_fst
            end.

Ltac snd := match goal with
              | [ |- iso (_ * _) _ ] => eapply prod_snd
              | [ |- iso (_ + _) _ ]=> eapply sum_snd
            end.

Ltac swp := match goal with
              | [ |- iso (_ * _) _ ] => eapply prod_swap
              | [ |- iso (_ + _) _ ]=> eapply sum_swap
            end.

Ltac asc := match goal with
              | [ |- iso (_ * _) _ ] => eapply prod_assoc
              | [ |- iso (_ + _) _ ]=> eapply sum_assoc
            end.

Ltac unt := match goal with
              | [ |- iso (_ * _) _ ] => eapply prod_unit
              | [ |- iso (_ + _) _ ]=> eapply sum_empty
            end.

Ltac sym := eapply iso_sym.

Ltac ist := eapply iso_tree.
Ltac dst := eapply prod_sum.

Fixpoint texp (T : Type) (n : nat) : Type :=
  match n with
    | 0 => unit
    | S n' => (texp T n') * T
  end.

Infix "^" := texp (at level 30, right associativity).

Lemma tree_split : forall n, iso (tree^S n) (tree^n + tree^S (S n)).
  induction n; simpl in *.
  - tr.
    { swp. }
    tr.
    { unt. }
    sym.
    tr.
    { snd. fst. swp. }
    tr.
    { snd. fst. unt. }
    sym.
    exact iso_tree.
  - sym.
    tr.
    { fst. swp. }
    tr.
    { snd. swp. }
    tr.
    { sym. dst. }
    sym.
    tr.
    { swp. }
    snd.
    assumption.
Defined.

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
Defined.
