Require Import Arith.
Require Import Coq.Strings.String.

Class EqBool (A : Type) :=
  {
    eqb : A -> A -> bool;
    eqb_liebniz : forall x y, eqb x y = true -> x = y;
    eqb_refl : forall x, eqb x x = true
  }.
Global Opaque eqb.

Global Instance NatEqB : EqBool nat :=
  {
    eqb := Nat.eqb;
    eqb_liebniz := fun x y => proj1 (Nat.eqb_eq x y);
    eqb_refl := fun x => proj2 (Nat.eqb_eq x x) eq_refl
  }.


Section BoolEqB.
  Definition bool_eqb (b1 b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false =>
        match b2 with
        | true => false
        | false => true
        end
    end.
  Theorem bool_eqb_liebniz : forall x y, bool_eqb x y = true -> x = y.
  Proof using.
    intro x; destruct x; intro y; [|destruct y]; auto.
  Qed.
  Theorem bool_eqb_refl : forall x, bool_eqb x x = true.
  Proof using.
    intro x; destruct x; cbn; reflexivity.
  Qed.
  
  Global Instance BoolEqB : EqBool bool :=
    {
      eqb := bool_eqb;
      eqb_liebniz := bool_eqb_liebniz;
      eqb_refl := bool_eqb_refl
    }.
End BoolEqB.

Section PairEqB.
  Context {A B : Type} `{EqBool A} `{EqBool B}.

  Definition pair_eqb (p1 p2 : A * B) : bool :=
    match p1, p2 with
    | (a1, b1), (a2, b2) => eqb a1 a2 && eqb b1 b2
    end.
  
  #[global] Program Instance PairEqB : EqBool (A * B) :=
    {
      eqb := pair_eqb;
    }.
  Next Obligation.
    cbn in H1. apply andb_prop in H1; destruct H1.
    apply eqb_liebniz in H1; apply eqb_liebniz in H2.
    subst; reflexivity.
  Defined.
  Next Obligation.
    cbn; repeat rewrite eqb_refl; reflexivity.
  Defined.
  
End PairEqB.

Section ListEqB.
  Context {A : Type} `{EqBA : EqBool A}.

  Fixpoint list_eqb (l1 l2 : list A) : bool :=
    match l1 with
    | nil =>
        match l2 with
        | nil => true
        | _ => false
        end
    | cons a l1 =>
        match l2 with
        | nil => false
        | cons b l2 =>
            eqb a b && list_eqb l1 l2
        end
    end.

  Lemma list_eqb_spec : forall l1 l2 : list A, list_eqb l1 l2 = true <-> l1 = l2.
  Proof using.
    intro l1; induction l1 as [| a l1]; destruct l2 as [| b l2]; cbn;
      split; intro H; auto; try discriminate.
    apply andb_prop in H; destruct H.
    apply IHl1 in H0. apply eqb_liebniz in H. subst; auto.
    apply andb_true_intro; split. inversion H; subst; apply eqb_refl. 
    apply <- IHl1; inversion H; auto.
  Qed.
  
  Global Instance ListEqb : EqBool (list A) :=
    {
      eqb := list_eqb;
      eqb_liebniz := fun l1 l2 => proj1 (list_eqb_spec l1 l2);
      eqb_refl := fun l => proj2 (list_eqb_spec l l) eq_refl
    }.
End ListEqB.

Section StringEqB.
  
  Lemma string_eqb_liebniz : forall s1 s2 : string, String.eqb s1 s2 = true -> s1 = s2.
  Proof using.
    intros s1 s2; pose proof (eqb_spec s1 s2) as H.
    inversion H; subst; intro H'; [reflexivity | inversion H'].
  Qed.

  Global Instance StringEqB : EqBool string :=
    {
      eqb := String.eqb;
      eqb_liebniz := string_eqb_liebniz;
      eqb_refl := String.eqb_refl;
    }.
  
End StringEqB.

Section EqBoolLemmas.
  Context {A : Type} `{EqBA : EqBool A}.

  Lemma eq_to_eqb : forall (x y : A), x = y -> eqb x y = true.
  Proof using.
    intros x y eq; subst; apply eqb_refl.
  Qed.
  Lemma neq_to_eqb : forall (x y : A), x <> y -> eqb x y = false.
  Proof using.
    intros x y neq. destruct (eqb x y) eqn: eq; auto.
    exfalso; apply neq; apply eqb_liebniz; auto.
  Qed.
  Lemma eqb_liebniz_false : forall (x y : A), eqb x y = false -> x <> y.
  Proof using.
    intros x y eqb_eq eq; subst. rewrite eqb_refl in eqb_eq; inversion eqb_eq.
  Qed.

  Definition eq_dec : forall (x y : A),  {x = y} + {x <> y}.
  Proof using A EqBA.
    intros x y;  destruct (eqb x y) eqn:H.
    apply eqb_liebniz in H; left; auto.
    apply eqb_liebniz_false in H; right; auto.
  Defined.

  Lemma eqb_sym : forall (x y : A), eqb x y = eqb y x.
  Proof using A EqBA.
    intros x y. destruct (eqb x y) eqn:H.
    - apply eqb_liebniz in H; subst; symmetry; apply eqb_refl.
    - apply eqb_liebniz_false in H; symmetry; apply neq_to_eqb; auto.
  Qed.

End EqBoolLemmas.

Open Scope bool_scope.

Ltac eq_bool :=
  repeat match goal with
    (* Take care of assumptions first so that we can use the results when taking care of the conclusion *)
    | [ H : context[true && _] |- _ ] => rewrite Bool.andb_true_l in H
    | [ H : context[_ && true] |- _ ] => rewrite Bool.andb_true_r in H
    | [ H : context[false && _] |- _ ] => rewrite Bool.andb_false_l in H
    | [ H : context[_ && false] |- _ ] => rewrite Bool.andb_false_r in H
    | [ |- context[true && _]] => rewrite Bool.andb_true_l
    | [ |- context[_ && true]] => rewrite Bool.andb_true_r
    | [ |- context[false && _]] => rewrite Bool.andb_false_l
    | [ |- context[_ && false]] => rewrite Bool.andb_false_r
    | [ H : context[eqb ?a ?b] |- _ ] =>
        lazymatch type of H with
        | eqb a b = true => (* This is a record that a and b are equal *)
            lazymatch goal with
            | [H' : a <> b |- _ ] => (* If we assumed a and b are unequal, we're done *)
                destruct (H' (eqb_liebniz a b H))
            | [H' : b <> a |- _ ] =>
                destruct (H' (eq_sym (eqb_liebniz a b H)))
            | [H' : a = b |- _ ] => fail (* If we already assumed a and b are equal, we can't learn more from this *)
            | [H' : b = a |- _ ] => fail
            | _ => pose proof (eqb_liebniz a b H) (* We get that a and b are equal *)
            end
        | eqb a b = false => (* This is the dual of the previous branch *)
            lazymatch goal with
            | [H' : a = b |- _ ] =>
                destruct (eqb_liebniz_false a b H H')
            | [H' : b = a |- _ ] =>
                destruct (eqb_liebniz_false a b H (eq_sym H'))
            | [H' : a <> b |- _ ] => fail
            | [H' : b <> a |- _ ] => fail
            | _ => pose proof (eqb_liebniz_false a b H)
            end
        | _ => (* eqb is part of a longer goal. We need to break it down. *)
            tryif unify a b (* a and b are syntactically equal already *)
            then rewrite (eqb_refl a) in H (* a chosen arbitrarily *)
            else
              lazymatch goal with
              (* | [ H' : eqb a b = true |- _] => (* we've recorded the call, but not the meaning yet *) *)
              (*   rewrite H' in H *)
              (* | [ H' : eqb a b = false |- _ ] => *)
              (*   rewrite H' in H *)
              (* | [ H' : eqb b a = true |- _ ] => *)
              (*   rewrite (eqb_sym a b) in H; rewrite H' in H *)
              (* | [ H' : eqb b a = false |- _ ] => *)
              (*   rewrite (eqb_sym a b) in H; rewrite H' in H *)
              | [ H' : a = b |- _ ] => (* a and b are equal *)
                  rewrite (eq_to_eqb a b H') in H
              | [ H' : b = a |- _ ] =>
                  rewrite (eq_to_eqb a b (eq_sym H')) in H
              | [ H' : a <> b |- _ ] => (* a and b are unequal *)
                  rewrite (neq_to_eqb a b H') in H
              | [ H' : b <> a |- _ ] =>
                  rewrite (neq_to_eqb a b (fun e : a = b => H' (eq_sym e))) in H
              | _ => (* None of the above applies, we need to destruct the call *)
                  let e1 := fresh "e" in
                  let e2 := fresh "eq" in
                  let n := fresh "neq" in
                  destruct (eqb a b) eqn:e1;
                  [
                    pose proof (eqb_liebniz a b e1) as e2
                  | pose proof (eqb_liebniz_false a b e1) as n
                  ]
              end
        end
    | [ |- context[eqb ?a ?b]] => (* Very similar to the last case above, but in the goal *)
        tryif unify a b
        then rewrite (eqb_refl a)
        else
          lazymatch goal with
          | [ H : eqb a b = true |- _ ] => rewrite H
          | [ H : eqb b a = true |- _ ] => rewrite (eqb_sym a b); rewrite H
          | [ H : eqb a b = false |- _ ] => rewrite H
          | [ H : eqb b a = false |- _ ] => rewrite (eqb_sym a b); rewrite H
          | [ H : a = b |- _ ] =>
              rewrite (eqb_liebniz a b H)
          | [ H : b = a |- _ ] =>
              rewrite (eqb_liebniz b a (eq_sym H))
          | [ H : a <> b |- _ ] =>
              rewrite (eqb_liebniz_false a b H)
          | [ H : b <> a |- _ ] =>
              rewrite (eqb_liebniz_false a b (fun e : a = b => H (eq_sym e)))
          | _ =>
              let e1 := fresh "e" in
              let e2 := fresh "eq" in
              let n := fresh "neq" in
              destruct (eqb a b) eqn:e1;
              [ pose proof (eqb_liebniz a b e1) as e2
              | pose proof (eqb_liebniz_false a b e1) as n
              ]
          end
    end.

Ltac solve_eqb_liebniz x :=
  let y := fresh "y" in
  let H := fresh "H" in
    induction x; intro y; destruct y; cbn; intro H;
    repeat match goal with
      | [ |- ?a = ?a ] => reflexivity
      | [ H : false = true |- _ ] => inversion H
      | [ H : eqb ?x ?y = true |- _ ] => eq_bool; subst; clear H
      | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
      | [ IH : forall y, ?eq_b ?x y = true -> ?x = y, H : ?eq_b ?x ?y = true |- _ ] =>
          apply IH in H; subst
      end.

Ltac solve_eqb_refl :=
  match goal with
  | [ |- ?eq_b ?x ?x = true ] =>
      induction x; cbn; 
      repeat match goal with
        | [|- ?a = ?a ] => reflexivity
        | [IH : eq_b ?x ?y = true |- context[eq_b ?x ?y] ] => rewrite IH; cbn
        | [ |- context[eqb] ] => eq_bool; subst
        end
  end.
