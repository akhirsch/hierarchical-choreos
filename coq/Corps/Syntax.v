Require Import Base.EqBool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.
Import ListNotations.
From Stdlib Require Import Logic.JMeq.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Program.Wf.

Require Import Modalities.

Set Implicit Arguments.
Section CorpsSyntax.

  Context {PName : Type} `{EqBool PName}.
  #[local] Abbreviation mod := (@mod PName).
  #[local] Definition ptm := @proc_to_mod PName.
  #[local] Definition PrefixOfT := @PrefixOfT PName.
  Coercion ptm : PName >-> mod.

  Section CorpsTypes.

    Inductive type : Type :=
      UnitT
    | VoidT
    | AtT : PName -> type -> type
    | TimesT : type -> type -> type
    | PlusT : type -> type -> type
    | ArrT : type -> type -> type.

    Fixpoint typ_eqb (t1 t2 : type) : bool :=
      match t1, t2 with
      | UnitT, UnitT => true
      | VoidT, VoidT => true
      | AtT p t1, AtT q t2 => eqb p q && typ_eqb t1 t2
      | TimesT t11 t12, TimesT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | PlusT t11 t12, PlusT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | ArrT t11 t12, ArrT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | _, _ => false
      end.

    #[global] Program Instance TypEqB : EqBool type :=
      {
        eqb := typ_eqb
      }.
    Next Obligation.
      revert y H0; solve_eqb_liebniz x.
    Defined.
    Next Obligation.
      solve_eqb_refl.
    Defined.

  End CorpsTypes.

  Section CorpsTerms.

    Inductive expr : Type :=
      var : nat -> expr
    | uu : expr
    | atE (p : PName) (e : expr) : expr
    | letAt (p : PName) (e1 e2 : expr) : expr
    | pair (e1 e2 : expr) : expr
    | pi1 (e : expr)
    | pi2 (e : expr)
    | inl (e : expr)
    | inr (e : expr)
    | caseE (e1 e2 e3 : expr)
    | efql (e : expr) (* ex falso quod libet; exfalso is taken by coq *)
    | lam (t : type) (e : expr)
    | appE (e1 e2 : expr)
    | send (e : expr) (m : mod) (p : PName) (q : PName)
    | up (e : expr) (m : mod) (p : PName)
    | down (e : expr) (m : mod) (p : PName).

    Fixpoint expr_eqb (e1 e2 : expr) : bool :=
      match e1, e2 with
      | var n, var m => eqb n m
      | uu, uu => true
      | atE p e1, atE q e2 => eqb p q && expr_eqb e1 e2
      | letAt p e11 e12, letAt q e21 e22 => eqb p q && expr_eqb e11 e21 && expr_eqb e12 e22
      | pair e11 e12, pair e21 e22 => expr_eqb e11 e21 && expr_eqb e12 e22
      | pi1 e1, pi1 e2 => expr_eqb e1 e2
      | pi2 e1, pi2 e2 => expr_eqb e1 e2
      | inl e1, inl e2 => expr_eqb e1 e2
      | inr e1, inr e2 => expr_eqb e1 e2
      | caseE e11 e12 e13, caseE e21 e22 e23 =>
          expr_eqb e11 e21 && expr_eqb e12 e22 && expr_eqb e13 e23
      | efql e1, efql e2 => expr_eqb e1 e2
      | lam t1 e1, lam t2 e2 => eqb t1 t2 && expr_eqb e1 e2
      | appE e11 e12, appE e21 e22 => expr_eqb e11 e21 && expr_eqb e12 e22
      | send e1 m1 p1 q1, send e2 m2 p2 q2 =>
          expr_eqb e1 e2 && eqb m1 m2&& eqb p1 p2 && eqb q1 q2
      | up e1 m1 p1, up e2 m2 p2 =>
          expr_eqb e1 e2 && eqb m1 m2 && eqb p1 p2
      | down e1 m1 p1, down e2 m2 p2 =>
          expr_eqb e1 e2 && eqb m1 m2 && eqb p1 p2
      | _, _ => false 
      end.

    Theorem expr_eqb_liebniz : forall x y, expr_eqb x y = true -> x = y.
    Proof using.
      intro x; solve_eqb_liebniz x.
    Qed.

    Theorem expr_eqb_refl : forall x, expr_eqb x x = true.
    Proof using.
      intro x; solve_eqb_refl.
    Qed.
    
    #[global] Instance exprEqBool : EqBool expr :=
      {
        eqb := expr_eqb;
        eqb_liebniz := expr_eqb_liebniz;
        eqb_refl := expr_eqb_refl;
      }.

  End CorpsTerms.

  Section Renaming.

    Definition renaming : Type := nat -> nat.

    Definition id_renaming : renaming := fun n => n.

    Definition renup (ξ : renaming) : renaming :=
      fun n =>
        match n with
        | 0 => 0
        | S n => S (ξ n)
        end.

    Lemma renup_ext : forall (ξ1 ξ2 : renaming),
        (forall n, ξ1 n = ξ2 n) ->
        forall n, (renup ξ1) n = (renup ξ2) n.
    Proof using.
      intros ξ1 ξ2 ext_eq n; destruct n; cbn; [| rewrite ext_eq]; reflexivity.
    Qed.

    Lemma renup_id : forall n, (renup id_renaming) n = id_renaming n.
    Proof using.
      intro n; destruct n; unfold id_renaming; cbn; reflexivity.
    Qed.

    Lemma renup_fusion : forall ξ1 ξ2 : renaming,
      forall n, (fun n => renup ξ2 (renup ξ1 n)) n = renup (fun n => ξ2 (ξ1 n)) n.
    Proof using.
      intros ξ1 ξ2 n; destruct n; cbn; reflexivity.
    Qed.

    Lemma renup_id_below : forall ξ n,
        (forall m, m < n -> ξ m = m) ->
        forall m, m < S n -> renup ξ m = m.
    Proof using.
      intros ξ n id_bel m m_le_n; destruct m; cbn; [reflexivity|].
      rewrite id_bel; [reflexivity | lia].
    Qed.

    Fixpoint ren (e : expr) (ξ : renaming) : expr :=
      match e with
      | var x => var (ξ x)
      | uu => uu
      | atE p e => atE p (ren e ξ)
      | letAt p e1 e2 => letAt p (ren e1 ξ) (ren e2 (renup ξ))
      | pair e1 e2 => pair (ren e1 ξ) (ren e2 ξ)
      | pi1 e => pi1 (ren e ξ)
      | pi2 e => pi2 (ren e ξ)
      | inl e => inl (ren e ξ)
      | inr e => inr (ren e ξ)
      | caseE e1 e2 e3 => caseE (ren e1 ξ) (ren e2 (renup ξ)) (ren e3 (renup ξ))
      | efql e => efql (ren e ξ)
      | lam t e => lam t (ren e (renup ξ))
      | appE e1 e2 => appE (ren e1 ξ) (ren e2 ξ)
      | send e m p q => send (ren e ξ) m p q
      | up e m p => up (ren e ξ)  m p
      | down e m p => down (ren e ξ) m p
      end.
    
    Lemma ren_ext : forall (ξ1 ξ2 : renaming),
        (forall n, ξ1 n = ξ2 n) ->
        forall e, ren e ξ1 = ren e ξ2.
    Proof using.
      intros ξ1 ξ2 ext_eq e; revert ξ1 ξ2 ext_eq; induction e; intros ξ1 ξ2 ext_eq; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall n, ?f n = ?g n |- context [?f ?n]] => rewrite (H n)
          | [ IH : forall ξ1 ξ2, (forall n, ξ1 n = ξ2 n) -> ren ?e ξ1 = ren ?e ξ2,
                H : forall n, ?f n = ?g n |- context[ren ?e ?f]] =>
              rewrite (IH f g H)
          | [H : forall n, ?f n = ?g n |- context[renup ?f]] =>
              pose proof (renup_ext f g H)
          end.
    Qed.


    Lemma ren_id : forall e, ren e id_renaming = e.
    Proof using.
      intro e; induction e; cbn;
        repeat match goal with
          | [|- ?a = ?a ] => reflexivity
          | [|- context[id_renaming _]] => unfold id_renaming; cbn
          | [ H : ren ?e id_renaming = ?e |- context[ren ?e id_renaming]] => rewrite H
          | [ H : ren ?e id_renaming = ?e |- context[ren ?e (fun x => x)]] => unfold id_renaming in H; rewrite H
          | [|- context[ren ?e (renup id_renaming)]] =>
              rewrite (ren_ext (renup id_renaming) id_renaming renup_id e)
          end.
    Qed.

    Lemma ren_fusion : forall e ξ1 ξ2, ren (ren e ξ1) ξ2 = ren e (fun n => ξ2 (ξ1 n)).
    Proof using.
      intro e; induction e; intros ξ1 ξ2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ1 ξ2, ren (ren ?e ξ1) ξ2 = ren ?e (fun n => ξ2 (ξ1 n))
                            |-  context[ren (ren ?e ?f) ?g]] =>
              rewrite (IH f g)
          | [ |- context[ren ?e (fun n => renup ?g (renup ?f n))]] =>
              rewrite (ren_ext (fun n => renup g (renup f n)) (renup (fun n => g (f n)))
                         (renup_fusion f g) e)
          end.
    Qed.
  End Renaming.

  Section Substitution.

    Definition substitution : Type := nat -> expr.
    Definition id_substitution : substitution := var.

    Definition substup (σ : substitution) : substitution :=
      fun n =>
        match n with
        | 0 => var 0
        | S n => ren (σ n) S
        end.

    Lemma substup_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall n, substup σ1 n = substup σ2 n.
    Proof using.
      intros σ1 σ2 ext_eq n; destruct n; cbn; [|rewrite ext_eq]; reflexivity.
    Qed.

    Lemma id_substup :
      forall n, substup id_substitution n = id_substitution n.
    Proof using.
      intros n; destruct n; unfold id_substitution; cbn; reflexivity.
    Qed.

    Lemma renup_substup : forall ξ n,
        (fun n => var (renup ξ n)) n = substup (fun n => var (ξ n)) n.
    Proof using.
      intros ξ n; destruct n; cbn; reflexivity.
    Qed.

    Lemma substup_renup_fusion : forall ξ σ n,
        (fun n => substup σ (renup ξ n)) n = (substup (fun n => σ (ξ n))) n.
    Proof using.
      intros ξ σ n; destruct n; cbn; reflexivity.
    Qed.

    Lemma renup_substup_fusion : forall σ ξ n,
        (fun n => ren (substup σ n) (renup ξ)) n = (substup (fun n => ren (σ n) ξ)) n.
    Proof using.
      intros σ ξ n; destruct n; cbn; [reflexivity|].
      repeat rewrite ren_fusion; unfold renup; reflexivity.
    Qed.

    Lemma substup_id_below : forall σ n,
        (forall m, m < n -> σ m = var m) ->
        forall m, m < S n -> substup σ m = var m.
    Proof using.
      intros σ n id_below m m_lt_Sn; destruct m; cbn; [reflexivity|].
      rewrite id_below; [reflexivity|].
      lia.
    Qed.

    Definition option_bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
      match x with
      | Some a => f a
      | None => None
      end.

    #[local] Notation "x >>= f" := (option_bind x f) (at level 10).

    Fixpoint subst (e : expr) (σ : substitution) : expr :=
      match e with
      | var x => σ x
      | uu => uu
      | atE p e => atE p (subst e σ)
      | letAt p e1 e2 => letAt p (subst e1 σ) (subst e2 (substup σ))
      | pair e1 e2 => pair (subst e1 σ) (subst e2 σ)
      | pi1 e => pi1 (subst e σ)
      | pi2 e => pi2 (subst e σ)
      | inl e => inl (subst e σ)
      | inr e => inr (subst e σ)
      | caseE e1 e2 e3 =>
          caseE (subst e1 σ) (subst e2 (substup σ)) (subst e3 (substup σ))
      | efql e => efql (subst e σ)
      | lam t e => lam t (subst e (substup σ))
      | appE e1 e2 => appE (subst e1 σ) (subst e2 σ)
      | send e m p q => send (subst e σ) m p q
      | up e m p => up (subst e σ) m p
      | down e m p => down (subst e σ) m p
      end.

    Lemma subst_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall e, subst e σ1 = subst e σ2.
    Proof using.
      intros σ1 σ2 ext_eq e; revert σ1 σ2 ext_eq; induction e; intros σ1 σ2 ext_eq; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall n, ?f n = ?g n |- context[?f ?n]] => rewrite (H n)
          | [ IH : forall σ1 σ2, (forall n, σ1 n = σ2 n) -> subst ?e σ1 = subst ?e σ2,
                H : forall n, ?f n = ?g n |- context[subst ?e ?f]] =>
              rewrite (IH f g H)
          | [ H : forall n, ?f n = ?g n |- context[substup ?f] ] =>
              pose proof (substup_ext f g H)
          end.
    Qed.

    Lemma subst_id : forall e,
        subst e id_substitution = e.
    Proof using.
      intro e; induction e; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ |- context[id_substitution _]] => unfold id_substitution; cbn
          | [ IH : subst ?e ?f = ?e |- context[subst ?e ?f]] =>
              rewrite IH
          | [ |- context[subst ?e (substup id_substitution)]] =>
              rewrite (subst_ext (substup id_substitution) id_substitution
                         id_substup e)
          end.
    Qed.

    Lemma ren_subst : forall e ξ,
        ren e ξ = subst e (fun n => var (ξ n)).
    Proof using.
      intro e; induction e; intro ξ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ, ren ?e ξ = subst ?e (fun n => var (ξ n)) |- context[ren ?e ?f]] =>
              rewrite (IH f)
          | [ |- context[subst ?e (fun n => var (renup ?ξ n))]] =>
              rewrite (subst_ext (fun n => var (renup ξ n)) (substup (fun n => var (ξ n)))
                         (renup_substup ξ) e)
          end.
    Qed.
    
    Lemma ren_subst_fusion : forall e ξ σ,
        subst (ren e ξ) σ = subst e (fun n => σ (ξ n)).
    Proof using.
      intro e; induction e; intros ξ σ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ σ, subst (ren ?e ξ) σ = subst ?e (fun n => σ (ξ n))
                               |- context[subst (ren ?e ?ξ) ?σ]] =>
              rewrite (IH ξ σ)
          | [ |- context[subst ?e (fun n => substup σ (renup ξ n))]] =>
              rewrite (subst_ext (fun n => substup σ (renup ξ n)) (substup (fun n => σ (ξ n)))
                         (substup_renup_fusion ξ σ) e)
          end.
    Qed.
    
    Lemma subst_ren_fusion : forall e σ ξ,
        ren (subst e σ) ξ = subst e (fun n => ren (σ n) ξ).
    Proof using.
      intro e; induction e; intros σ ξ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall σ ξ, ren (subst ?e σ) ξ = subst ?e (fun n => ren (σ n) ξ)
                               |- context[ren (subst ?e ?σ) ?ξ]] =>
              rewrite (IH σ ξ)
          | [|- context[subst ?e (fun n => ren (substup ?σ n) (renup ?ξ))]] =>
              rewrite (subst_ext (fun n => ren (substup σ n) (renup ξ))
                         (substup (fun n => ren (σ n) ξ))
                         (renup_substup_fusion σ ξ) e)
          end.
    Qed.

    Lemma substup_fusion : forall σ1 σ2 n,
        (fun n => subst (substup σ1 n) (substup σ2)) n = (substup (fun n => subst (σ1 n) σ2)) n.
    Proof using.
      intros σ1 σ2 n; destruct n; cbn; [reflexivity|].
      rewrite ren_subst_fusion; rewrite subst_ren_fusion.
      unfold substup; reflexivity.
    Qed.

    Theorem subst_fusion : forall e σ1 σ2,
        subst (subst e σ1) σ2 = subst e (fun n => subst (σ1 n) σ2).
    Proof using.
      intro e; induction e; intros σ1 σ2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall σ1 σ2, subst (subst ?e σ1) σ2 = subst ?e (fun n => subst (σ1 n) σ2)
                                 |- context[subst (subst ?e ?f) ?g]] =>
              rewrite (IH f g)
          | [ |- context[subst ?e (fun n => subst (substup ?f n) (substup ?g))]] =>
              rewrite (subst_ext (fun n => subst (substup f n) (substup g))
                         (substup (fun n => subst (f n) g))
                         (substup_fusion f g))
          end.
    Qed.

  End Substitution.

  Section Closure.

    Inductive closed_above : expr -> nat -> Prop :=
    | var_ca {n m : nat} (n_lt_m : n < m) : closed_above (var n) m
    | uu_ca (n : nat) : closed_above uu n
    | atE_ca (p : PName) {e : expr} {n : nat} (pf : closed_above e n) : closed_above (atE p e) n
    | letAt_ca (p : PName) {e1 e2 : expr} {n : nat}
        (pf1 : closed_above e1 n) (pf2 : closed_above e2 (S n)) : closed_above (letAt p e1 e2) n
    | pair_ca {e1 e2 : expr} {n : nat} (pf1 : closed_above e1 n) (pf2 : closed_above e2 n)
      : closed_above (pair e1 e2) n
    | pi1_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (pi1 e) n
    | pi2_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (pi2 e) n
    | inl_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (inl e) n
    | inr_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (inr e) n
    | caseE_ca {e1 e2 e3 : expr} {n : nat}
        (pf1 : closed_above e1 n)
        (pf2 : closed_above e2 (S n))
        (pf3 : closed_above e3 (S n))
      : closed_above (caseE e1 e2 e3) n
    | efql_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (efql e) n
    | lam_ca (t : type) {e : expr} {n : nat} (pf : closed_above e (S n)) : closed_above (lam t e) n
    | app_ca {e1 e2 : expr} {n : nat} (pf1 : closed_above e1 n) (pf2 : closed_above e2 n)
      : closed_above (appE e1 e2) n
    | send_ca {e : expr} (m : mod) (p q : PName) {n : nat} (pf : closed_above e n)
      : closed_above (send e m p q) n
    | up_ca {e : expr} (m : mod) (p : PName) {n : nat} (pf : closed_above e n)
      : closed_above (up e m p) n
    | down_ca {e : expr}  (m : mod) (p : PName) {n : nat} (pf : closed_above e n)
      : closed_above (down e m p) n.

    Fixpoint closed_aboveb (e : expr) (n : nat) : bool :=
      match e with
      | var x => PeanoNat.Nat.ltb x n
      | uu => true
      | atE p e => closed_aboveb e n
      | letAt p e1 e2 => closed_aboveb e1 n && closed_aboveb e2 (S n)
      | pair e1 e2 => closed_aboveb e1 n && closed_aboveb e2 n
      | pi1 e => closed_aboveb e n
      | pi2 e => closed_aboveb e n
      | inl e => closed_aboveb e n
      | inr e => closed_aboveb e n
      | caseE e1 e2 e3 => closed_aboveb e1 n && closed_aboveb e2 (S n) && closed_aboveb e3 (S n)
      | efql e => closed_aboveb e n
      | lam t e => closed_aboveb e (S n)
      | appE e1 e2 => closed_aboveb e1 n && closed_aboveb e2 n
      | send e m p q => closed_aboveb e n
      | up e  m p => closed_aboveb e n
      | down e m p => closed_aboveb e n
      end.

    Lemma closed_aboveb_spec1 : forall e n, closed_aboveb e n = true -> closed_above e n.
    Proof using.
      intro e; induction e; cbn; intros n' clsdb;
        repeat match goal with
          | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
          end;
        try (econstructor; eauto; fail).
      constructor; rewrite <- PeanoNat.Nat.ltb_lt; cbn; assumption.
    Qed.

    Lemma closed_aboveb_spec2 : forall e n, closed_above e n -> closed_aboveb e n = true.
    Proof using.
      intros e n clsd; induction clsd; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : ?P |- ?P ] => exact H
          | [ |- _ && _ = true ] => apply andb_true_intro; split
          | [ H : ?n < ?m |- match ?m with | 0 => false | S m' => PeanoNat.Nat.leb ?n m' end = true] =>
              let H' := fresh in
              pose proof ((proj2 (PeanoNat.Nat.ltb_lt n m)) H) as H';
              cbn in H';
              rewrite H';
              reflexivity
          end.
    Qed.

    Theorem closed_aboveb_spec : forall e n, closed_above e n <-> closed_aboveb e n = true.
    Proof using.
      intros e n; split; [apply closed_aboveb_spec2 | apply closed_aboveb_spec1].
    Qed.

    Theorem closed_above_mono : forall e n, closed_above e n -> forall m, n < m -> closed_above e m.
    Proof using.
      intros e n clsd; induction clsd; intros k n_lt_k;
        repeat match goal with
          | [ IH : forall m, S ?n < m -> closed_above ?e m, H : ?n < ?k |- _ ] =>
              lazymatch goal with
              | [_ : S n < S k |- _ ] => fail
              | _ => assert (S n < S k) by lia
              end
          end;
        try (econstructor; eauto; fail).
      * constructor; transitivity m; assumption.
    Qed.

    Corollary closed_above_mono' : forall e n, closed_above e n -> forall m, n <= m -> closed_above e m.
    Proof using.
      intros e n clsd m n_le_m.
      destruct (Compare_dec.le_lt_eq_dec n m n_le_m); [|subst; assumption].
      apply closed_above_mono with (n := n); assumption.
    Qed.

    Definition closed (e : expr) : Prop := closed_above e 0.

    Theorem closed_closed_above : forall e, closed e -> forall n, closed_above e n.
    Proof using.
      intros e clsd n; apply (closed_above_mono' clsd). apply le_0_n.
    Qed.
    
    Lemma closed_above_ren_id : forall e ξ n,
        (forall m, m < n -> ξ m = m) ->
        closed_above e n ->
        ren e ξ = e.
    Proof using.
      intro e; induction e; cbn; intros ξ k id_bel clsd; inversion clsd; subst;
        repeat match goal with
          | [ H : ?m < ?n, H' : forall m, m < ?n -> ?f m = m |- context[?f ?m]] => rewrite (H' m H)
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ n, (forall m, m < n -> ξ m = m) -> closed_above ?e n -> ren ?e ξ = ?e,
                H : forall m, m < ?n -> ?f m = m,
                H' : closed_above ?e ?n |-
                  context[ren ?e ?f]] =>
              rewrite (IH f n H H')
          | [ H : forall m, m < ?n -> ?f m = m |- context[renup ?f]] =>
              lazymatch goal with
              | [ _ : forall m, m < S ?n -> renup ?f m = m |- _ ] => fail
              | _ => pose proof (renup_id_below f H)
              end
          end.
    Qed.

    Corollary closed_ren_id : forall e, closed e -> forall ξ, ren e ξ = e.
    Proof using.
      intros e clsd ξ; apply (@closed_above_ren_id e ξ 0); [| exact clsd].
      intros m m_lt_z; inversion m_lt_z.
    Qed.

    Lemma closed_above_subst_id : forall e σ n,
        (forall m, m < n -> σ m = var m) ->
        closed_above e n ->
        subst e σ = e.
    Proof using.
      intro e; induction e; cbn; intros σ k id_bel clsd; inversion clsd; subst;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall m, m < ?n -> ?f m = var m, H' : ?m < ?n |- context[?f ?m]] => rewrite (H m H')
          | [ IH : forall σ n, (forall m, m < n -> σ m = var m) -> closed_above ?e n -> subst ?e σ = ?e,
                H' : forall m, m < ?n -> ?f m = var m,
                H'' : closed_above ?e ?n |- context[subst ?e ?f]] =>
              rewrite (IH f n H' H'')
          | [H : forall m, m < ?n -> ?f m = var m |- context[substup ?f]] =>
              lazymatch goal with
              | [_ : forall m, m < S n -> substup f m = var m |- _] => fail
              | _ => pose proof (substup_id_below f H)
              end
          end.
    Qed.

    Corollary closed_subst_id : forall e, closed e -> forall σ, subst e σ = e.
    Proof using.
      intros e clsd σ; apply closed_above_subst_id with (n := 0); [|exact clsd].
      intros m m_lt_0; inversion m_lt_0.
    Qed.

    Lemma renup_closed_above : forall ξ n k,
        (forall m, m < n -> ξ m < k) ->
        forall m, m < S n -> renup ξ m < S k.
    Proof using.
      intros ξ n k clsd_abv m m_lt_Sn; destruct m; cbn.
      apply PeanoNat.Nat.lt_0_succ.
      assert (ξ m < k) by (apply clsd_abv; lia); lia.
    Qed.

    Lemma ren_closed_above : forall e ξ n k,
        closed_above e n ->
        (forall m, m < n -> ξ m < k) ->
        closed_above (ren e ξ) k.
    Proof using.
      intros e; induction e; intros ξ k1 k2 clsd_e clsd_ξ; inversion clsd_e; subst; cbn;
        repeat match goal with
          | [ H : forall m, m < ?k1 -> ?f m < ?k2 |- context[renup ?f]] =>
              lazymatch goal with
              | [_ : forall m, m < S k1 -> renup f m < S k2 |- _ ] => fail
              | _ => pose proof (renup_closed_above f H)
              end
          end;
        try (econstructor; eauto; fail).
    Qed.

    Lemma substup_closed_above : forall σ n k,
        (forall m, m < n -> closed_above (σ m) k) ->
        forall m, m < S n -> closed_above (substup σ m) (S k).
    Proof using.
      intros σ n k clsd_abv m m_lt_Sn; destruct m; cbn.
      * constructor; apply PeanoNat.Nat.lt_0_succ.
      * apply ren_closed_above with (n := k). apply clsd_abv.
        all: intros; lia.
    Qed.

    Lemma subst_closed_above : forall e σ n k,
        closed_above e n ->
        (forall m, m < n -> closed_above (σ m) k) ->
        closed_above (subst e σ) k.
    Proof using.
      intro e; induction e; intros σ k1 k2 clsd_e clsd_σ; inversion clsd_e; subst; cbn;
        repeat match goal with
          | [ H : forall m, m < ?n -> closed_above (?σ m) ?k |- context[substup ?σ]] =>
              lazymatch goal with
              | [ _ : forall m, m < S n -> closed_above (substup σ m) (S k) |- _ ] => fail
              | _ => pose proof (substup_closed_above σ H)
              end
          end;
        try (econstructor; eauto; fail).
      apply clsd_σ; assumption.
    Qed.

    (* This is essentially a nameless version of the traditional free-variables function. *)
    Fixpoint min_closure (e : expr) : nat :=
      match e with
      | var x => S x
      | uu => 0
      | atE p e => min_closure e
      | letAt p e1 e2 => max (min_closure e1) (pred (min_closure e2))
      | pair e1 e2 => max (min_closure e1) (min_closure e2)
      | pi1 e => min_closure e
      | pi2 e => min_closure e
      | inl e => min_closure e
      | inr e => min_closure e
      | caseE e1 e2 e3 => max (min_closure e1) (max (pred (min_closure e2)) (pred (min_closure e3)))
      | efql e => min_closure e
      | lam t e => pred (min_closure e)
      | appE e1 e2 => max (min_closure e1) (min_closure e2)
      | send e m p q => min_closure e
      | up e  m p => min_closure e
      | down e m p => min_closure e
      end.

    Theorem closed_above_min : forall e, closed_above e (min_closure e).
    Proof using.
      intro e; induction e; cbn; try (econstructor; eauto; fail).
      all: constructor; eapply closed_above_mono'; eauto; lia.
    Qed.

    Theorem open_below_min : forall e n, closed_above e n -> min_closure e <= n.
    Proof using.
      intros e n clsd; induction clsd; cbn; lia.
    Qed.

    Inductive closed_between : expr -> nat -> nat -> Prop :=
    | var_cb1 {n m x : nat} (x_lt_n : x < n) : closed_between (var x) n m
    | var_cb2 {n m x : nat} (m_lt_x : m <= x) : closed_between (var x) n m
    | uu_cb (n m : nat) : closed_between uu n m
    | atE_cb (p : PName) {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (atE p e) n m
    | letAt_cb (p : PName) {e1 e2 : expr} {n m : nat}
        (pf1 : closed_between e1 n m) (pf2 : closed_between e2 (S n) (S m))
      : closed_between (letAt p e1 e2) n m
    | pair_cb {e1 e2 : expr} {n m : nat} (pf1 : closed_between e1 n m) (pf2 : closed_between e2 n m)
      : closed_between (pair e1 e2) n m
    | pi1_cb {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (pi1 e) n m
    | pi2_cb {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (pi2 e) n m
    | inl_cb {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (inl e) n m
    | inr_cb {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (inr e) n m
    | caseE_cb {e1 e2 e3 : expr} {n m : nat}
        (pf1 : closed_between e1 n m)
        (pf2 : closed_between e2 (S n) (S m))
        (pf3 : closed_between e3 (S n) (S m))
      : closed_between (caseE e1 e2 e3) n m
    | efql_cb {e : expr} {n m : nat} (pf : closed_between e n m) : closed_between (efql e) n m
    | lam_cb (t : type) {e : expr} {n m : nat} (pf : closed_between e (S n) (S m))
      : closed_between (lam t e) n m
    | app_cb {e1 e2 : expr} {n m : nat} (pf1 : closed_between e1 n m) (pf2 : closed_between e2 n m)
      : closed_between (appE e1 e2) n m
    | send_cb {e : expr} (m : mod) (p q : PName) {n k : nat} (pf : closed_between e n k)
      : closed_between (send e m p q) n k
    | up_cb {e : expr} (m : mod) (p : PName) {n k : nat} (pf : closed_between e n k)
      : closed_between (up e m p) n k
    | down_cb {e : expr}  (m : mod) (p : PName) {n k : nat} (pf : closed_between e n k)
      : closed_between (down e m p) n k.

    Definition closed_below (e : expr) (m : nat) : Prop :=
      closed_between e 0 m.
    
    Fixpoint closed_betweenb (e : expr) (n k : nat) : bool :=
      match e with
      | var x => PeanoNat.Nat.ltb x n || PeanoNat.Nat.leb k x
      | uu => true
      | atE p e => closed_betweenb e n k
      | letAt p e1 e2 => closed_betweenb e1 n k && closed_betweenb e2 (S n) (S k)
      | pair e1 e2 => closed_betweenb e1 n k && closed_betweenb e2 n k
      | pi1 e => closed_betweenb e n k
      | pi2 e => closed_betweenb e n k
      | inl e => closed_betweenb e n k
      | inr e => closed_betweenb e n k
      | caseE e1 e2 e3 =>
          closed_betweenb e1 n k && closed_betweenb e2 (S n) (S k) && closed_betweenb e3 (S n) (S k)
      | efql e => closed_betweenb e n k
      | lam t e => closed_betweenb e (S n) (S k)
      | appE e1 e2 => closed_betweenb e1 n k && closed_betweenb e2 n k
      | send e m p q => closed_betweenb e n k
      | up e m p => closed_betweenb e n k
      | down e m p => closed_betweenb e n k
      end.

    Definition closed_belowb (e : expr) (m : nat) := closed_betweenb e 0 m.
    
    Lemma closed_betweenb_spec1 : forall e n k, closed_betweenb e n k = true -> closed_between e n k.
    Proof using.
      intro e; induction e; intros k1 k2 eq; cbn in *;
        repeat match goal with
          | [ H : ?b1 && ?b2 = true |- _ ] => apply Bool.andb_true_iff in H; destruct H
          | [ H : ?b1 || ?b2 = true |- _ ] => apply Bool.orb_true_iff in H; destruct H
          end; try (econstructor; eauto; fail).
      destruct k1; [inversion H0|].
      constructor.
      apply Compare_dec.leb_complete in H0; rewrite PeanoNat.Nat.lt_succ_r; assumption.
      apply var_cb2.
      apply Compare_dec.leb_complete; assumption.
    Qed.

    Lemma closed_between_spec2 : forall e n k, closed_between e n k -> closed_betweenb e n k = true.
    Proof using.
      intros e n k clsd; induction clsd; cbn;
        repeat match goal with
          | [ |- _ && _ = true ] => apply Bool.andb_true_iff; split
          | [ |- ?b1 || ?b2 = true ] => apply Bool.orb_true_iff
          end; auto.
      - left. destruct n; [destruct (PeanoNat.Nat.nlt_0_r x x_lt_n) |].
        apply PeanoNat.Nat.leb_le; apply PeanoNat.Nat.lt_succ_r; assumption.
      - right; apply Compare_dec.leb_correct; assumption.
    Qed.

    Theorem closed_betweenb_spec : forall e n m, closed_between e n m <-> closed_betweenb e n m = true.
    Proof using.
      intros e n m; split; [apply closed_between_spec2 | apply closed_betweenb_spec1].
    Qed.

    Corollary closed_belowb_spec : forall e n, closed_below e n <-> closed_belowb e n = true.
    Proof using.
      unfold closed_below; unfold closed_belowb; intros e n; apply closed_betweenb_spec.
    Qed.

    Theorem closed_between_mono : forall e n m,
        closed_between e n m -> forall n' m', n < n' -> m' < m -> closed_between e n' m'.
    Proof using.
      intros e n m clsd; induction clsd; intros n' m' n_lt_n' m'_lt_m;
        repeat match goal with
          | [ IH : forall n' m', ?n < n' -> m' < ?m -> closed_between ?e n' m',
                H1 : ?n < ?n', H2 : ?m' < ?m |- _ ] =>
              lazymatch goal with
              | [ _ : closed_between e n' m' |- _ ] => fail
              | _ => pose proof (IH n' m' H1 H2)
              end
          | [ IH : forall n' m', S ?n < n' -> m' < S ?m -> closed_between ?e n' m',
                H1 : ?n < ?n', H2 : ?m' < ?m |- _ ] =>
              lazymatch goal with
              | [ _ : closed_between e (S n') (S m') |- _ ] => fail
              | _ => pose proof (IH (S n') (S m') (ltac:(rewrite <- PeanoNat.Nat.succ_lt_mono; exact H1))
                                  (ltac:(rewrite <- PeanoNat.Nat.succ_lt_mono; exact H2)))
              end 
          end; try (econstructor; eauto; fail).
      try (constructor; etransitivity; eauto; fail).
      apply var_cb2; transitivity m; lia.
    Qed.

    Theorem closed_between_mono' : forall e n m,
        closed_between e n m ->
        forall n' m', n <= n' -> m' <= m -> closed_between e n' m'.
    Proof using.
      intros e n m clsd; induction clsd; intros n' m' n_le_n' m'_le_m;
        repeat match goal with
          | [ IH : forall n' m', ?n <= n' -> m' <= ?m -> closed_between ?e n' m',
                H1 : ?n <= ?n', H2 : ?m' <= ?m |- _ ] =>
              lazymatch goal with
              | [ _ : closed_between e n' m' |- _ ] => fail
              | _ => pose proof (IH n' m' H1 H2)
              end
          | [ IH : forall n' m', S ?n <= n' -> m' <= S ?m -> closed_between ?e n' m',
                H1 : ?n <= ?n', H2 : ?m' <= ?m |- _ ] =>
              lazymatch goal with
              | [ _ : closed_between e (S n') (S m') |- _ ] => fail
              | _ => pose proof (IH (S n') (S m') (ltac:(rewrite <- PeanoNat.Nat.succ_le_mono; exact H1))
                                  (ltac:(rewrite <- PeanoNat.Nat.succ_le_mono; exact H2)))
              end 
          end; try (econstructor; eauto; fail).
      - constructor; apply PeanoNat.Nat.lt_le_trans with (m := n); auto.
      - apply var_cb2; transitivity m; auto. 
    Qed.

    Corollary closed_below_mono' : forall e n, closed_below e n -> forall n', n' <= n -> closed_below e n'.
    Proof using.
      unfold closed_below. intros e n clsd n' n'_le_n.
      apply closed_between_mono' with (n := 0) (m := n); auto.
    Qed.

    Corollary closed_below_mono : forall e n, closed_below e n -> forall n', n' < n -> closed_below e n'.
    Proof using.
      intros e n H0 n' H1; apply closed_below_mono' with (n := n); auto; lia.
    Qed.

    Lemma closed_between_ren_up1 : forall ξ n,
        (forall k, k < n -> ξ k = k) ->
        forall k, k < (S n) -> renup ξ k = k.
    Proof using.
      intros ξ n ξbd k k_lt_Sn; destruct k; cbn. reflexivity.
      rewrite ξbd. reflexivity.
      rewrite PeanoNat.Nat.succ_lt_mono; assumption.
    Qed.

    
    Lemma closed_between_ren_up2 : forall ξ n,
        (forall k, n <= k -> ξ k = k) ->
        forall k, (S n) <= k -> renup ξ k = k.
    Proof using.
      intros ξ n ξbd k Sn_lt_k; destruct k; cbn. reflexivity.
      rewrite ξbd. reflexivity.
      rewrite PeanoNat.Nat.succ_le_mono; assumption.
    Qed.

    Lemma closed_between_ren_id : forall e ξ n m,
        (forall k, k < n -> ξ k = k) ->
        (forall k, m <= k -> ξ k = k) ->  
        closed_between e n m ->
        ren e ξ = e.
    Proof using.
      intros e ξ n m ξbd1 ξbd2 clsd; revert ξ ξbd1 ξbd2; induction clsd; intros ξ ξbd1 ξbd2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ, (forall k, k < ?n -> ξ k = k) -> (forall k', ?m <= k' -> ξ k' = k') -> ren ?e ξ = ?e,
                H1 : forall k, k < ?n -> ?ξ k = k, H2 : forall k, ?m <= k -> ?ξ k = k |- context[ren ?e ?ξ] ] =>
              rewrite (IH ξ H1 H2)
          | [ IH : forall ξ, (forall k, k < S ?n -> ξ k = k) -> (forall k', S ?m <= k' -> ξ k' = k') -> ren ?e ξ = ?e,
                H1 : forall k, k < ?n -> ?ξ k = k, H2 : forall k, ?m <= k -> ?ξ k = k |- context[ren ?e (renup ?ξ)] ] =>
              rewrite (IH (renup ξ) (closed_between_ren_up1 ξ H1) (closed_between_ren_up2 ξ H2))
          end.
      - rewrite ξbd1; auto.
      - rewrite ξbd2; auto.
    Qed.
    Lemma closed_between_ren_ext_up1 : forall ξ1 ξ2 n,
        (forall k, k < n -> ξ1 k = ξ2 k) ->
        (forall k, k < S n -> renup ξ1 k = renup ξ2 k).
    Proof using.
      intros ξ1 ξ2 n H2 k; revert n H2; destruct k; intros n H2 k_lt_Sn; cbn in *.
      - reflexivity.
      - rewrite H2; [reflexivity| apply PeanoNat.Nat.succ_lt_mono; assumption].
    Qed.

    Lemma closed_between_ren_ext_up2 : forall ξ1 ξ2 n,
        (forall k, n <= k -> ξ1 k = ξ2 k) ->
        (forall k, S n <= k -> renup ξ1 k = renup ξ2 k).
    Proof using.
      intros ξ1 ξ2 n H1 k k_lt_n; destruct k; cbn.
      - reflexivity.
      - rewrite H1; [reflexivity| apply le_S_n; assumption].
    Qed.
    
    Lemma closed_between_ren_ext : forall e ξ1 ξ2 n m,
        (forall k, k < n -> ξ1 k = ξ2 k) ->
        (forall k, m <= k -> ξ1 k = ξ2 k) ->
        closed_between e n m ->
        ren e ξ1 = ren e ξ2.
    Proof using.
      intro e; induction e; intros ξ1 ξ2 n' m' blw abv clsd; inversion clsd; subst; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : ?P |- ?P ] => exact H
          | [ IH : forall ξ1 ξ2 n m, (forall k, k < n -> ξ1 k = ξ2 k) ->
                                (forall k', m <= k' -> ξ1 k' = ξ2 k') ->
                                closed_between ?e n m ->
                                ren ?e ξ1 = ren ?e ξ2,
                H1 : forall k, k < ?n -> ?ξ1 k = ?ξ2 k,
                H2 : forall k, ?m <= k -> ?ξ1 k = ?ξ2 k,
                H3 : closed_between ?e ?n ?m
                |- context[ren ?e ?ξ1]] =>
              rewrite (IH ξ1 ξ2 n m H1 H2 H3)
          | [ H : forall k, k < ?n -> ?ξ1 k = ?ξ2 k |- context[renup ?ξ1]] =>
              lazymatch goal with
              | [_ : forall k, k < S n -> renup ξ1 k = renup ξ2 k |- _ ] => fail
              | _ => pose proof (closed_between_ren_ext_up1 ξ1 ξ2 H)
              end 
          | [ H : forall k, ?m <= k -> ?ξ1 k = ?ξ2 k |- context[renup ?ξ1]] =>
              lazymatch goal with
              | [_ : forall k, S m <= k -> renup ξ1 k = renup ξ2 k |- _ ] => fail
              | _ => pose proof (closed_between_ren_ext_up2 ξ1 ξ2 H)
              end 
          end; eauto.
    Qed.                   
    Corollary closed_below_ren_ext : forall e ξ1 ξ2 m,
        (forall k, m <= k -> ξ1 k = ξ2 k) ->
        closed_below e m ->
        ren e ξ1 = ren e ξ2.
    Proof using.
      intros e ξ1 ξ2 m H0 H1; unfold closed_below in H1.
      apply closed_between_ren_ext with (n := 0) (m := m); auto.
      intros k H2; inversion H2.
    Qed.

    Lemma closed_between_subst_up1 : forall σ n,
        (forall k, k < n -> σ k = var k) ->
        forall k, k < (S n) -> substup σ k = var k.
    Proof using.
      intros σ n σbd k k_lt_Sn; destruct k; cbn. reflexivity.
      rewrite σbd. reflexivity.
      rewrite PeanoNat.Nat.succ_lt_mono; assumption.
    Qed.

    Lemma closed_between_subst_up2 : forall σ n,
        (forall k, n <= k -> σ k = var k) ->
        forall k, (S n) <= k -> substup σ k = var k.
    Proof using.
      intros σ n σbd k Sn_lt_k; destruct k; cbn. reflexivity.
      rewrite σbd. reflexivity.
      rewrite PeanoNat.Nat.succ_le_mono; assumption.
    Qed.
    
    Lemma closed_between_subst_id : forall e σ n m,
        (forall k, k < n -> σ k = var k) ->
        (forall k, m <= k -> σ k = var k) ->  
        closed_between e n m ->
        subst e σ = e.
    Proof using.
      intros e σ n m σbd1 σbd2 clsd; revert σ σbd1 σbd2; induction clsd; intros σ σbd1 σbd2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall σ, (forall k, k < ?n -> σ k = var k) -> (forall k', ?m <= k' -> σ k' = var k') -> subst ?e σ = ?e,
                H1 : forall k, k < ?n -> ?σ k = var k, H2 : forall k, ?m <= k -> ?σ k = var k |- context[subst ?e ?σ] ] =>
              rewrite (IH σ H1 H2)
          | [ IH : forall σ, (forall k, k < S ?n -> σ k = var k) -> (forall k', S ?m <= k' -> σ k' = var k') -> subst ?e σ = ?e,
                H1 : forall k, k < ?n -> ?σ k = var k, H2 : forall k, ?m <= k -> ?σ k = var k |- context[subst ?e (substup ?σ)] ] =>
              rewrite (IH (substup σ) (closed_between_subst_up1 σ H1) (closed_between_subst_up2 σ H2))
          end.
      - rewrite σbd1; auto.
      - rewrite σbd2; auto.
    Qed.

    Lemma closed_between_ren_subst_up1 : forall σ1 σ2 n,
        (forall k, k < n -> σ1 k = σ2 k) ->
        (forall k, k < S n -> substup σ1 k = substup σ2 k).
    Proof using.
      intros σ1 σ2 n H2 k; revert n H2; destruct k; intros n H2 k_lt_Sn; cbn in *.
      - reflexivity.
      - rewrite H2; [reflexivity| apply PeanoNat.Nat.succ_lt_mono; assumption].
    Qed.

    Lemma closed_between_ren_subst_up2 : forall σ1 σ2 n,
        (forall k, n <= k -> σ1 k = σ2 k) ->
        (forall k, S n <= k -> substup σ1 k = substup σ2 k).
    Proof using.
      intros σ1 σ2 n H1 k k_lt_n; destruct k; cbn.
      - reflexivity.
      - rewrite H1; [reflexivity| apply le_S_n; assumption].
    Qed.

    Lemma closed_between_subst_ext : forall e σ1 σ2 n m,
        (forall k, k < n -> σ1 k = σ2 k) ->
        (forall k, m <= k -> σ1 k = σ2 k) ->
        closed_between e n m ->
        subst e σ1 = subst e σ2.
    Proof using.
      intro e; induction e; intros σ1 σ2 n' m' blw abv clsd; inversion clsd; subst; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : ?P |- ?P ] => exact H
          | [ IH : forall σ1 σ2 n m, (forall k, k < n -> σ1 k = σ2 k) ->
                                (forall k', m <= k' -> σ1 k' = σ2 k') ->
                                closed_between ?e n m ->
                                subst ?e σ1 = subst ?e σ2,
                H1 : forall k, k < ?n -> ?ξ1 k = ?ξ2 k,
                H2 : forall k, ?m <= k -> ?ξ1 k = ?ξ2 k,
                H3 : closed_between ?e ?n ?m
                |- context[subst ?e ?ξ1]] =>
              rewrite (IH ξ1 ξ2 n m H1 H2 H3)
          | [ H : forall k, k < ?n -> ?σ1 k = ?σ2 k |- context[substup ?σ1]] =>
              lazymatch goal with
              | [_ : forall k, k < S n -> substup σ1 k = substup σ2 k |- _ ] => fail
              | _ => pose proof (closed_between_ren_subst_up1 σ1 σ2 H)
              end 
          | [ H : forall k, ?m <= k -> ?σ1 k = ?σ2 k |- context[substup ?σ1]] =>
              lazymatch goal with
              | [_ : forall k, S m <= k -> substup σ1 k = renup σ2 k |- _ ] => fail
              | _ => pose proof (closed_between_ren_subst_up2 σ1 σ2 H)
              end 
          end; eauto.
    Qed.

    Corollary closed_below_subst_ext : forall e σ1 σ2 m,
        (forall k, m <= k -> σ1 k = σ2 k) ->
        closed_below e m ->
        subst e σ1 = subst e σ2.
    Proof using.
      intros e σ1 σ2 m H0 H1; unfold closed_below in H1.
      apply closed_between_subst_ext with (n := 0) (m := m); auto.
      intros k H2; inversion H2.
    Qed.

    Lemma renup_closed_below : forall {ξ : renaming} {k k' : nat},
        (forall n, k <= n -> k' <= ξ n) ->
        (forall n, S k <= n -> S k' <= renup ξ n).
    Proof using.
      intros ξ k k' H0 n; induction n; intro H1; cbn.
      inversion H1.
      apply le_S_n in H1; apply le_n_S; apply H0; auto.
    Qed.

    Lemma closed_between_ren : forall {e : expr} {ξ : renaming} {k1 k2 k1' k2' : nat},
        (forall n, n < k1' -> ξ n < k1) ->
        (forall n, k2' <= n -> k2 <= ξ n) ->
        closed_between e k1' k2' ->
        closed_between (ren e ξ) k1 k2.
    Proof using.
      intros e; induction e; intros ξ k1 k2 k1' k2' H0 H1 clsd; inversion clsd; subst; cbn;
        try (econstructor;
             repeat match goal with
               | [ IH : forall ξ k1 k2 k1' k2', (forall n, n < k1' -> ξ n < k1) -> (forall m, k2' <= m -> k2 <= ξ m) -> closed_between ?e k1' k2' -> closed_below (ren ?e ξ) k1 k2,
                     H1 : forall n, n < ?k1' -> ?ξ n < ?k1,
                     H2 : forall n, ?k2' <= n -> ?k2 <= ?ξ n,
                     H3 : closed_between ?e ?k1' ?k2' |- closed_between (ren ?e ?ξ) ?k1 ?k ] =>
                   apply (IH ξ k1 k2 k1' k2' H1 H2 H3)
               end; eauto; fail).
      - constructor. apply IHe1 with (k1' := k1') (k2' := k2'); auto.
        apply IHe2 with (k1' := S k1') (k2' := S k2'); auto.
        apply renup_closed_above; assumption.
        apply renup_closed_below; assumption.
      - constructor.
        -- eapply IHe1; eauto.
        -- eapply IHe2; eauto. apply renup_closed_above; assumption.
           apply renup_closed_below; assumption.
        -- eapply IHe3; eauto. apply renup_closed_above; assumption.
           apply renup_closed_below; assumption.
      - constructor. eapply IHe; eauto.
        apply renup_closed_above; assumption.
        apply renup_closed_below; assumption.
    Qed.

    Corollary closed_below_ren : forall {e : expr} {ξ : renaming} {k k' : nat},
        (forall n, k' <= n -> k <= ξ n) ->
        closed_below e k' ->
        closed_below (ren e ξ) k.
    Proof using.
      intros e ξ k k' H0 H1; unfold closed_below; eapply closed_between_ren;
        eauto.
      intros n H2; inversion H2.
    Qed.

    Lemma closed_between_self : forall (e : expr) (m : nat), closed_between e m m.
    Proof using.
      intro e; induction e; intro k; try (econstructor; eauto; fail).
      destruct (PeanoNat.Nat.lt_ge_cases n k); (econstructor; eauto; fail).
    Qed.

    Corollary closed_below_zero : forall (e : expr), closed_below e 0.
    Proof using.
      intro e; unfold closed_below; apply closed_between_self.
    Qed.

    Theorem closed_between_substup1 : forall {σ : substitution} {n n' m' : nat},
        (forall k, k < n -> closed_between (σ k) n' m') ->
        (forall k, k < S n -> @closed_between (substup σ k) (S n') (S m')).
    Proof using.
      intros σ n n' m' clsd k k_lt_Sn.
      destruct k; cbn. constructor; lia.
      apply @closed_between_ren with (k2' := m') (k1' := n').
      intros; rewrite <- PeanoNat.Nat.succ_lt_mono; assumption.
      apply le_n_S.
      apply clsd.
      rewrite PeanoNat.Nat.succ_lt_mono; assumption.
    Qed.

    Theorem closed_between_substup2 : forall {σ : substitution} {m n' m' : nat},
        (forall k, m <= k -> closed_between (σ k) n' m') ->
        (forall k, S m <= k -> @closed_between (substup σ k) (S n') (S m')).
    Proof using.
      intros σ m n' m' H0 k H1; destruct k; cbn. constructor; lia.
      apply le_S_n in H1.
      apply @closed_between_ren with (k1' := n') (k2' := m').
      intros; rewrite <- PeanoNat.Nat.succ_lt_mono; assumption.
      apply le_n_S.
      apply H0; assumption.
    Qed.

    Theorem closed_between_subst : forall {e : expr} {σ : substitution} {n m n' m' : nat},
        (forall k, k < n -> closed_between (σ k) n' m') ->
        (forall k, m <= k -> closed_between (σ k) n' m') ->
        closed_between e n m ->
        closed_between (subst e σ) n' m'.
    Proof using.
      intro e; induction e; intros σ i j i' j' clsd1 clsd2 clsd; inversion clsd; subst; cbn;
        try (econstructor; repeat match goal with
               | [ H : forall k, k < ?i -> closed_between (?σ k) ?i' ?j' |- context[substup ?σ]] =>
                   lazymatch goal with
                   | [_ : forall k, k < S i -> closed_between (substup σ k) (S i') (S j') |- _] => fail
                   | _ => pose proof (closed_between_substup1 H)
                   end
               | [ H : forall k, ?j <= k -> closed_between (?σ k) ?i' ?j' |- context[substup ?σ]] =>
                   lazymatch goal with
                   | [_ : forall k, S j <= k  -> closed_between (substup σ k) (S i') (S j') |- _] => fail
                   | _ => pose proof (closed_between_substup2 H)
                   end
               end; eauto; fail).
      - apply clsd1; auto.
      - apply clsd2; auto.
    Qed.

    Corollary closed_below_subst : forall {e : expr} {σ : substitution} {n n' : nat},
        (forall k, n <= k -> closed_below (σ k) n') ->
        closed_below e n ->
        closed_below (subst e σ) n'.
    Proof using.
      unfold closed_below; intros e σ n n' H0 H1.
      apply @closed_between_subst with (m := n) (n := 0); [ | exact H0 | exact H1].
      intros k H2; inversion H2.
    Qed.

    Theorem closed_narrow_substup1 : forall {σ : substitution} {n n' m' j : nat},
        (forall k, k < j -> k < n -> closed_between (σ k) n' m') ->
        (forall k, k < S j -> k < S n -> @closed_between (substup σ k) (S n') (S m')).
    Proof using.
      intros σ n n' m' j clsd k k_lt_Sj k_lt_Sn.
      destruct k; cbn. constructor; lia.
      apply @closed_between_ren with (k2' := m') (k1' := n').
      intros; rewrite <- PeanoNat.Nat.succ_lt_mono; assumption.
      apply le_n_S.
      apply clsd.
      all: rewrite PeanoNat.Nat.succ_lt_mono; assumption.
    Qed.

    Theorem closed_narrow_substup2 : forall {σ : substitution} {m n' m' j : nat},
        (forall k, k < j -> m <= k -> closed_between (σ k) n' m') ->
        (forall k, k < S j -> S m <= k -> @closed_between (substup σ k) (S n') (S m')).
    Proof using.
      intros σ m n' m' j H0 k H1 H2; destruct k; cbn. constructor; lia.
      apply le_S_n in H2.
      apply @closed_between_ren with (k1' := n') (k2' := m').
      intros; rewrite <- PeanoNat.Nat.succ_lt_mono; assumption.
      apply le_n_S.
      apply H0; lia.
    Qed.

    Lemma closed_narrow_subst : forall {e : expr} {σ : substitution} {n m n' m' j : nat},
        (forall k, k < j -> k < n -> closed_between (σ k) n' m') ->
        (forall k, k < j -> m <= k -> closed_between (σ k) n' m') ->
        closed_above e j ->
        closed_between e n m ->
        closed_between (subst e σ) n' m'.
    Proof using.
      intro e; induction e; intros σ i j i' j' k clsd1 clsd2 clsdabv clsdbtwn;
        inversion clsdabv; subst; inversion clsdbtwn; subst; cbn;
        try lia; try (econstructor; repeat match goal with
               | [ H : forall k, k < ?j -> k < ?i -> closed_between (?σ k) ?i' ?j' |- context[substup ?σ]] =>
                   lazymatch goal with
                   | [_ : forall k, k < S j -> k < S i -> closed_between (substup σ k) (S i') (S j') |- _] => fail
                   | _ => pose proof (closed_narrow_substup1 H)
                   end
               | [ H : forall k, k < ?j -> ?m <= k -> closed_between (?σ k) ?i' ?j' |- context[substup ?σ]] =>
                   lazymatch goal with
                   | [_ : forall k, k < S j -> S m <= k  -> closed_between (substup σ k) (S i') (S j') |- _] => fail
                   | _ => pose proof (closed_narrow_substup2 H)
                   end
               end; eauto; fail).
      - apply clsd1; assumption.
      - apply clsd2; assumption.
    Qed.
    
  End Closure.
  
End CorpsSyntax.

Arguments type : clear implicits.
Arguments expr : clear implicits.
Arguments mod : clear implicits.


