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
  #[local] Notation mod := (@mod PName).
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
    | send (e : expr) (seen : nat) (m : mod) (p : PName) (q : PName)
    | up (e : expr)(seen : nat) (m : mod) (p : PName)
    | down (e : expr) (seen : nat) (m : mod) (p : PName).

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
      | send e1 seen1 m1 p1 q1, send e2 seen2 m2 p2 q2 =>
          expr_eqb e1 e2 && eqb seen1 seen2 && eqb m1 m2&& eqb p1 p2 && eqb q1 q2
      | up e1 seen1 m1 p1, up e2 seen2 m2 p2 =>
          expr_eqb e1 e2 && eqb seen1 seen2 && eqb m1 m2 && eqb p1 p2
      | down e1 seen1 m1 p1, down e2 seen2 m2 p2 =>
          expr_eqb e1 e2 && eqb seen1 seen2 && eqb m1 m2 && eqb p1 p2
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

    Definition renup_many (ξ : renaming) (n : nat) : renaming :=
      fun m =>
        if PeanoNat.Nat.ltb m n
        then m
        else n + (ξ (m - n)).

    Fixpoint renup_many' (ξ : renaming) (n : nat) : renaming :=
      match n with
      | 0 => ξ
      | S n' => renup_many' (renup ξ) n'
      end.

    (* Lemma renup_many_spec : forall ξ n m, renup_many ξ n m = renup_many' ξ n m. *)
    (* Proof using. *)
    (*   intros ξ n; revert ξ; induction n; intros ξ m; cbn. *)
    (*   - f_equal; apply PeanoNat.Nat.sub_0_r. *)
    (*   - rewrite <- IHn; unfold renup_many. *)
    (*     destruct (PeanoNat.Nat.ltb_spec m (S n)); *)
    (*       destruct (PeanoNat.Nat.ltb_spec m n); auto. *)
        
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
      | send e seen m p q => send (ren e ξ) seen m p q
      | up e seen m p => up (ren e ξ) seen m p
      | down e seen m p => down (ren e ξ) seen m p
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

    Definition substup_many (σ : substitution) (n : nat) : substitution :=
      fun m =>
        if PeanoNat.Nat.ltb m n
        then var m
        else ren (σ (m - n)) (fun k => n + k).

    Fixpoint substup_many' (σ : substitution) (n : nat) : substitution :=
      match n with
      | 0 => σ
      | S n' => substup_many' (substup σ) n'
      end.

    Lemma substup_many_eq : forall σ n m, substup_many σ n m = substup_many' σ n m.
    Proof using.
      intros σ n m; revert σ m; induction n; intros σ m; cbn.
      - rewrite PeanoNat.Nat.sub_0_r; rewrite ren_id; reflexivity.
      - rewrite <- IHn. unfold substup_many.
        destruct (PeanoNat.Nat.ltb_spec m n); cbn;
          destruct (PeanoNat.Nat.leb_spec m n); cbn; auto.
        -- exfalso; apply (PeanoNat.Nat.lt_irrefl n); transitivity m; auto.
        -- assert (n = m) by (apply PeanoNat.Nat.le_antisymm; auto); subst.
           rewrite PeanoNat.Nat.sub_diag; cbn.
           rewrite <- plus_n_O; reflexivity.
        -- assert (m - n <> 0) by (apply PeanoNat.Nat.sub_gt; exact H1).
           assert (exists k, m - n = S k). destruct (m - n) as [|k]; [exfalso; apply H2; reflexivity| exists k; reflexivity].
           destruct H3 as [k eq_k]; rewrite eq_k; cbn.
           rewrite ren_fusion.
           assert (m - S n = k) by (rewrite PeanoNat.Nat.sub_succ_r; rewrite eq_k; cbn; reflexivity).
           rewrite H3; apply ren_ext; intro j. apply plus_n_Sm.
    Qed.

    Lemma substup_many1 : forall σ n, substup σ n = substup_many σ 1 n.
    Proof using.
      intros σ n; destruct n; cbn; auto.
      rewrite PeanoNat.Nat.sub_0_r.
      reflexivity.
    Qed.

    Lemma substup_many_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall n m, substup_many σ1 n m = substup_many σ2 n m.
    Proof using.
      intros σ1 σ2 ext_eq n m; unfold substup_many; destruct (PeanoNat.Nat.ltb m n); [|rewrite ext_eq]; reflexivity.
    Qed.

    Lemma substup_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall n, substup σ1 n = substup σ2 n.
    Proof using.
      intros σ1 σ2 ext_eq n; destruct n; cbn; [|rewrite ext_eq]; reflexivity.
    Qed.

    Lemma id_substup_many : forall n m, substup_many id_substitution n m = id_substitution m.
    Proof using.
      intros; unfold substup_many; unfold id_substitution; destruct (PeanoNat.Nat.ltb_spec m n); cbn; [reflexivity|].
      f_equal.
      induction n; cbn.
      apply PeanoNat.Nat.sub_0_r.
      assert (n < m) as H1 by (rewrite PeanoNat.Nat.le_succ_l in H0; exact H0).
      rewrite PeanoNat.Nat.sub_succ_r.
      rewrite PeanoNat.Nat.add_pred_r.
      rewrite PeanoNat.Nat.lt_succ_pred with (z := n).
      -- apply IHn; apply PeanoNat.Nat.lt_le_incl; exact H1.
      --rewrite <- Arith_base.le_plus_minus_stt.
        rewrite PeanoNat.Nat.le_succ_l in H0; exact H0.
        apply PeanoNat.Nat.lt_le_incl; exact H1.
      -- apply PeanoNat.Nat.sub_gt; exact H1.
    Qed.

    Lemma id_substup :
      forall n, substup id_substitution n = id_substitution n.
    Proof using.
      intros n; destruct n; unfold id_substitution; cbn; reflexivity.
    Qed.

    (* Lemma renup_subst_manyup : forall ξ n m, *)
    (*     (fun k => var (renup ξ k)) m *)

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
      | send e seen m p q => send (subst e σ) seen m p q
      | up e seen m p => up (subst e σ) seen m p
      | down e seen m p => down (subst e σ) seen m p
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
          | [ H : forall n, ?f n = ?g n |- context[substup_many ?f ?n] ] =>
              pose proof (substup_many_ext f g H n)
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
          | [ |- context[subst ?e (substup_many id_substitution ?n)]] =>
              rewrite (subst_ext (substup_many id_substitution n) id_substitution
                         (id_substup_many n) e)
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
    | send_ca {e : expr} (seen : nat) (m : mod) (p q : PName) {n : nat} (pf : closed_above e n)
      : closed_above (send e seen m p q) n
    | up_ca {e : expr} (seen : nat) (m : mod) (p : PName) {n : nat} (pf : closed_above e n)
      : closed_above (up e seen m p) n
    | down_ca {e : expr} (seen : nat) (m : mod) (p : PName) {n : nat} (pf : closed_above e n)
      : closed_above (down e seen m p) n.

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
      | send e seen m p q => closed_aboveb e n
      | up e seen m p => closed_aboveb e n
      | down e seen m p => closed_aboveb e n
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
      | send e seen m p q => min_closure e
      | up e seen m p => min_closure e
      | down e seen m p => min_closure e
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
    
  End Closure.

  
  
End CorpsSyntax.

Arguments type : clear implicits.
Arguments expr : clear implicits.
Arguments mod : clear implicits.


