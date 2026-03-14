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
Require Import Syntax.

Create HintDb ctxts.

Section Contexts.
  Context {PName : Type} `{EqBool PName}.

  #[local] Abbreviation type := (type PName).
  #[local] Abbreviation expr := (expr PName).
  #[local] Abbreviation mod := (mod PName).
  #[local] Abbreviation base := (@base PName).
  #[local] Definition ptm := @proc_to_mod PName.
  Coercion ptm : PName >-> mod.
  Context {CanSend CanUp CanDown : mod -> mod -> Prop}.


  Inductive Ctxt :=
    EmptyCtxt: Ctxt
  | VarExt : Ctxt -> mod -> type -> Ctxt
  | LockExt : Ctxt -> mod -> Ctxt.

  Section CtxtEquality.
    Fixpoint ctxt_eq_bool (Γ Δ : Ctxt) : bool :=
      match Γ, Δ with
      | EmptyCtxt, EmptyCtxt => true
      | VarExt Γ' m τ, VarExt Δ' m' τ' => eqb m m' && eqb τ τ' && ctxt_eq_bool Γ' Δ'
      | LockExt Γ' m, LockExt Δ' m' => eqb m m' && ctxt_eq_bool Γ' Δ'
      | _, _ => false
      end.

    Lemma ctxt_eq_bool_liebniz : forall Γ Δ, ctxt_eq_bool Γ Δ = true -> Γ = Δ.
    Proof using.
      intro Γ; solve_eqb_liebniz Γ.
    Qed.

    Lemma ctxt_eq_bool_refl : forall Γ, ctxt_eq_bool Γ Γ = true.
    Proof using.
      intro Γ; solve_eqb_refl.
    Qed.

    Global Instance CtxtEqBool : EqBool Ctxt :=
      {
        eqb := ctxt_eq_bool;
        eqb_liebniz := ctxt_eq_bool_liebniz;
        eqb_refl := ctxt_eq_bool_refl
      }.
  End CtxtEquality.
  
  Section BasicFunctions.

    Fixpoint num_vars (Γ : Ctxt) : nat :=
      match Γ with
      | EmptyCtxt => 0
      | VarExt Γ _ _ => S (num_vars Γ)
      | LockExt Γ _ => num_vars Γ
      end.
    
    Fixpoint vars (Γ : Ctxt) (n : nat) : option (mod * type) :=
      match Γ, n with
      | EmptyCtxt, _ => None
      | VarExt _ m τ, 0 => Some (m, τ)
      | VarExt Γ _ _, S n => vars Γ n
      | LockExt Γ _, n => vars Γ n
      end.

    Lemma vars_within_num1 : forall Γ n, n < num_vars Γ -> vars Γ n <> None.
    Proof using.
      intro Γ; induction Γ; cbn; intros n n_lt_num_vars.
      - inversion n_lt_num_vars.
      - destruct n; [discriminate|]; apply IHΓ; apply PeanoNat.Nat.succ_lt_mono; assumption.
      - apply IHΓ; assumption.
    Qed.

    Lemma vars_within_num2 : forall Γ n, vars Γ n <> None -> n < num_vars Γ.
    Proof using.
      intro Γ; induction Γ; cbn; intros n neq.
      - exfalso; apply neq; reflexivity.
      - destruct n; [apply PeanoNat.Nat.lt_0_succ|].
        apply -> PeanoNat.Nat.succ_lt_mono; apply IHΓ; assumption.
      - apply IHΓ; assumption.
    Qed.

    Corollary vars_within_num3 : forall Γ n m, vars Γ n = Some m -> n < num_vars Γ.
    Proof using.
      intros Γ n m eq; apply vars_within_num2; rewrite eq; discriminate.
    Qed.

    Theorem vars_within_num : forall Γ n, n < num_vars Γ <-> vars Γ n <> None.
    Proof using.
      intros Γ n; split; [apply vars_within_num1 | apply vars_within_num2].
    Qed.

    Fixpoint locks (Γ : Ctxt) (n : nat) : option mod :=
      match Γ, n with
      | EmptyCtxt, _ => None
      | VarExt _ _ _, 0 => Some base
      | VarExt Γ _ _, S n => locks Γ n
      | LockExt Γ m, n =>
          match locks Γ n with
          | None => None
          | Some m' => Some (mod_app m' m)
          end
      end.

    Fixpoint all_locks (Γ : Ctxt) : mod :=
      match Γ with
      | EmptyCtxt => base
      | VarExt Γ _ _ => all_locks Γ
      | LockExt Γ m => mod_app (all_locks Γ) m
      end.

    Lemma locks_sub_all_locks : forall Γ n m,
        locks Γ n = Some m ->
        SuffixOf m (all_locks Γ).
    Proof using.
      intro Γ; induction Γ; intros n m' eq; cbn in eq; try discriminate; [destruct n; cbn in eq; [inversion eq; subst|]|].
      constructor.
      apply IHΓ with (n := n); auto.
      destruct (locks Γ n) eqn:eq'; inversion eq; subst.
      apply SuffixOf_modapp. apply IHΓ with (n := n); auto.
    Qed.
  End BasicFunctions.


  Section InContext.

    Inductive InCtxt : nat -> mod -> type -> mod -> Ctxt -> Prop :=
    | hereInCtxt (Γ : Ctxt) (m : mod) (τ : type) : InCtxt 0 m τ base (VarExt Γ m τ)
    | thereVarInCtxt {Γ : Ctxt} {n : nat} {m1 m : mod} {τ1 : type} (m2 : mod) (τ2 : type)
        (i : InCtxt n m1 τ1 m Γ) : InCtxt (S n) m1 τ1 m (VarExt Γ m2 τ2)
    | thereLockInCtxt {Γ : Ctxt} {n : nat} {m m1 : mod} {τ : type} (m2 : mod)
        (i : InCtxt n m τ m1 Γ) : InCtxt n m τ (mod_app m1 m2) (LockExt Γ m2).

    Lemma InCtxt_vars_locks1 : forall Γ n m τ m',
        InCtxt n m τ m' Γ ->
        locks Γ n = Some m'.
    Proof using.
      intros Γ n m τ m' i; induction i; cbn;  try reflexivity; try apply IHi.
      rewrite IHi; reflexivity.
    Qed.

    Lemma InCtxt_vars_locks2 : forall Γ n m τ m',
        InCtxt n m τ m' Γ ->
        vars Γ n = Some (m, τ).
    Proof using.
      intros Γ n m τ m' i; induction i; cbn; auto.
    Qed.

    Lemma InCtxt_vars_locks3 : forall Γ n m τ m',
        locks Γ n = Some m' ->
        vars Γ n = Some (m, τ) ->
        InCtxt n m τ m' Γ.
    Proof using.
      intros Γ; induction Γ; intro n; destruct n; intros m' τ m'' locks_eq vars_eq; cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _] => inversion H
          | [H : Some ?a = Some ?b |- _ ] =>
              inversion H; clear H; subst
          | [ IH : forall n m τ m', locks ?Γ n = Some m' -> vars ?Γ n = Some (m, τ) -> InCtxt n m τ m' ?Γ,
                H1 : locks ?Γ ?n = Some ?m', H2 : vars ?Γ ?n = Some (?m, ?τ) |- _ ] =>
              lazymatch goal with
              | [ _ : InCtxt n m τ m' Γ |- _ ] => fail
              | _ => pose proof (IH n m τ m' H1 H2)
              end
          end.
      all: try (econstructor; eauto; fail).
      - destruct (locks Γ 0) eqn: locks_eq'; inversion locks_eq; clear locks_eq; subst.
        constructor; apply IHΓ; auto.
      - destruct (locks Γ (S n)) eqn: locks_eq'; inversion locks_eq; clear locks_eq; subst.
        constructor; apply IHΓ; auto.
    Qed.

    Theorem InCtxt_vars_locks : forall Γ n m τ m',
        InCtxt n m τ m' Γ <->
          locks Γ n = Some m' /\
            vars Γ n = Some (m, τ).
    Proof using.
      intros Γ n m τ m'; split; intro H0; [split; [eapply InCtxt_vars_locks1 |eapply InCtxt_vars_locks2 ] | destruct H0; eapply InCtxt_vars_locks3]; eauto.
    Qed.

  End InContext.

  Section ContextEquivalence.

    Inductive ctxt_equiv : Ctxt -> Ctxt -> Prop :=
    | EmptyCtxtEquiv : ctxt_equiv EmptyCtxt EmptyCtxt
    | VarExtEquiv: forall {Γ Δ : Ctxt} (m : mod) (τ : type), ctxt_equiv Γ Δ -> ctxt_equiv (VarExt Γ m τ) (VarExt Δ m τ)
    | LockExtEquiv : forall {Γ Δ : Ctxt} (m : mod), ctxt_equiv Γ Δ -> ctxt_equiv (LockExt Γ m) (LockExt Δ m)
    (* | VarSwapEquiv : forall {Γ Δ : Ctxt} (m1 m2 : mod) (τ1 τ2 : type), *)
    (*     ctxt_equiv Γ Δ -> ctxt_equiv (VarExt (VarExt Γ m1 τ1) m2 τ2) (VarExt (VarExt Δ m2 τ2) m1 τ1) *)
    | LockCollapseEquiv : forall {Γ Δ : Ctxt} (m1 m2 : mod),
        ctxt_equiv Γ Δ -> ctxt_equiv (LockExt (LockExt Γ m1) m2) (LockExt Δ (mod_app m1 m2))
    | LockSplitEquiv : forall {Γ Δ : Ctxt} (m1 m2 : mod),
        ctxt_equiv Γ Δ -> ctxt_equiv (LockExt Γ (mod_app m1 m2)) (LockExt (LockExt Δ m1) m2)
    | LockNothingEquiv1 : forall {Γ Δ : Ctxt},
        ctxt_equiv Γ Δ -> ctxt_equiv Γ (LockExt Δ base)
    | LockNothingEquiv2 : forall {Γ Δ : Ctxt},
        ctxt_equiv Γ Δ -> ctxt_equiv (LockExt Γ base) Δ
    | CtxtEquivTrans : forall {Γ Δ E: Ctxt},
        ctxt_equiv Γ Δ -> ctxt_equiv Δ E -> ctxt_equiv Γ E. (* I Think I can get rid of this, but it doesn't seem worth the effort. *)

    Theorem ctxt_equiv_refl : forall Γ : Ctxt, ctxt_equiv Γ Γ.
    Proof using.
      intro Γ; induction Γ; constructor; auto.
    Qed.

    Theorem ctxt_equiv_sym : forall {Γ Δ : Ctxt}, ctxt_equiv Γ Δ -> ctxt_equiv Δ Γ.
    Proof using.
      intros Γ Δ eqv; induction eqv; econstructor; eauto.
    Qed.

    Global Instance CtxtEquivRefl : Reflexive ctxt_equiv := ctxt_equiv_refl.
    Global Instance CtxtEquivSym : Symmetric ctxt_equiv := @ctxt_equiv_sym.
    Global Instance CtxtEquivTrans' : Transitive ctxt_equiv := fun Γ Δ E pf1 pf2 => CtxtEquivTrans pf1 pf2.

    Lemma num_vars_proper : forall {Γ Δ}, ctxt_equiv Γ Δ -> num_vars Γ = num_vars Δ.
    Proof using.
      intros Γ Δ eqv; induction eqv; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : num_vars ?Γ = num_vars ?Δ |- num_vars ?Γ = num_vars ?Δ] => exact IH
          | [ IH : num_vars ?Γ = num_vars ?Δ |- context[num_vars ?Γ]] => rewrite IH
          end.
    Qed.

    Lemma vars_proper : forall {Γ Δ}, ctxt_equiv Γ Δ -> forall n, vars Γ n = vars Δ n.
    Proof using.
      intros Γ Δ eqv; induction eqv; intros n; cbn.
      2: destruct n.
      all: repeat match goal with
             | [ |- ?a = ?a ] => reflexivity
             | [IH : forall n, vars ?Γ n = vars ?Δ n |- vars ?Γ ?n = vars ?Δ ?n] => exact (IH n)
             | [IH : forall n, vars ?Γ n = vars ?Δ n |- context[vars ?Γ ?n]] => rewrite (IH n)
             end.
    Qed.

    Lemma locks_proper : forall {Γ Δ}, ctxt_equiv Γ Δ -> forall n, locks Γ n = locks Δ n.
    Proof using.
      intros Γ Δ eqv; induction eqv; intros n; cbn.
      2: destruct n.
      all: repeat match goal with
             | [ |- ?a = ?a ] => reflexivity
             | [ IH : forall n, locks ?Γ n = locks ?Δ n |- context[locks ?Γ ?n]] => rewrite (IH n)
             end; destruct (locks  Δ n); auto; rewrite mod_app_assoc; reflexivity.
    Qed.

    Lemma all_locks_proper : forall {Γ Δ}, ctxt_equiv Γ Δ -> all_locks Γ = all_locks Δ.
    Proof using.
      intros Γ Δ eqv; induction eqv; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : all_locks ?Γ = all_locks ?Δ |- context[all_locks ?Γ]] => rewrite IH
          end; rewrite mod_app_assoc; reflexivity.
    Qed.

    Lemma InCtxt_proper' : forall {Γ Δ}, ctxt_equiv Γ Δ -> forall n m τ m', InCtxt n m τ m' Γ -> InCtxt n m τ m' Δ.
    Proof using.
      intros Γ Δ eqv; induction eqv; intros n m' τ' m'' inc;
        try (inversion inc; subst; econstructor; eauto; fail); auto.
      - inversion inc; subst; inversion i; subst.
        rewrite mod_app_assoc; constructor; apply IHeqv; assumption.
      - inversion inc; subst.
        rewrite <- mod_app_assoc; do 2 constructor; apply IHeqv; assumption.
      - assert (m'' = mod_app m'' base) as eq by reflexivity; rewrite eq.
        constructor; apply IHeqv; assumption.
      - inversion inc; subst; cbn in *; apply IHeqv; assumption.
    Qed.

    Corollary InCtxt_proper : forall {Γ Δ}, ctxt_equiv Γ Δ -> forall n m τ m', InCtxt n m τ m' Γ <-> InCtxt n m τ m' Δ.
    Proof using.
      intros Γ Δ H0 n m τ m'; split; intro H1; [| symmetry in H0]; eapply InCtxt_proper'; eauto.
    Qed.

    Lemma LockNothingEquiv1_inv : forall Γ Δ,
        ctxt_equiv Γ (LockExt Δ base) ->
        ctxt_equiv Γ Δ.
    Proof using.
      intros Γ Δ; generalize (@eq_refl _ (LockExt Δ base)); generalize (LockExt Δ base) at 1 3; intros c eq eqv; revert Δ eq; induction eqv; intros Δ' eq; inversion eq; subst.
      all: try (econstructor; eauto; fail).
      - apply mod_app_base_inv in H2; destruct H2; subst; cbn.
        do 2 constructor; assumption.
      - assumption.
    Qed.

  End ContextEquivalence.

  Section ContextNormalForm.
    
    Definition not_lock (Γ : Ctxt) : Prop :=
      match Γ with
      | LockExt _ _ => False
      | _ => True
      end.
    
    Fixpoint ctxt_nf (Γ : Ctxt) : Prop :=
      match Γ with
      | EmptyCtxt => True
      | VarExt Γ' _ _ => ctxt_nf Γ'
      | LockExt Γ' m => m <> base /\ not_lock Γ' /\ ctxt_nf Γ'
      end.
    
    Fixpoint collect_ctxt_locks  (Γ : Ctxt) (m : mod) :=
      match Γ with
      | EmptyCtxt => if eqb m base then EmptyCtxt else LockExt EmptyCtxt m
      | VarExt Γ m' τ => if eqb m base then VarExt Γ m' τ else LockExt (VarExt Γ m' τ) m
      | LockExt Γ m' => collect_ctxt_locks Γ (mod_app m' m)
      end.

    Lemma collect_ctxt_locks_equiv : forall Γ m, ctxt_equiv (collect_ctxt_locks Γ m) (LockExt Γ m).
    Proof using.
      intro Γ; induction Γ; try rename m into m'; intro m; cbn; eq_bool; subst; try (apply ctxt_equiv_refl); try (apply LockNothingEquiv1; apply ctxt_equiv_refl; fail).
      transitivity (LockExt Γ (mod_app m' m)). apply IHΓ. apply LockSplitEquiv; reflexivity.
    Qed.

    Lemma collect_locks_proper : forall Γ Δ m, ctxt_equiv Γ Δ -> ctxt_equiv (collect_ctxt_locks Γ m) (collect_ctxt_locks Δ m).
    Proof using.
      intros Γ Δ m ceqv; revert m; induction ceqv; intro m'; cbn; eq_bool; subst; try (econstructor; eauto; fail); try reflexivity;
        try rewrite mod_app_assoc; try rewrite mod_base_app; auto.
      repeat constructor; auto.
    Qed.

    Lemma collect_not_lock : forall Γ m, not_lock Γ -> collect_ctxt_locks Γ m = if eqb m base then Γ else LockExt Γ m.
    Proof using.
      intro Γ; destruct Γ; intro m'; cbn; intro nl_Γ; eq_bool; subst; cbn; auto; destruct nl_Γ.
    Qed.

    Lemma collect_locks_base_nf : forall Γ, ctxt_nf Γ -> collect_ctxt_locks Γ base = Γ.
    Proof using.
      intro Γ; induction Γ; cbn; intro nf_Γ; eq_bool; subst ;auto.
      destruct nf_Γ as [m_neq_base [not_lock_Γ nf_Γ]].
      rewrite collect_not_lock; [| assumption];
        destruct (eqb m base) eqn:eq; [ apply eqb_liebniz in eq; exfalso; apply m_neq_base; exact eq | reflexivity].
    Qed.

    Lemma collect_locks_preserve_nf : forall Γ m, ctxt_nf Γ -> ctxt_nf (collect_ctxt_locks Γ m).
    Proof using.
      intro Γ; induction Γ; cbn; intros m' nf_Γ; eq_bool; subst; auto; try (repeat constructor; auto).
      destruct nf_Γ as [m_neq_base [nl_Γ nf_Γ]]; apply IHΓ; auto.
    Qed.

    Lemma collect_locks_twice : forall Γ m1 m2, collect_ctxt_locks (collect_ctxt_locks Γ m1) m2 = collect_ctxt_locks Γ (mod_app m1 m2).
    Proof using.
      intro Γ; induction Γ; intros m1 m2; cbn; eq_bool; subst; cbn in *; eq_bool; subst; auto;
        repeat match goal with
          | [ H : context[mod_app base _] |- _ ] => rewrite mod_base_app in H
          | [ |- context[mod_app base _] ] => rewrite mod_base_app
          end; cbn in *; eq_bool; subst; auto.
      -  rewrite IHΓ; rewrite mod_app_assoc; reflexivity.
    Qed.

    Fixpoint ctxt_normalize (Γ : Ctxt) :=
      match Γ with
      | EmptyCtxt => EmptyCtxt
      | VarExt Γ m τ => VarExt (ctxt_normalize Γ) m τ
      | LockExt Γ m => collect_ctxt_locks (ctxt_normalize Γ) m
      end.

    Lemma ctxt_normalize_nf : forall Γ, ctxt_nf (ctxt_normalize Γ).
    Proof using.
      intro Γ; induction Γ; cbn; auto.
      apply collect_locks_preserve_nf; apply IHΓ.
    Qed.

    Lemma ctxt_normalize_equiv : forall Γ, ctxt_equiv Γ (ctxt_normalize Γ).
    Proof using.
      intro Γ; induction Γ; cbn; try (constructor; auto; reflexivity; fail).
      transitivity (collect_ctxt_locks Γ m). symmetry; apply collect_ctxt_locks_equiv.
      apply collect_locks_proper; exact IHΓ.
    Qed.

    Corollary eq_normal_equiv : forall Γ Δ, ctxt_normalize Γ = ctxt_normalize Δ -> ctxt_equiv Γ Δ.
    Proof using.
      intros Γ Δ eq; transitivity (ctxt_normalize Γ); [|rewrite eq; symmetry]; apply ctxt_normalize_equiv.
    Qed.

    Lemma equiv_eq_normal : forall Γ Δ, ctxt_equiv Γ Δ -> ctxt_normalize Γ = ctxt_normalize Δ.
    Proof using.
      intros Γ Δ eqv; induction eqv; cbn; subst; try rewrite IHeqv; auto.
      apply collect_locks_twice.
      symmetry; apply collect_locks_twice.
      1,2 : rewrite collect_locks_base_nf; [reflexivity| apply ctxt_normalize_nf].
      transitivity (ctxt_normalize Δ); auto.
    Qed.

    Definition ctxt_equivb (Γ Δ : Ctxt) : bool := eqb (ctxt_normalize Γ) (ctxt_normalize Δ).

    Lemma ctxt_equivb_equiv : forall Γ Δ, ctxt_equivb Γ Δ = true -> ctxt_equiv Γ Δ.
    Proof using.
      intros Γ Δ eq; unfold ctxt_equivb in eq; eq_bool; subst.
      apply eq_normal_equiv; auto.
    Qed.

    Lemma ctxt_equiv_equivb : forall Γ Δ, ctxt_equiv Γ Δ -> ctxt_equivb Γ Δ = true.
    Proof using.
      intros Γ Δ eqv; unfold ctxt_equivb; apply equiv_eq_normal in eqv; rewrite eqv; apply eqb_refl.
    Qed.

  End ContextNormalForm.

  Section ContextApp.

    Fixpoint ctxt_app (Γ Δ : Ctxt) : Ctxt :=
      match Δ with
      | EmptyCtxt => Γ
      | VarExt Δ m τ => VarExt (ctxt_app Γ Δ) m τ
      | LockExt Δ m => LockExt (ctxt_app Γ Δ) m
      end.

    Theorem ctxt_app_proper : forall Γ1 Γ2 Δ1 Δ2,
        ctxt_equiv Γ1 Γ2 ->
        ctxt_equiv Δ1 Δ2 ->
        ctxt_equiv (ctxt_app Γ1 Δ1) (ctxt_app Γ2 Δ2).
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 eqvΓ eqvΔ; revert Γ1 Γ2 eqvΓ; induction eqvΔ; try rename Γ into Δ1; try rename Δ into Δ2; intros Γ1 Γ2 eqvΓ; cbn; auto.
      all: try (econstructor; eauto; fail).
      transitivity (ctxt_app Γ2 Δ2). apply IHeqvΔ1; auto. apply IHeqvΔ2; reflexivity.
    Qed.

    Theorem ctxt_app_identity_left : forall Γ, ctxt_app EmptyCtxt Γ = Γ.
    Proof using.
      intro Γ; induction Γ; cbn; try rewrite IHΓ; reflexivity.
    Qed.

    Theorem ctxt_app_identity_right : forall Γ, ctxt_app Γ EmptyCtxt = Γ. Proof using. reflexivity. Qed.

    Theorem ctxt_app_assoc : forall Γ Δ E, ctxt_app (ctxt_app Γ Δ) E = ctxt_app Γ (ctxt_app Δ E).
    Proof using.
      intros Γ Δ E; revert Γ Δ; induction E as [| E IHE m τ | E IHE m]; intros Γ Δ; cbn; try rewrite IHE; reflexivity.
    Qed.

    Lemma ctxt_app_num_vars : forall Γ Δ, num_vars (ctxt_app Γ Δ) = num_vars Γ + num_vars Δ.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m τ | Δ IHΔ m]; intro Γ; cbn; try rewrite IHΔ; lia.
    Qed.

    Lemma ctxt_app_vars1 : forall Γ Δ n m τ, vars Δ n = Some (m, τ) -> vars (ctxt_app Γ Δ) n = Some (m, τ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m' τ' | Δ IHΔ m']; intros Γ n m τ eq; cbn in *; try discriminate; [destruct n | ]; auto.
    Qed.

    Lemma ctxt_app_vars2 : forall Γ Δ n m τ, vars Γ n = Some (m, τ) -> vars (ctxt_app Γ Δ) (n + num_vars Δ) = Some (m, τ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m' τ' | Δ IHΔ m']; intros Γ n m τ eq; cbn in *.
      - rewrite <- plus_n_O; assumption.
      - rewrite <- plus_n_Sm; apply IHΔ; assumption.
      - apply IHΔ; assumption.
    Qed.

    Corollary ctxt_app_vars : forall Γ Δ n, vars (ctxt_app Γ Δ) n =
                                              if PeanoNat.Nat.ltb n (num_vars Γ + num_vars Δ)
                                              then if PeanoNat.Nat.ltb n (num_vars Δ) then vars Δ n else vars Γ (n - num_vars Δ)
                                              else None.
    Proof using.
      intros Γ Δ n; destruct (PeanoNat.Nat.ltb_spec n (num_vars Γ + num_vars Δ)); [destruct (PeanoNat.Nat.ltb_spec n (num_vars Δ))|].
      - apply vars_within_num in H1; destruct (vars Δ n) as [[m τ]|] eqn:eq; [| exfalso; apply H1; reflexivity].
        apply ctxt_app_vars1; assumption.
      - assert (n = (n - num_vars Δ) + num_vars Δ) as eq by lia.
        rewrite eq at 1.
        assert (n - num_vars Δ < num_vars Γ) as eq' by lia;  apply vars_within_num in eq'.
        destruct (vars Γ (n - num_vars Δ)) as [[m τ]|] eqn:eq''; [| exfalso; apply eq'; reflexivity].
        apply ctxt_app_vars2; assumption.
      - destruct (vars (ctxt_app Γ Δ)) as [[m τ]|] eqn:eq; [| reflexivity];
          assert (vars (ctxt_app Γ Δ) n <> None) as H1 by (intro eq'; rewrite eq' in eq; inversion eq); apply vars_within_num2 in H1;
          rewrite ctxt_app_num_vars in H1; lia.
    Qed.

    Lemma ctxt_app_locks1 : forall Γ Δ n m, locks Δ n = Some m -> locks (ctxt_app Γ Δ) n = Some m.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m' τ | Δ IHΔ m']; intros Γ n m eq; cbn in *; try discriminate.
      - destruct n; auto.
      - destruct (locks Δ n) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
        apply IHΔ with (Γ := Γ) in eq; rewrite eq; reflexivity.
    Qed.

    Lemma ctxt_app_locks2 : forall Γ Δ n m, locks Γ n = Some m -> locks (ctxt_app Γ Δ) (n + num_vars Δ) = Some (mod_app m (all_locks Δ)).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m' τ | Δ IHΔ m']; intros Γ n m eq; cbn in *; try discriminate.
      - rewrite <- plus_n_O; assumption.
      - rewrite <- plus_n_Sm; apply IHΔ; assumption.
      - rewrite IHΔ with (m := m); [| assumption]; rewrite mod_app_assoc; reflexivity.
    Qed.

    Lemma ctxt_app_all_locks : forall Γ Δ, all_locks (ctxt_app Γ Δ) = mod_app (all_locks Γ) (all_locks Δ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m τ | Δ IHΔ m]; intro Γ; cbn; auto.
      rewrite IHΔ; apply mod_app_assoc.
    Qed.

    Lemma InCtxt_app1 : forall Γ Δ n m τ m', InCtxt n m τ m' Δ -> InCtxt n m τ m' (ctxt_app Γ Δ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m'' τ' | Δ IHΔ m'']; intros Γ n m τ m' inc; cbn; inversion inc; subst;
        constructor; apply IHΔ; auto.
    Qed.

    Lemma InCtxt_app2 : forall Γ Δ n m τ m', InCtxt n m τ m' Γ -> InCtxt (n + num_vars Δ) m τ (mod_app m' (all_locks Δ)) (ctxt_app Γ Δ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ as [| Δ IHΔ m'' τ' | Δ IHΔ m'']; intros Γ n m τ m' inc; cbn.
      - rewrite <- plus_n_O; assumption.
      - rewrite <- plus_n_Sm; constructor; apply IHΔ; assumption.
      - rewrite <- mod_app_assoc; constructor; apply IHΔ; assumption.
    Qed.

    Lemma ctxt_app_empty_inv1 : forall Γ Δ, EmptyCtxt = ctxt_app Γ Δ ->
                                            Γ = EmptyCtxt.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; cbn; intros Γ eq; auto; inversion eq.
    Qed.
    
  End ContextApp.

  Section NonVar.

    Inductive NonVar : Ctxt -> Prop :=
    | EmptyNonVar : NonVar EmptyCtxt
    | LockNonVar (Γ : Ctxt) (m : mod) : m <> base -> NonVar (LockExt Γ m)
    | BaseLockNonVar (Γ : Ctxt) : NonVar Γ -> NonVar (LockExt Γ base).

    Lemma nonvar_equiv : forall Γ Δ,
        ctxt_equiv Γ Δ ->
        NonVar Γ ->
        NonVar Δ.
    Proof using H.
      intros Γ Δ eqv; induction eqv; intro nv; inversion nv; subst;
        try (econstructor; eauto; fail).
      - apply LockNonVar. intro eq. apply mod_app_base_inv in eq; destruct eq.
        auto. 
      - inversion H1; subst.
        cbn. constructor; auto. cbn; constructor; apply IHeqv; assumption.
      - destruct (eqb m2 base) eqn:eq; eq_bool; subst; cbn in *.
        apply BaseLockNonVar; apply LockNonVar; assumption.
        apply LockNonVar; assumption.
      - symmetry in H2; apply mod_app_base_inv in H2; destruct H2; subst.
        do 2 apply BaseLockNonVar; apply IHeqv; assumption.
      - exfalso; apply H1; reflexivity.
      - apply IHeqv; auto.
      - apply IHeqv2; apply IHeqv1; auto.
      - apply IHeqv2; apply IHeqv1; auto.
      - apply IHeqv2; apply IHeqv1; auto.
    Qed.

  End NonVar.
  Section Emptoid.
    
    Inductive Emptoid : Ctxt -> Prop :=
    | EmptyEmptoid : Emptoid EmptyCtxt
    | LockEmptoid (Γ : Ctxt) (emptd : Emptoid Γ) : Emptoid (LockExt Γ base).

    Lemma emptoid_equiv : forall {Γ : Ctxt},
        Emptoid Γ -> ctxt_equiv EmptyCtxt Γ.
    Proof using.
      intros Γ emptd; induction emptd. reflexivity.
      apply LockNothingEquiv1; assumption.
    Qed.

    Lemma Emptoid_from_Equiv : forall Γ Δ,
        Emptoid Γ -> ctxt_equiv Γ Δ -> Emptoid Δ.
    Proof using.
      intros Γ Δ etd eqv; revert etd; induction eqv; intro etd; inversion etd; subst;
        try (constructor; auto; fail); auto.
      - inversion emptd; subst. cbn. constructor; auto.
      - destruct (mod_app_base_inv m1 m2 (eq_sym H2)); subst; do 2 constructor; auto.
    Qed.

    Corollary equiv_empty_emptoid1 : forall Γ,
        ctxt_equiv EmptyCtxt Γ -> Emptoid Γ.
    Proof using.
      intros Γ H0;
        apply Emptoid_from_Equiv with (Γ := EmptyCtxt); [ constructor | assumption].
    Qed.      

    Corollary equiv_empty_emptoid2 : forall Γ,
        ctxt_equiv Γ EmptyCtxt -> Emptoid Γ.
    Proof using.
      intros Γ H0;
        apply Emptoid_from_Equiv with (Γ := EmptyCtxt); [ constructor | symmetry; assumption].
    Qed.

    Lemma emptoid_nonvar : forall Γ, Emptoid Γ -> NonVar Γ.
    Proof using.
      intro Γ; induction Γ; intro etd. constructor. exfalso; inversion etd.
      assert (m = base) by (inversion etd; subst; auto). subst.
      apply BaseLockNonVar. apply IHΓ. inversion etd; subst; auto.
    Qed.

  End Emptoid.

  Section Varoid.
    
    Inductive Varoid : Ctxt -> mod -> type -> Ctxt -> Prop :=
    | VarVaroid (Γ : Ctxt) (m : mod) (τ : type) :
      Varoid Γ m τ (VarExt Γ m τ)
    | EmptyLockVaroid (Γ : Ctxt) (m : mod) (τ : type) (Δ : Ctxt) (vd : Varoid Γ m τ Δ)
      : Varoid Γ m τ (LockExt Δ base).

    Theorem ctxt_equiv_varoid : forall {Γ Δ E m τ},
        Varoid Γ m τ Δ ->
        ctxt_equiv Δ E ->
        exists Γ', Varoid Γ' m τ E /\ ctxt_equiv Γ Γ'.
    Proof using.
      intros Γ Δ E m τ vd eqv; revert Γ m τ vd; induction eqv; intros Γ' m' τ' vd.
      - inversion vd.
      - inversion vd; subst; exists Δ; split; [constructor | assumption].
      - inversion vd; subst. specialize (IHeqv Γ' m' τ' vd0).
        destruct IHeqv as [Γ'' [vd' eqv']].
        exists Γ''; split; [constructor|]; assumption.
      - inversion vd; subst. inversion vd0; subst; cbn.
        destruct (IHeqv Γ' m' τ' vd1) as [Γ'' [vd' eqv']].
        exists Γ''; split; [constructor|]; assumption.
      - inversion vd; subst.
        symmetry in H5; apply mod_app_base_inv in H5; destruct H5; subst; cbn in vd.
        destruct (IHeqv Γ' m' τ' vd0) as [Γ'' [vd' eqv']].
        exists Γ''; split; [do 2 constructor|]; assumption.
      - destruct (IHeqv Γ' m' τ' vd) as [Γ'' [vd' eqv']].
        exists Γ''; split; [constructor|]; assumption.
      - inversion vd; subst; destruct (IHeqv Γ' m' τ' vd0) as [Γ'' [vd' eqv']].
        exists Γ''; split; assumption.
      - destruct (IHeqv1 Γ' m' τ' vd) as [Γ'1 [vd1 eqv1']].
        destruct (IHeqv2 Γ'1 m' τ' vd1) as [Γ'2 [vd2 eqv2']].
        exists Γ'2; split. assumption. transitivity Γ'1; assumption.
    Qed.
    
    Theorem varoid_ctxt_equiv : forall Γ Γ' Δ E m τ,
        Varoid Γ m τ Δ ->
        Varoid Γ' m τ E ->
        ctxt_equiv Γ Γ' ->
        ctxt_equiv Δ E.
    Proof using.
      intros Γ Γ' Δ E m τ vdΔ; revert E Γ'; induction vdΔ; intros E Γ' vdE eqv.
      - induction vdE.
        --  apply VarExtEquiv; transitivity Γ; [symmetry|]. reflexivity.
            assumption.
        --  apply LockNothingEquiv1; apply IHvdE; assumption.
      - apply LockNothingEquiv2; apply IHvdΔ with (Γ' := Γ'); assumption.
    Qed.

  End Varoid.

  Section ContextLeq.

    Inductive ctxt_leq : Ctxt -> renaming -> Ctxt -> Prop :=
    | EmptyCtxtLeq'' {ξ : renaming} :
      (forall n, ξ n = n) -> 
      ctxt_leq EmptyCtxt ξ EmptyCtxt
    | VarExtLeq'' : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
        (forall n, ξ2 n = renup ξ1 n) -> 
        ctxt_leq Γ ξ1 Δ ->
        ctxt_leq (VarExt Γ m τ) ξ2 (VarExt Δ m τ)
    | LockExtLeq'' : forall {Γ Δ : Ctxt} {ξ : renaming} (m : mod),
        ctxt_leq Γ ξ Δ ->
        ctxt_leq (LockExt Γ m) ξ (LockExt Δ m)
    | VarAddLeq'' : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
        ctxt_leq Γ ξ1 Δ ->
        (forall n, ξ2 n = S (ξ1 n)) ->
        ctxt_leq Γ ξ2 (VarExt Δ m τ)
    | VarSwapLeq'' : forall (Γ : Ctxt) (m1 m2 : mod) (τ1 τ2 : type) (ξ : renaming),
        (ξ 0 = 1) ->
        (ξ 1 = 0) ->
        (forall n, ξ (S (S n)) = S (S n)) ->
        ctxt_leq (VarExt (VarExt Γ m1 τ1) m2 τ2) ξ (VarExt (VarExt Γ m2 τ2) m1 τ1)
    | LockCollapseLeq'' : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt (LockExt Γ m1) m2) ξ (LockExt Γ (mod_app m1 m2))
    | LockSplitLeq'' : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt Γ (mod_app m1 m2)) ξ (LockExt (LockExt Γ m1) m2)
    | LockNothingLeq1'' : forall (Γ : Ctxt) (ξ : renaming),
        (forall n, ξ n = n) ->
        ctxt_leq Γ ξ (LockExt Γ base)
    | LockNothingLeq2'' : forall (Γ : Ctxt) (ξ : renaming),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt Γ base) ξ Γ
    | CtxtLeq''Trans : forall {Γ Δ E : Ctxt} {ξ1 ξ2 : renaming} (ξ3 : renaming),
        (forall n, ξ3 n = ξ2 (ξ1 n)) -> 
        ctxt_leq Γ ξ1 Δ ->
        ctxt_leq Δ ξ2 E ->
        ctxt_leq Γ ξ3 E.

    Theorem ctxt_leq_ext : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming},
        (forall n, ξ1 n = ξ2 n) -> 
        ctxt_leq Γ ξ1 Δ ->
        ctxt_leq Γ ξ2 Δ.
    Proof using.
      intros Γ Δ ξ1 ξ2 ext_eq lq; revert ξ2 ext_eq; induction lq; intros ξ1' ext_eq;
        try (econstructor; eauto; fail).
      - apply EmptyCtxtLeq''. intro n. rewrite <- ext_eq. apply H0.
      - apply @VarExtLeq'' with (ξ1 := ξ1); auto.
        intro n. rewrite <- ext_eq. apply H0.
      - apply @VarAddLeq'' with (ξ1 := ξ1); auto.
        intro n; rewrite <- ext_eq; apply H0.
      - apply VarSwapLeq''. 3 : intro n. all: rewrite <- ext_eq; auto.
      - apply LockCollapseLeq''; intro n; transitivity (ξ n); auto.
      - apply LockSplitLeq''; intro n; transitivity (ξ n); auto.
      - apply LockNothingLeq1''; intro n; transitivity (ξ n); auto.
      - apply LockNothingLeq2''; intro n; transitivity (ξ n); auto.
      - apply @CtxtLeq''Trans with (ξ2 := ξ2) (ξ1 := ξ1) (Δ := Δ); auto.
        intro n; transitivity (ξ3 n); auto.
    Qed.

    Fixpoint ctxt_leq_refl (Γ : Ctxt) : ctxt_leq Γ id_renaming Γ :=
      match Γ with
      | EmptyCtxt => EmptyCtxtLeq'' (fun n => eq_refl)
      | VarExt Γ m τ => @VarExtLeq'' Γ Γ id_renaming id_renaming m τ (fun n => eq_sym (renup_id n)) (ctxt_leq_refl Γ)
      | LockExt Γ m => @LockExtLeq'' Γ Γ id_renaming m (ctxt_leq_refl Γ)
      end.

    Theorem ctxt_leq_numvars: forall Γ Δ ξ,
        ctxt_leq Γ ξ Δ ->
        num_vars Γ <= num_vars Δ.
    Proof using.
      intros Γ Δ ξ lq; induction lq; cbn; try lia.
    Qed.
    
    Hint Constructors Ctxt : ctxts.
    Hint Constructors ctxt_equiv : ctxts.
    Hint Constructors ctxt_leq : ctxts.
    

    Fixpoint CtxtRemove (Γ : Ctxt) (n : nat) : Ctxt :=
      match Γ with
      | EmptyCtxt => EmptyCtxt
      | VarExt Γ m τ =>
          match n with
          | 0 => Γ
          | S n => VarExt (CtxtRemove Γ n) m τ
          end
      | LockExt Γ m => LockExt (CtxtRemove Γ n) m
      end.

    Lemma renup_id_inv : forall ξ1 ξ2 : renaming,
        (forall n, ξ1 n = n) ->
        (forall n, renup ξ2 n = ξ1 n) ->
        forall n, ξ2 n = n.
    Proof using.
      intros ξ1 ξ2 H0 H1 n;
        specialize (H1 (S n)); cbn in H1; rewrite H0 in H1; inversion H1; subst;
        repeat rewrite H3; reflexivity.
    Qed.
    
  End ContextLeq.


  Section LockChanges.

    Fixpoint change_lock_after (Γ : Ctxt) (m : mod) (p q : PName) : option Ctxt :=
      match Γ with
      | EmptyCtxt => None
      | VarExt Γ m' τ =>
          match change_lock_after Γ m p q with
          | Some Δ => Some (VarExt Δ m' τ)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb (cons m p) (all_locks Γ)
          then match change_lock_after Γ m p q with
               | Some Δ => Some (LockExt Δ m')
               | None => None
               end
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => match change_prefix (cons m'' p) m' (cons m'' q) with
                             | None => None
                             | Some m''' => Some (LockExt Γ m''')
                             end
               end
      end.
    
    Fixpoint remove_lock_after (Γ : Ctxt) (m : mod) (p : PName) : option Ctxt :=
      match Γ with
      | EmptyCtxt => None
      | VarExt Γ m' τ =>
          match remove_lock_after Γ m p with
          | Some Δ => Some (VarExt Δ m' τ)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb (cons m p) (all_locks Γ)
          then match remove_lock_after Γ m p with
               | Some Δ => Some (LockExt Δ m')
               | None => None
               end
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => match change_prefix (cons m'' p) m' m'' with 
                             | None => None
                             | Some m''' => Some (LockExt Γ m''')
                             end
               end
      end.

    Fixpoint add_lock_after (Γ : Ctxt) (m : mod) (p : PName) : option Ctxt :=
      match Γ with
      | EmptyCtxt =>
          if eqb m base
          then Some (LockExt EmptyCtxt p)
          else None
      | VarExt Γ m' τ =>
          match add_lock_after Γ m p with
          | Some Δ => Some (VarExt Δ m' τ)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb m (all_locks Γ)
          then match add_lock_after Γ m p with
               | Some Δ => Some (LockExt Δ m')
               | None => None
               end
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => match change_prefix m'' m' (cons m'' p) with
                             | None => None
                             | Some m''' => Some (LockExt Γ m''')
                             end
               end
      end.

    Theorem change_lock_after_defined : forall {Γ : Ctxt} {m : mod} {p q : PName},
        PrefixOf (cons m p) (all_locks Γ) ->
        exists (Δ : Ctxt), change_lock_after Γ m p q = Some Δ.
    Proof using.
      intro Γ; induction Γ; try rename m into m'; intros m p q pfx;
        cbn in *; try (inversion pfx; fail).
      - destruct (IHΓ m p q pfx) as [Δ eq]; rewrite eq.
        eexists; eauto.
      - destruct (prefixb (cons m p) (all_locks Γ)) eqn:eq.
        -- apply prefixb_PrefixOf in eq.
           destruct (IHΓ m p q eq) as [Δ eq']; rewrite eq'; eexists; auto.
        -- apply prefixb_not_PrefixOf in eq.
           pose proof (extended_suffix_prefix pfx eq) as pfx'.
           assert (PrefixOf (all_locks Γ) m) as pfx''
               by (inversion pfx'; subst; auto;
                   match goal with
                   | [ H1 : ~ PrefixOf ?a ?b, H2 : ?b = ?a |- _ ] =>
                       exfalso; apply H1; rewrite H2; reflexivity
                   end).
           destruct (prefix_remove_Some pfx'') as [m'' eqm'']; rewrite eqm''.
           pose proof (readd_remove_prefix eqm'').
           destruct (PrefixOf_peel pfx) as [m''' eqm'''].
           rewrite <- H0 in eqm'''.
           assert (cons (mod_app (all_locks Γ) m'') p = mod_app (all_locks Γ) (cons m'' p)) as H1 by reflexivity; rewrite H1 in eqm'''; clear H1.
           rewrite mod_app_assoc in eqm'''. apply mod_app_inj in eqm'''.
           subst.
           rewrite change_mod_app. eexists; auto.
    Qed.

    Theorem remove_lock_after_defined : forall {Γ : Ctxt} {m : mod} {p : PName},
        PrefixOf (cons m p) (all_locks Γ) ->
        exists (Δ : Ctxt), remove_lock_after Γ m p = Some Δ.
    Proof using.
      intro Γ; induction Γ; intros m_pre p pfx; cbn in *; try (inversion pfx; fail).
      - destruct (IHΓ m_pre p pfx) as [Δ Δeq]; rewrite Δeq.
        eexists; auto.
      - destruct (prefixb (cons m_pre p) (all_locks Γ)) eqn:eq_pre.
        -- destruct (IHΓ m_pre p (prefixb_PrefixOf eq_pre)) as [Δ Δeq]; rewrite Δeq.
           eexists; auto.
        -- assert (~ PrefixOf (cons m_pre p) (all_locks Γ)) as npfx
               by (intro pfx'; apply PrefixOf_prefixb in pfx'; rewrite pfx' in eq_pre; inversion eq_pre).
           pose (pfx' := extended_suffix_prefix pfx npfx).
           assert (PrefixOf (all_locks Γ) m_pre) as pfx''
               by (inversion pfx'; subst; auto;
                   match goal with
                   | [ H1 : ~ PrefixOf ?a ?b, H2 : ?b = ?a |- _ ] =>
                       exfalso; apply H1; rewrite H2; reflexivity
                   end).
           destruct (prefix_remove_Some pfx'') as [m' eqm']; rewrite eqm'.
           assert (m_pre = mod_app (all_locks Γ) m') as eq_pre'
               by (symmetry; apply readd_remove_prefix; assumption).
           destruct (PrefixOf_peel pfx) as [m'' eqm''].
           rewrite eq_pre' in eqm''.
           assert (mod_app (all_locks Γ) m = mod_app (all_locks Γ) (mod_app (cons m' p) m'')) as eq''
               by (transitivity (mod_app (mod_app (all_locks Γ) (cons m' p)) m'');
                   [cbn; exact eqm'' | apply mod_app_assoc]).
           apply mod_app_inj in eq''. rewrite eq''.
           rewrite change_mod_app.
           eexists; auto.
    Qed.

    Theorem add_lock_after_defined : forall {Γ : Ctxt} {m : mod} {p : PName},
        PrefixOf m (all_locks Γ) ->
        exists (Δ : Ctxt), add_lock_after Γ m p = Some Δ.
    Proof using.
      intros Γ; induction Γ as [| Γ IHΓ m' τ | Γ IHΓ m']; intros m p pfx; cbn in *.
      - inversion pfx; subst. eq_bool; subst. eexists; eauto.
      - destruct (IHΓ m p pfx) as [Δ eq]; rewrite eq; eexists; eauto.
      - destruct (prefixb m (all_locks Γ)) eqn:eq_pfx.
        -- destruct (IHΓ m p (prefixb_PrefixOf eq_pfx)) as [Δ eq]; rewrite eq;
             eexists; eauto.
        -- pose proof (prefixb_not_PrefixOf eq_pfx) as npfx.
           pose proof (extended_suffix_prefix pfx npfx) as pfx'.
           destruct (prefix_remove_Some pfx') as [m'' eqm'']; rewrite eqm''.
           destruct (PrefixOf_peel pfx) as [m''' eqm'''].
           pose proof (readd_remove_prefix eqm'') as H0; rewrite <- H0 in eqm'''.
           rewrite mod_app_assoc in eqm'''. apply mod_app_inj in eqm'''.
           subst.
           rewrite change_mod_app. eexists; eauto.
    Qed.

    Theorem change_lock_after_prefix : forall {Γ Δ : Ctxt} {m : mod} {p q : PName},
        change_lock_after Γ m p q = Some Δ ->
        PrefixOf (cons m p) (all_locks Γ).
    Proof using.
      intro Γ; induction Γ as [| Γ IHΓ m' τ | Γ IHΓ m']; intros Δ m p q eq; cbn in *;
        try (inversion eq; fail).
      - destruct (change_lock_after Γ m p q) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
        apply IHΓ in eq; assumption.
      - destruct (prefixb (cons m p) (all_locks Γ)) eqn:eq_pfx.
        -- pose proof (prefixb_PrefixOf eq_pfx) as pfx.
           destruct (change_lock_after Γ m p q) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
           transitivity (all_locks Γ); [assumption | apply PrefixOf_app].
        -- destruct (remove_Prefix (all_locks Γ) m) eqn: eq'; [| inversion eq].
           destruct (change_prefix (cons m0 p) m' (cons m0 q)) eqn:eq''; inversion eq; subst; clear eq.
           destruct (change_prefix_to_app eq'') as [m'' [eqm' eqm1]]; subst.
           pose proof (readd_remove_prefix eq'); subst.
           assert (cons (mod_app (all_locks Γ) m0) p = mod_app (all_locks Γ) (cons m0 p)) as eq
               by reflexivity; rewrite eq; clear eq.
           rewrite <- mod_app_assoc. apply PrefixOf_app.
    Qed.             

    Theorem remove_lock_after_prefix : forall {Γ Δ : Ctxt} {m : mod} {p : PName},
        remove_lock_after Γ m p = Some Δ ->
        PrefixOf (cons m p) (all_locks Γ).
    Proof using.
      intro Γ; induction Γ; try (rename m into m'); intros Δ m p eq; cbn in eq;
        try (inversion eq; fail).
      - destruct (remove_lock_after Γ m p) eqn: eq'; [| inversion eq].
        apply IHΓ in eq'.
        cbn; exact eq'.
      - destruct (prefixb (cons m p) (all_locks Γ)) eqn: eq_pfx.
        -- destruct (remove_lock_after Γ m p) eqn:eq'; [| inversion eq].
           apply IHΓ in eq'; cbn; transitivity (all_locks Γ); [exact eq' | apply PrefixOf_app].
        -- cbn; destruct (remove_Prefix (all_locks Γ) m) eqn:eq_rmv; [| inversion eq].
           destruct (change_prefix (cons m0 p) m' m0) eqn:eq_chng; [| inversion eq].
           apply change_prefix_to_app in eq_chng; destruct eq_chng as [m5 [eq_m' eq_m1]].
           rewrite eq_m'.
           pose proof (readd_remove_prefix eq_rmv).
           rewrite <- H0.
           transitivity (mod_app (all_locks Γ) (cons m0 p)); [reflexivity|].
           apply mod_app_mono_l. apply PrefixOf_app.
    Qed.

    Theorem add_lock_after_prefix : forall {Γ Δ : Ctxt} {m : mod} {p : PName},
        add_lock_after Γ m p = Some Δ ->
        PrefixOf m (all_locks Γ).
    Proof using.
      intro Γ; induction Γ as [| Γ IHΓ m' τ | Γ IHΓ m']; intros Δ m p eq; cbn in eq.
      - eq_bool; subst; inversion eq; subst; clear eq; cbn. reflexivity.
      - destruct (add_lock_after Γ m p) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
        apply IHΓ in eq; cbn; assumption.
      - destruct (prefixb m (all_locks Γ)) eqn:eq_pfx.
        -- destruct (add_lock_after Γ m p) eqn: eq'; inversion eq; subst; clear eq; rename eq' into eq.
           apply IHΓ in eq. cbn; transitivity (all_locks Γ); [assumption | apply PrefixOf_app].
        -- destruct (remove_Prefix (all_locks Γ) m) eqn:eq_rmv; [| inversion eq].
           destruct (change_prefix m0 m' (cons m0 p)) eqn:eq_chng; inversion eq; subst; clear eq.
           pose proof (readd_remove_prefix eq_rmv); subst.
           destruct (change_prefix_to_app eq_chng) as [m2 [eqm' eqm1]]; subst.
           cbn; rewrite <- mod_app_assoc; apply PrefixOf_app.
    Qed.

    (* Theorem remove_lock_after_all_locks : forall {Γ Δ : Ctxt} {m : mod} {p : PName}, *)
    (*     remove_lock_after Γ m p = Some Δ -> *)
    (*     Some (all_locks Δ) = change_prefix (cons m p) (all_locks Γ) m. *)
    (* Proof using. *)
    (*   intro Γ; induction Γ; try (rename m into m'); intros Δ m p eq; cbn in eq; *)
    (*     try (inversion eq; fail). *)
    (*   - destruct (remove_lock_after Γ m p) eqn: eq'; [| inversion eq]. *)
    (*     apply IHΓ in eq'. inversion eq; subst; clear eq; cbn. exact eq'. *)
    (*   - destruct (prefixb (cons m p) (all_locks Γ)) eqn:eq_pfxb. *)
    (*     -- destruct (remove_lock_after Γ m p) eqn: eq'; inversion eq; subst; clear eq; cbn. *)
    (*        apply IHΓ in eq'. *)
    (*        symmetry in eq'. apply change_prefix_to_app in eq'; destruct eq' as [m5 [eq1_m5 eq2_m5]]. *)
    (*        rewrite eq1_m5; rewrite eq2_m5. *)
    (*        symmetry. rewrite mod_app_assoc. rewrite change_mod_app. *)
    (*        rewrite mod_app_assoc; reflexivity. *)
    (*     -- destruct (remove_Prefix (all_locks Γ) m) eqn:eq_rmv_pfx; [| inversion eq]. *)
    (*        destruct (change_prefix (cons m0 p) m' m0) eqn:eq_chng_pfx; inversion eq; subst; clear eq; cbn. *)
    (*        pose proof (readd_remove_prefix eq_rmv_pfx); subst; clear eq_rmv_pfx; cbn. *)
    (*        destruct (change_prefix_to_app eq_chng_pfx) as [m5 [eq_m51 eq_m52]]; subst. *)
    (*        assert (mod_app (all_locks Γ) (mod_app (cons m0 p) m5) = mod_app (cons (mod_app (all_locks Γ) m0) p) m5) *)
    (*          by (rewrite <- mod_app_assoc; cbn; reflexivity); rewrite H0. *)
    (*        rewrite change_mod_app; rewrite mod_app_assoc; reflexivity. *)
    (* Qed. *)

    Theorem all_locks_prefix_equiv : forall {Γ : Ctxt} {m : mod},
        PrefixOf m (all_locks Γ) ->
        exists (Γ1 Γ2 : Ctxt), ctxt_equiv Γ (ctxt_app Γ1 Γ2) /\ all_locks Γ1 = m /\ NonVar Γ1.
    Proof using H PName.
      intro Γ; induction Γ as [| Γ IHΓ m' τ | Γ IHΓ m']; intros m pfx; cbn in *.
      - inversion pfx; subst. exists EmptyCtxt; exists EmptyCtxt; split; [| split]; cbn; try reflexivity; constructor.
      - destruct (IHΓ m pfx) as [Γ1 [Γ2 [eqv [lox nv]]]].
        exists Γ1; exists (VarExt Γ2 m' τ); split; [| split]; cbn; auto.
        apply VarExtEquiv; auto.
      - destruct (PrefixOf_dec m (all_locks Γ)) as [pfx' | npfx].
        -- destruct (IHΓ m pfx') as [Γ1 [Γ2 [eqv [lox nv]]]].
           exists Γ1; exists (LockExt Γ2 m'); split; [| split]; auto; cbn.
           constructor; auto.
        -- pose proof (extended_suffix_prefix pfx npfx) as pfx'.
           destruct (PrefixOf_peel pfx') as [m'' eq]; subst.
           apply mod_app_prefix in pfx.
           destruct (PrefixOf_peel pfx) as [m eq]; subst.
           destruct (eqb m'' base) eqn:eq; eq_bool; subst.
           --- cbn. rewrite mod_base_app.
               destruct (IHΓ (all_locks Γ) (PO_refl (all_locks Γ))) as [Γ1 [Γ2 [eqv [lox nv]]]].
               exists Γ1; exists (LockExt Γ2 m); split; [| split]; cbn; auto.
               constructor; auto.
           --- exists (LockExt Γ m''); exists (LockExt EmptyCtxt m); split; [| split]; cbn; auto.
               all: constructor; auto. reflexivity.
    Qed.
    
    Theorem all_locks_prefix_equiv' : forall {Γ : Ctxt} {m : mod} {p : PName},
        PrefixOf (cons m p) (all_locks Γ) ->
        exists (Γ1 Γ2 : Ctxt), ctxt_equiv Γ (ctxt_app (LockExt Γ1 p) Γ2) /\ all_locks Γ1 = m.
    Proof using H PName.
      intros Γ m p H0.
      destruct (all_locks_prefix_equiv H0) as [Γ1 [Γ2 [eqv [lox nv]]]].
      induction nv. cbn in lox; inversion lox.
      2: { cbn in lox; apply IHnv; auto.
           transitivity (ctxt_app (LockExt Γ0 base) Γ2); auto.
           apply ctxt_app_proper; [constructor|]; reflexivity.
      }
      cbn in lox. destruct m0; cbn in lox; inversion lox; subst; [destruct (H1 eq_refl)|]; clear lox.
      exists (LockExt Γ0 m0); exists Γ2; split; cbn; auto.
      transitivity (ctxt_app (LockExt Γ0 (cons m0 p)) Γ2); auto.
      apply ctxt_app_proper; [| reflexivity].
      transitivity (LockExt Γ0 (mod_app m0 p)); [cbn | apply LockSplitEquiv]; reflexivity.
    Qed.

    Lemma change_lock_after_app : forall {Γ1 Γ2 Δ : Ctxt} {m : mod} {p q : PName},
        change_lock_after Γ1 m p q = Some Δ ->
        change_lock_after (ctxt_app Γ1 Γ2) m p q = Some (ctxt_app Δ Γ2).
    Proof using.
      intros Γ1 Γ2; revert Γ1; induction Γ2 as [| Γ2 IHΓ2 m' τ | Γ2 IHΓ2 m']; intros Γ1 Δ m p q eq; cbn.
      - exact eq.
      - rewrite (IHΓ2 Γ1 Δ m p q eq); reflexivity.
      - pose proof (change_lock_after_prefix eq) as pfx.
        assert (PrefixOf (cons m p) (all_locks (ctxt_app Γ1 Γ2))) as pfx'
            by (rewrite ctxt_app_all_locks; transitivity (all_locks Γ1); [assumption | apply PrefixOf_app]).
        rewrite (PrefixOf_prefixb pfx').
        rewrite (IHΓ2 Γ1 Δ m p q eq). reflexivity.
    Qed.

    Lemma remove_lock_after_app : forall {Γ1 Γ2 Δ : Ctxt} {m : mod} {p : PName},
        remove_lock_after Γ1 m p = Some Δ ->
        remove_lock_after (ctxt_app Γ1 Γ2) m p = Some (ctxt_app Δ Γ2).
    Proof using.
      intros Γ1 Γ2; revert Γ1; induction Γ2; try rename m into m'; intros Γ1 Δ m p eq; cbn.
      - exact eq.
      - rewrite (IHΓ2 Γ1 Δ m p eq). reflexivity.
      - pose proof (remove_lock_after_prefix eq) as pfx1.
        assert (PrefixOf (cons m p) (all_locks (ctxt_app Γ1 Γ2))) as pfx2
            by (rewrite ctxt_app_all_locks; transitivity (all_locks Γ1); [exact pfx1 | apply PrefixOf_app]).
        rewrite (PrefixOf_prefixb pfx2).
        rewrite (IHΓ2 Γ1 Δ m p eq). reflexivity.
    Qed.

    Lemma add_lock_after_app : forall {Γ1 Γ2 Δ : Ctxt} {m : mod} {p : PName},
        add_lock_after Γ1 m p = Some Δ ->
        add_lock_after (ctxt_app Γ1 Γ2) m p = Some (ctxt_app Δ Γ2).
    Proof using.
      intros Γ1 Γ2; revert Γ1; induction Γ2 as [| Γ2 IHΓ2 m' τ | Γ2 IHΓ2 m']; intros Γ1 Δ m p eq; cbn.
      - assumption.
      - rewrite (IHΓ2 Γ1 Δ m p eq); reflexivity.
      - pose proof (add_lock_after_prefix eq) as pfx.
        assert (PrefixOf m (all_locks (ctxt_app Γ1 Γ2))) as pfx'
            by (rewrite ctxt_app_all_locks; transitivity (all_locks Γ1); [assumption | apply PrefixOf_app]).
        rewrite (PrefixOf_prefixb pfx').
        rewrite (IHΓ2 Γ1 Δ m p eq). reflexivity.
    Qed.

    Lemma change_lock_equiv_none : forall {Γ1 Γ2 : Ctxt} {m : mod} {p q : PName},
        ctxt_equiv Γ1 Γ2 ->
        change_lock_after Γ1 m p q = None ->
        change_lock_after Γ2 m p q = None.
    Proof using.
      intros Γ1 Γ2 m p q H0 H1.
      destruct (change_lock_after Γ2 m p q) eqn: eq; [| reflexivity].
      apply change_lock_after_prefix in eq. rewrite <- (all_locks_proper H0) in eq.
      destruct (@change_lock_after_defined _ _ _ q eq) as [Δ eqΔ].
      rewrite H1 in eqΔ; inversion eqΔ.
    Qed.

    Corollary change_lock_equiv_none' : forall {Γ1 Γ2 : Ctxt} {m : mod} {p q : PName},
        ctxt_equiv Γ1 Γ2 ->
        change_lock_after Γ2 m p q = None ->
        change_lock_after Γ1 m p q = None.
    Proof using.
      intros Γ1 Γ2 m p q H0 H1. symmetry in H0. apply @change_lock_equiv_none with (Γ1 := Γ2); auto.
    Qed.

    Lemma remove_lock_equiv_none : forall {Γ1 Γ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        remove_lock_after Γ1 m p = None ->
        remove_lock_after Γ2 m p = None.
    Proof using.
      intros Γ1 Γ2 m p H0 H1.
      destruct (remove_lock_after Γ2 m p) eqn:eq; [| reflexivity].
      apply remove_lock_after_prefix in eq.
      rewrite <- (all_locks_proper H0) in eq.
      apply remove_lock_after_defined in eq; destruct eq as [Δ eq].
      rewrite eq in H1; inversion H1.
    Qed.

    Corollary remove_lock_equiv_none' : forall {Γ1 Γ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        remove_lock_after Γ2 m p = None ->
        remove_lock_after Γ1 m p = None.
    Proof using.
      intros Γ1 Γ2 m p H0 H1.
      apply @remove_lock_equiv_none with (Γ1 := Γ2); [symmetry|]; assumption.
    Qed.

    Lemma add_lock_equiv_none : forall {Γ1 Γ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        add_lock_after Γ1 m p = None ->
        add_lock_after Γ2 m p = None.
    Proof using.
      intros Γ1 Γ2 m p H0 H1.
      destruct (add_lock_after Γ2 m p) eqn:eq; [| reflexivity].
      apply add_lock_after_prefix in eq.
      rewrite <- (all_locks_proper H0) in eq.
      destruct (@add_lock_after_defined _ _ p eq) as [Δ eq'].
      rewrite eq' in H1; inversion H1.
    Qed.

    Corollary add_lock_equiv_none' : forall {Γ1 Γ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        add_lock_after Γ2 m p = None ->
        add_lock_after Γ1 m p = None.
    Proof using.
      intros Γ1 Γ2 m p H0 H1.
      apply @add_lock_equiv_none with (Γ1 := Γ2); [symmetry|]; assumption.
    Qed.

    Theorem change_lock_equiv : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p q : PName},
        ctxt_equiv Γ1 Γ2 ->
        change_lock_after Γ1 m p q = Some Δ1 ->
        change_lock_after Γ2 m p q = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p q eqv1; revert Δ1 Δ2 m p; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some ?a = Some ?b |- _ ] =>
              inversion H; subst; clear H
          | [ |- ctxt_equiv ?a ?a ] => reflexivity
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper Γ Δ H) in H'
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper H) in H'
          | [ H:  context[eqb ?a ?b] |- _ ]=> eq_bool; subst
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[change_lock_after ?Γ ?m ?p ?q] |- _ ] =>
              lazymatch type of H with
              | change_lock_after Γ m p q = _ => fail
              | forall Δ1 Δ2 m p q, change_lock_after _ _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (change_lock_after Γ m p q) eqn: H
              end
          | [ IH : forall Δ1 Δ2 m p q, change_lock_after ?Γ1 m p q = Some Δ1 -> change_lock_after ?Γ2 m p q = Some Δ2 -> ctxt_equiv Δ1 Δ2, H1 : change_lock_after ?Γ1 ?m ?p ?q = Some ?Δ1, H2 : change_lock_after ?Γ2 ?m ?p ?q = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_equiv Δ1 Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p q H1 H2)
              end 
          end; try (econstructor; eauto; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - rewrite mod_app_assoc in H6. apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H5. apply mod_app_inj in H5; subst.
        rewrite <- mod_app_assoc in H7; cbn in H7. apply mod_app_inj in H7; subst.
        assert (cons (mod_app m1 m) q = mod_app m1 (cons m q)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6. apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H5; apply mod_app_inj in H5; subst.
        assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq in H7; clear eq.
        rewrite <- mod_app_assoc in H7. apply mod_app_inj in H7; subst.
        assert (cons (mod_app m1 m0) q = mod_app m1 (cons m0 q)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - destruct (change_lock_after Δ m p q) as [Δ3|] eqn:eq3;
          [| rewrite (change_lock_equiv_none' eqv1_1 eq3) in eq1; inversion eq1].
        transitivity Δ3. apply IHeqv1_1 with (m := m) (p := p); assumption.
        apply IHeqv1_2 with (m := m) (p := p); assumption.
    Qed.
    

    Theorem remove_lock_equiv : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        remove_lock_after Γ1 m p = Some Δ1 ->
        remove_lock_after Γ2 m p = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p eqv1; revert Δ1 Δ2 m p; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some ?a = Some ?b |- _ ] =>
              inversion H; subst; clear H
          | [ |- ctxt_equiv ?a ?a ] => reflexivity
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper Γ Δ H) in H'
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper H) in H'
          | [ H:  context[eqb ?a ?b] |- _ ]=> eq_bool; subst
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[remove_lock_after ?Γ ?m ?p] |- _ ] =>
              lazymatch type of H with
              | remove_lock_after Γ m p = _ => fail
              | forall Δ1 Δ2 m p, remove_lock_after _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (remove_lock_after Γ m p) eqn: H
              end
          | [ IH : forall Δ1 Δ2 m p, remove_lock_after ?Γ1 m p = Some Δ1 -> remove_lock_after ?Γ2 m p = Some Δ2 -> ctxt_equiv Δ1 Δ2, H1 : remove_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : remove_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_equiv Δ1 Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p H1 H2)
              end 
          end; try (econstructor; eauto; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - rewrite mod_app_assoc in H6. apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H5. apply mod_app_inj in H5; subst.
        rewrite <- mod_app_assoc in H7; cbn in H7. apply mod_app_inj in H7; subst.
        rewrite mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6. apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H5; apply mod_app_inj in H5; subst.
        assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq in H7; clear eq.
        rewrite <- mod_app_assoc in H7. apply mod_app_inj in H7; subst.
        rewrite mod_app_assoc. constructor; auto.
      - destruct (remove_lock_after Δ m p) as [Δ3|] eqn:eq3;
          [| rewrite (remove_lock_equiv_none' eqv1_1 eq3) in eq1; inversion eq1].
        transitivity Δ3. apply IHeqv1_1 with (m := m) (p := p); assumption.
        apply IHeqv1_2 with (m := m) (p := p); assumption.
    Qed.

    
    Theorem add_lock_equiv : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        add_lock_after Γ1 m p = Some Δ1 ->
        add_lock_after Γ2 m p = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p eqv1; revert Δ1 Δ2 m p; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some ?a = Some ?b |- _ ] =>
              inversion H; subst; clear H
          | [ |- ctxt_equiv ?a ?a ] => reflexivity
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper Γ Δ H) in H'
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_equiv ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (all_locks_proper H) in H'
          | [ H:  context[eqb ?a ?b] |- _ ]=> eq_bool; subst
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[add_lock_after ?Γ ?m ?p] |- _ ] =>
              lazymatch type of H with
              | add_lock_after Γ m p = _ => fail
              | forall Δ1 Δ2 m p, add_lock_after _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (add_lock_after Γ m p) eqn: H
              end
          | [ IH : forall Δ1 Δ2 m p, add_lock_after ?Γ1 m p = Some Δ1 -> add_lock_after ?Γ2 m p = Some Δ2 -> ctxt_equiv Δ1 Δ2, H1 : add_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : add_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_equiv Δ1 Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p H1 H2)
              end 
          end; try (econstructor; eauto; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - destruct m0; cbn in H2; try lia.
        destruct m1; cbn in H2; try lia.
        cbn in *. exfalso; apply H4; reflexivity.
      - rewrite mod_app_assoc in H6. apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H5. apply mod_app_inj in H5; subst.
        rewrite <- mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        assert (cons (mod_app m1 m) p = mod_app m1 (cons m p)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - exfalso; apply H1. transitivity (all_locks Γ); auto. apply PrefixOf_app.
      - rewrite mod_app_assoc in H5; apply mod_app_inj in H5; subst.
        rewrite <- mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - pose proof (readd_remove_prefix H2). cbn in H4. rewrite H4 in H1. exfalso; apply H1; reflexivity.
      - pose proof (readd_remove_prefix H2). cbn in H4. rewrite H4 in H1. exfalso; apply H1; reflexivity.
      - destruct (add_lock_after Δ m p) as [Δ3|] eqn:eq3;
          [| rewrite (add_lock_equiv_none' eqv1_1 eq3) in eq1; inversion eq1].
        transitivity Δ3. apply IHeqv1_1 with (m := m) (p := p); assumption.
        apply IHeqv1_2 with (m := m) (p := p); assumption.                                                  Qed.                                             

    Corollary remove_lock_after_equiv : forall {Γ Δ : Ctxt} {m : mod} {p : PName},
        remove_lock_after Γ m p = Some Δ ->
        exists (Γ1 Γ2 : Ctxt), ctxt_equiv Γ (ctxt_app (LockExt Γ1 p) Γ2) /\ ctxt_equiv Δ (ctxt_app Γ1 Γ2).
    Proof using.
      intros Γ Δ m p eq.
      pose proof (remove_lock_after_prefix eq) as pfx.
      destruct (all_locks_prefix_equiv' pfx) as [Γ1 [Γ2 [eqv eq']]].
      assert (remove_lock_after (LockExt Γ1 p) m p = Some (LockExt Γ1 base)).
      cbn; destruct (prefixb (cons m p) (all_locks Γ1)) eqn:eq_pfxb;
        [apply prefixb_PrefixOf in eq_pfxb; rewrite eq' in eq_pfxb;
         apply PrefixOf_size in eq_pfxb; cbn in eq_pfxb; lia|].
      rewrite eq'. rewrite remove_all_mod. eq_bool. reflexivity.
      apply @remove_lock_after_app with (Γ2 := Γ2) in H0.
      pose proof (remove_lock_equiv eqv eq H0).
      exists Γ1; exists Γ2; split; auto. transitivity (ctxt_app (LockExt Γ1 base) Γ2); auto.
      apply ctxt_app_proper; [apply LockNothingEquiv2|]; reflexivity.
    Qed.


    Theorem ctxt_leq_all_locks : forall {Γ Δ : Ctxt} {ξ : renaming},
        ctxt_leq Γ ξ Δ -> all_locks Γ = all_locks Δ.
    Proof using.
      intros Γ Δ ξ lq; induction lq; cbn; auto.
      - rewrite IHlq; reflexivity.
      - apply mod_app_assoc.
      - symmetry; apply mod_app_assoc.
      - transitivity (all_locks Δ); assumption.
    Qed.

    Theorem ctxt_leq_locks : forall {Γ Δ : Ctxt} {ξ : renaming},
        ctxt_leq Γ ξ Δ ->
        forall n, locks Γ n = locks Δ (ξ n).
    Proof using.
      intros Γ Δ ξ lq; induction lq; intro n; cbn; auto.
      - destruct n; rewrite H0; cbn; auto.
      - rewrite <- IHlq. destruct (locks Γ n); auto.
      - rewrite H0; auto.
      - destruct n. rewrite H0; reflexivity. destruct n. rewrite H1; reflexivity.
        rewrite H2; reflexivity.
      - rewrite H0. destruct (locks Γ n); [rewrite mod_app_assoc|]; reflexivity.
      - rewrite H0. destruct (locks Γ n); [rewrite mod_app_assoc|]; reflexivity.
      - rewrite H0. destruct (locks Γ n); reflexivity.
      - rewrite H0. destruct (locks Γ n); reflexivity.
      - rewrite IHlq1. rewrite IHlq2. rewrite H0. reflexivity.
    Qed.


    Theorem ctxt_leq_change_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p q : PName},
        ctxt_leq Γ1 ξ Γ2 ->
        change_lock_after Γ1 m p q = Some Δ1 ->
        change_lock_after Γ2 m p q = Some Δ2 ->
        ctxt_leq Δ1 ξ Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 ξ m p q lq; revert Δ1 Δ2 m p q; induction lq; try rename m into m'; intros Δ1 Δ2 m p q eq1 eq2;
        cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_leq ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (ctxt_leq_all_locks H) in H'
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[change_lock_after ?Γ ?m ?p ?q] |- _ ] =>
              lazymatch type of H with
              | change_lock_after Γ m p q = _ => fail
              | forall Δ1 Δ2 m p q, change_lock_after _ _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (change_lock_after Γ m p q) eqn: H
              end
          | [ H : context[eqb _ _ ] |- _ ] => eq_bool; subst 
          | [ IH : forall Δ1 Δ2 m p q, change_lock_after ?Γ1 m p q = Some Δ1 -> change_lock_after ?Γ2 m p q = Some Δ2 -> ctxt_leq Δ1 ?ξ Δ2, H1 : change_lock_after ?Γ1 ?m ?p ?q = Some ?Δ1, H2 : change_lock_after ?Γ2 ?m ?p ?q = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_leq Δ1 ξ Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p q H1 H2)
              end 
          end; try (econstructor; eauto with ctxts; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc in H8; cbn in H8; apply mod_app_inj in H8; subst.
        assert (cons (mod_app m1 m) q = mod_app m1 (cons m q)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc in H8; cbn in H8; apply mod_app_inj in H8; subst.
        assert (cons (mod_app m1 m0) q = mod_app m1 (cons m0 q)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - pose proof (change_lock_after_prefix eq1) as lox;
          rewrite (ctxt_leq_all_locks lq1) in lox;
          destruct (@change_lock_after_defined _ _ _ q lox) as [Δ3 eq3]; clear lox.
        pose proof (IHlq1 _ _ _ _ _ eq1 eq3).
        pose proof (IHlq2 _ _ _ _ _ eq3 eq2).
        eapply CtxtLeq''Trans; eauto.
    Qed.
    
    Theorem ctxt_leq_remove_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p : PName},
        ctxt_leq Γ1 ξ Γ2 ->
        remove_lock_after Γ1 m p = Some Δ1 ->
        remove_lock_after Γ2 m p = Some Δ2 ->
        ctxt_leq Δ1 ξ Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 ξ m p lq; revert Δ1 Δ2 m p; induction lq; try rename m into m'; intros Δ1 Δ2 m p eq1 eq2;
        cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_leq ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (ctxt_leq_all_locks H) in H'
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[remove_lock_after ?Γ ?m ?p] |- _ ] =>
              lazymatch type of H with
              | remove_lock_after Γ m p = _ => fail
              | forall Δ1 Δ2 m p, remove_lock_after _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (remove_lock_after Γ m p) eqn: H
              end
          | [ H : context[eqb _ _ ] |- _ ] => eq_bool; subst 
          | [ IH : forall Δ1 Δ2 m p, remove_lock_after ?Γ1 m p = Some Δ1 -> remove_lock_after ?Γ2 m p = Some Δ2 -> ctxt_leq Δ1 ?ξ Δ2, H1 : remove_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : remove_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_leq Δ1 ξ Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p H1 H2)
              end 
          end; try (econstructor; eauto with ctxts; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. apply LockCollapseLeq''; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        assert (cons (mod_app m1 m) p = mod_app m1 (cons m p)) by reflexivity.
        rewrite H6 in H8. rewrite mod_app_assoc in H8. do 2 apply mod_app_inj in H8.
        subst.
        rewrite mod_app_assoc. apply LockCollapseLeq''; auto.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. apply LockSplitLeq''; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc in H8; cbn in H8; apply mod_app_inj in H8; subst.
        rewrite mod_app_assoc; apply LockSplitLeq''; auto.
      - pose proof (remove_lock_after_prefix eq1).
        rewrite (ctxt_leq_all_locks lq1) in H1.
        apply remove_lock_after_defined in H1.
        destruct H1 as [Δ3 eq3].
        specialize (IHlq1 _ _ _ _ eq1 eq3).
        specialize (IHlq2 _ _ _ _ eq3 eq2).
        apply @CtxtLeq''Trans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
    Qed.

    Theorem ctxt_leq_add_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p : PName},
        ctxt_leq Γ1 ξ Γ2 ->
        add_lock_after Γ1 m p = Some Δ1 ->
        add_lock_after Γ2 m p = Some Δ2 ->
        ctxt_leq Δ1 ξ Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 ξ m p lq; revert Δ1 Δ2 m p; induction lq; try rename m into m'; intros Δ1 Δ2 m p eq1 eq2;
        cbn in *;
        repeat match goal with
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
          | [ H : ctxt_leq ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
              rewrite <- (ctxt_leq_all_locks H) in H'
          | [ H : prefixb ?m1 ?m2 = true |- _ ] =>
              lazymatch goal with
              | [ _ : PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = false |- _ ] => rewrite H' in H; inversion H
              | _ => pose proof (prefixb_PrefixOf H)
              end
          | [ H : prefixb ?m1 ?m2 = false |- _ ] =>
              lazymatch goal with
              | [ _ : ~ PrefixOf m1 m2 |- _ ] => fail
              | [ H' : prefixb m1 m2 = true |- _ ] => rewrite H in H'; inversion H'
              | _ => pose proof (prefixb_not_PrefixOf H)
              end
          | [ H: remove_Prefix ?m1 ?m2 = Some ?m3 |- _ ] =>
              tryif unify m2 (mod_app m1 m3)
              then clear H
              else lazymatch goal with
                   | [ _ : m2 = mod_app m1 m3 |- _ ] => fail
                   | [ _ : mod_app m1 m3 = m2 |-  _ ] => fail
                   | _ => pose proof (readd_remove_prefix H); subst
                   end
          | [H : change_prefix ?m1 (mod_app ?m1 ?m2) ?m3 = Some ?m4 |- _ ] =>
              tryif unify m4 (mod_app m1 m3)
              then fail
              else rewrite change_mod_app in H
          | [H : change_prefix ?m1 ?m2 ?m3 = Some ?m4 |- _ ] =>
              let m := fresh "m" in
              let H1 := fresh in
              let H2 := fresh in 
              destruct (change_prefix_to_app H) as [m [H1 H2]]; subst; clear H
          | [ H : PrefixOf ?m1 ?m2 |- _ ] =>
              lazymatch goal with
              | [ H: mod_size ?m1 <= mod_size ?m2 |- _ ] => fail
              | _ => pose proof (PrefixOf_size H)
              end
          | [ H : context[prefixb ?a ?b] |- _ ] =>
              lazymatch type of H with
              | prefixb a b = _ => fail
              | _ => let H := fresh in destruct (prefixb a b) eqn: H
              end
          | [ H : context[remove_Prefix ?m1 ?m2] |- _ ] =>
              lazymatch type of H with
              | remove_Prefix m1 m2 = _ => fail
              | _ => let H := fresh in destruct (remove_Prefix m1 m2) eqn: H
              end
          | [ H : context[change_prefix ?m1 ?m2 ?m3] |- _ ] =>
              lazymatch type of H with
              | change_prefix m1 m2 m3 = _ => fail
              | _ => let H := fresh in destruct (change_prefix m1 m2 m3) eqn: H
              end 
          | [ H : context[add_lock_after ?Γ ?m ?p] |- _ ] =>
              lazymatch type of H with
              | add_lock_after Γ m p = _ => fail
              | forall Δ1 Δ2 m p, add_lock_after _ _ _ = _ -> _ => fail
              | _ => let H := fresh in destruct (add_lock_after Γ m p) eqn: H
              end
          | [ H : context[eqb _ _ ] |- _ ] => eq_bool; subst 
          | [ IH : forall Δ1 Δ2 m p, add_lock_after ?Γ1 m p = Some Δ1 -> add_lock_after ?Γ2 m p = Some Δ2 -> ctxt_leq Δ1 ?ξ Δ2, H1 : add_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : add_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
              lazymatch goal with
              | [ H : ctxt_leq Δ1 ξ Δ2 |- _ ] => fail
              | _ => pose proof (IH Δ1 Δ2 m p H1 H2)
              end 
          end; try (econstructor; eauto with ctxts; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end; try lia.
      - do 2 constructor; assumption.
      - destruct m1; cbn in H3; try lia. destruct m0; cbn in H3; try lia.
        cbn in *.  exfalso; apply H5; reflexivity.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc in H8; apply mod_app_inj in H8; subst.
        assert (cons (mod_app m1 m) p = mod_app m1 (cons m p)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc. constructor; auto.
      - rewrite mod_app_assoc in H7; apply mod_app_inj in H7; subst.
        rewrite <- mod_app_assoc. constructor; auto.
      - destruct m1; destruct m0; cbn in H5; try lia; cbn in *.
        exfalso; apply H2; reflexivity.
      - rewrite mod_app_assoc in H6; apply mod_app_inj in H6; subst.
        rewrite <- mod_app_assoc in H8; apply mod_app_inj in H8; subst.
        assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq; clear eq.
        rewrite mod_app_assoc; constructor; auto.
      - exfalso; apply H2; reflexivity.
      - exfalso; apply H2; reflexivity.
      - pose proof (add_lock_after_prefix eq1).
        rewrite (ctxt_leq_all_locks lq1) in H1.
        apply @add_lock_after_defined  with (p := p) in H1.
        destruct H1 as [Δ3 eq3].
        specialize (IHlq1 _ _ _ _ eq1 eq3).
        specialize (IHlq2 _ _ _ _ eq3 eq2).
        apply @CtxtLeq''Trans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
    Qed.

  End LockChanges.

End Contexts.
