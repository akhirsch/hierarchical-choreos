Require Import EqBool.
Require Import Modalities.
Require Import Syntax.
(* Require Import Contexts. *)
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require List.
Import List.ListNotations.
From Stdlib Require Import Sorting.Permutation.

Section CorpsTypes.
  Context {PName : Type} `{EqBool PName}.

  #[local] Abbreviation type := (type PName).
  #[local] Abbreviation expr := (expr PName).
  #[local] Abbreviation mod := (mod PName).
  #[local] Abbreviation base := (@base PName).
  #[local] Definition ptm := @proc_to_mod PName.
  Coercion ptm : PName >-> mod.
  Context {CanSend CanUp CanDown : mod -> mod -> Prop}.

  Create HintDb ctxts.
  Section Contexts.
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
    End Emptoid.

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


    Section ContextLeq.

      Inductive ctxt_leq'' : Ctxt -> renaming -> Ctxt -> Prop :=
      | EmptyCtxtLeq'' {ξ : renaming} :
          (forall n, ξ n = n) -> 
          ctxt_leq'' EmptyCtxt ξ EmptyCtxt
      | VarExtLeq'' : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
          (forall n, ξ2 n = renup ξ1 n) -> 
          ctxt_leq'' Γ ξ1 Δ ->
          ctxt_leq'' (VarExt Γ m τ) ξ2 (VarExt Δ m τ)
      | LockExtLeq'' : forall {Γ Δ : Ctxt} {ξ : renaming} (m : mod),
          ctxt_leq'' Γ ξ Δ ->
          ctxt_leq'' (LockExt Γ m) ξ (LockExt Δ m)
      | VarAddLeq'' : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
          ctxt_leq'' Γ ξ1 Δ ->
          (forall n, ξ2 n = S (ξ1 n)) ->
          ctxt_leq'' Γ ξ2 (VarExt Δ m τ)
      | VarSwapLeq'' : forall (Γ : Ctxt) (m1 m2 : mod) (τ1 τ2 : type) (ξ : renaming),
          (ξ 0 = 1) ->
          (ξ 1 = 0) ->
          (forall n, ξ (S (S n)) = S (S n)) ->
          ctxt_leq'' (VarExt (VarExt Γ m1 τ1) m2 τ2) ξ (VarExt (VarExt Γ m2 τ2) m1 τ1)
      | LockCollapseLeq'' : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
          (forall n, ξ n = n) ->
          ctxt_leq'' (LockExt (LockExt Γ m1) m2) ξ (LockExt Γ (mod_app m1 m2))
      | LockSplitLeq'' : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
          (forall n, ξ n = n) ->
          ctxt_leq'' (LockExt Γ (mod_app m1 m2)) ξ (LockExt (LockExt Γ m1) m2)
      | LockNothingLeq1'' : forall (Γ : Ctxt) (ξ : renaming),
          (forall n, ξ n = n) ->
          ctxt_leq'' Γ ξ (LockExt Γ base)
      | LockNothingLeq2'' : forall (Γ : Ctxt) (ξ : renaming),
          (forall n, ξ n = n) ->
          ctxt_leq'' (LockExt Γ base) ξ Γ
      | CtxtLeq''Trans : forall {Γ Δ E : Ctxt} {ξ1 ξ2 : renaming} (ξ3 : renaming),
          (forall n, ξ3 n = ξ2 (ξ1 n)) -> 
          ctxt_leq'' Γ ξ1 Δ ->
          ctxt_leq'' Δ ξ2 E ->
          ctxt_leq'' Γ ξ3 E.

      
      Inductive ctxt_leq' : Ctxt -> Ctxt -> Type :=
        EmptyCtxtLeq' : ctxt_leq' EmptyCtxt EmptyCtxt
      | VarExtLeq' : forall {Γ Δ : Ctxt} (m : mod) (τ : type),
          ctxt_leq' Γ Δ ->
          ctxt_leq' (VarExt Γ m τ) (VarExt Δ m τ)
      | LockExtLeq' : forall {Γ Δ : Ctxt} (m : mod),
          ctxt_leq' Γ Δ ->
          ctxt_leq' (LockExt Γ m) (LockExt Δ m)
      | VarAddLeq' : forall {Γ Δ : Ctxt} (m : mod) (τ : type),
          ctxt_leq' Γ Δ ->
          ctxt_leq' Γ (VarExt Δ m τ)
      | VarSwapLeq' : forall (Γ : Ctxt) (m1 m2 : mod) (τ1 τ2 : type),
          ctxt_leq' (VarExt (VarExt Γ m1 τ1) m2 τ2) (VarExt (VarExt Γ m2 τ2) m1 τ1)
      | LockCollapseLeq' : forall (Γ : Ctxt) (m1 m2 : mod),
          ctxt_leq' (LockExt (LockExt Γ m1) m2) (LockExt Γ (mod_app m1 m2))
      | LockSplitLeq' : forall (Γ : Ctxt) (m1 m2 : mod),
          ctxt_leq' (LockExt Γ (mod_app m1 m2)) (LockExt (LockExt Γ m1) m2)
      | LockNothingLeq1' : forall (Γ : Ctxt),
          ctxt_leq' Γ (LockExt Γ base)
      | LockNothingLeq2' : forall (Γ : Ctxt),
          ctxt_leq' (LockExt Γ base) Γ
      | CtxtLeq'Trans : forall {Γ Δ E : Ctxt},
          ctxt_leq' Γ Δ ->
          ctxt_leq' Δ E ->
          ctxt_leq' Γ E.
      
      Fixpoint renaming_of_ctxt_leq' {Γ Δ : Ctxt} (lq : ctxt_leq' Γ Δ) : renaming :=
        match lq with
        | EmptyCtxtLeq' => id_renaming
        | VarExtLeq' m τ lq => renup (renaming_of_ctxt_leq' lq)
        | LockExtLeq' m lq => renaming_of_ctxt_leq' lq
        | VarAddLeq' m τ lq => fun n => S (renaming_of_ctxt_leq' lq n)
        | VarSwapLeq' Γ m1 m2 τ1 τ2 => fun n =>
                                  match n with
                                  | 0 => 1
                                  | 1 => 0
                                  | S (S m) => n
                                  end
        | LockCollapseLeq' Γ m1 m2 => id_renaming
        | LockSplitLeq' Γ m1 m2 => id_renaming
        | LockNothingLeq1' Γ => id_renaming
        | LockNothingLeq2' Γ => id_renaming
        | CtxtLeq'Trans lq1 lq2 => fun n => renaming_of_ctxt_leq' lq2 (renaming_of_ctxt_leq' lq1 n)
        end.

      Theorem ctxt_leq'_to_ctxt_leq'' : forall {Γ Δ : Ctxt} (lq : ctxt_leq' Γ Δ), ctxt_leq'' Γ (renaming_of_ctxt_leq' lq) Δ.
      Proof using.
        intros Γ Δ lq; induction lq; cbn; try (econstructor; eauto; fail).
      Qed.

      Theorem ctxt_leq''_ext : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming},
          (forall n, ξ1 n = ξ2 n) -> 
          ctxt_leq'' Γ ξ1 Δ ->
          ctxt_leq'' Γ ξ2 Δ.
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

      Fixpoint ctxt_leq''_refl (Γ : Ctxt) : ctxt_leq'' Γ id_renaming Γ :=
        match Γ with
        | EmptyCtxt => EmptyCtxtLeq'' (fun n => eq_refl)
        | VarExt Γ m τ => @VarExtLeq'' Γ Γ id_renaming id_renaming m τ (fun n => eq_sym (renup_id n)) (ctxt_leq''_refl Γ)
        | LockExt Γ m => @LockExtLeq'' Γ Γ id_renaming m (ctxt_leq''_refl Γ)
        end.

      Theorem ctxt_leq''_numvars: forall Γ Δ ξ,
          ctxt_leq'' Γ ξ Δ ->
          num_vars Γ <= num_vars Δ.
      Proof using.
        intros Γ Δ ξ lq; induction lq; cbn; try lia.
      Qed.

      Inductive ctxt_leq : Ctxt -> Ctxt -> Prop :=
      | EmptyCtxtLeq : ctxt_leq EmptyCtxt EmptyCtxt
      | VarExtLeq : forall {Γ Δ : Ctxt} (m : mod) (τ : type),
          ctxt_leq Γ Δ ->
          ctxt_leq (VarExt Γ m τ) (VarExt Δ m τ)
      | LockExtLeq : forall {Γ Δ : Ctxt} (m : mod),
          ctxt_leq Γ Δ -> ctxt_leq (LockExt Γ m) (LockExt Δ m)
      | VarAddLeq : forall {Γ Δ : Ctxt} (m : mod) (τ : type),
          ctxt_leq Γ Δ ->
          ctxt_leq Γ (VarExt Δ m τ)
      | VarSwapLeqL : forall {Γ Δ : Ctxt} (m1 m2 : mod) (τ1 τ2 : type),
          ctxt_leq (VarExt (VarExt Γ m1 τ1) m2 τ2) Δ ->
          ctxt_leq (VarExt (VarExt Γ m2 τ2) m1 τ1) Δ
      | VarSwapLeqR : forall {Γ Δ : Ctxt} (m1 m2 : mod) (τ1 τ2 : type),
          ctxt_leq Γ (VarExt (VarExt Δ m1 τ1) m2 τ2) ->
          ctxt_leq Γ (VarExt (VarExt Δ m2 τ2) m1 τ1)
      | LockSplitL : forall {Γ Δ : Ctxt} (m1 m2 : mod),
          ctxt_leq (LockExt Γ (mod_app m1 m2)) Δ ->
          ctxt_leq (LockExt (LockExt Γ m1) m2) Δ 
      | LockSplitR : forall {Γ Δ : Ctxt} (m1 m2 : mod),
          ctxt_leq Γ (LockExt Δ (mod_app m1 m2)) ->
          ctxt_leq Γ (LockExt (LockExt Δ m1) m2)
      | LockNothingLeq1 : forall {Γ Δ : Ctxt},
          ctxt_leq Γ Δ -> ctxt_leq Γ (LockExt Δ base)
      | LockNothingLeq2 : forall {Γ Δ : Ctxt},
          ctxt_leq Γ Δ -> ctxt_leq (LockExt Γ base) Δ.


      Fixpoint ctxt_leq_refl (Γ : Ctxt) : ctxt_leq Γ Γ :=
        match Γ with
        | EmptyCtxt => EmptyCtxtLeq
        | VarExt Γ m τ => VarExtLeq m τ (ctxt_leq_refl Γ)
        | LockExt Γ m => LockExtLeq m (ctxt_leq_refl Γ)
        end.

      Lemma ctxt_leq_numvars : forall Γ Δ,
          ctxt_leq Γ Δ ->
          num_vars Γ <= num_vars Δ.
      Proof using.
        intros Γ Δ lq; induction lq; cbn in *; try lia.
      Qed.

      Corollary ctxt_leq_emptoid : forall Γ Δ,
          Emptoid Δ ->
          ctxt_leq Γ Δ ->
          Emptoid Γ.
      Proof using.
        intros Γ Δ etd lq; revert etd; induction lq; intro etd;
          try (inversion etd; subst);
          repeat match goal with
            | [ |- Emptoid EmptyCtxt ] => constructor
            | [ H : Emptoid (VarExt _ _ _) |- _ ] => inversion H
            | [ H : Emptoid (LockExt ?Γ ?m) |- _ ] =>
                lazymatch goal with
                | [ _ : Emptoid Γ |- _ ] => fail 
                | _ => inversion H; subst
                end
            | [ H : ?P |- ?P ] => exact H
            | [ |- Emptoid (LockExt ?Γ base) ] => constructor
            | [ H : base = mod_app ?a ?b |- _ ] =>
                destruct (mod_app_base_inv a b (eq_sym H)); subst; clear H; cbn in *
            | [ IH : Emptoid ?a -> Emptoid ?b, H : Emptoid ?a |- _ ] => specialize (IH H)
            end.
      Qed.

      Lemma ctxt_leq_all_emptoids : forall Γ Δ,
          Emptoid Γ ->
          Emptoid Δ ->
          ctxt_leq Γ Δ.
      Proof using.
        intros Γ Δ etdΓ; revert Δ; induction etdΓ; intros Δ etdΔ.
        - induction etdΔ. constructor. constructor. apply IHetdΔ.
        - constructor. apply IHetdΓ. exact etdΔ.
      Qed.

      (* Theorem ctxt_leq_trans : forall Γ Δ E, *)
      (*     ctxt_leq Γ Δ -> *)
      (*     ctxt_leq Δ E -> *)
      (*     ctxt_leq Γ E. *)
      (* Proof using. *)
      (*   intros Γ Δ E lq1; revert E; induction lq1; intros E lq2; *)
      (*   repeat match goal with *)
      (*          | [ H : ?P |- ?P ] => exact H *)
      (*     end. *)
      (*   - dependent destruction lq2. *)
      (*     -- apply VarExtLeq. apply IHlq1. exact lq2. *)
      (*     -- apply VarAddLeq. *)
          

      (* Theorem ctxt_normalize_leq1 : forall Γ Δ, *)
      (*     ctxt_leq (ctxt_normalize Γ) Δ -> *)
      (*     ctxt_leq Γ Δ. *)
      (* Proof using. *)
      (*   intros Γ Δ lq; dependent induction lq; cbn in *. *)
      (*   2: { *)

      (* Theorem ctxt_normalize_leq : forall Γ Δ, *)
      (*     ctxt_leq (ctxt_normalize Γ) (ctxt_normalize Δ) -> *)
      (*     ctxt_leq Γ Δ. *)
      (* Proof using. *)
      (*   intros Γ Δ lq; dependent induction lq. *)
      (*   - apply ctxt_leq_all_emptoids; apply equiv_empty_emptoid1. *)
      (*     etransitivity; [| symmetry; apply ctxt_normalize_equiv]; rewrite <- x0; *)
      (*       constructor. *)
      (*     etransitivity; [| symmetry; apply ctxt_normalize_equiv]; rewrite <- x; *)
      (*       constructor. *)
      (*   - destruct Γ; cbn in x0; inversion x0; subst. *)
      (*     2: {  *)
                           

      Definition varlist : Type := list (mod * type).

      Fixpoint count_occurences (m : mod) (τ : type) (vl : varlist) : nat :=
        match vl with
        | nil => 0
        | List.cons (m', τ') vl' => if eqb m m' && eqb τ τ' then 1 + count_occurences m τ vl' else count_occurences m τ vl'
        end.

      Fixpoint remove_one_var (m : mod) (τ : type) (vl : varlist) : varlist :=
        match vl with
        | nil => nil
        | List.cons (m', τ') vl' =>
            if eqb m m' && eqb τ τ' then vl' else remove_one_var m τ vl'
        end.

      Lemma remove_one_var_count : forall vl m τ,
          count_occurences m τ (remove_one_var m τ vl) = (count_occurences m τ vl) - 1.
      Proof using.
        intros vl; induction vl as [| pr vl IHvl]; intros m τ; cbn.
        reflexivity.
        destruct pr as [m' τ']; eq_bool.
        cbn. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
        all: apply IHvl.
      Qed.

      Fixpoint VarExts (Γ : Ctxt) (vl : varlist) : Ctxt :=
        match vl with
        | nil => Γ
        | List.cons (m, τ) vl' => VarExt (VarExts Γ vl') m τ
        end.

      Fixpoint SplitVars (Γ : Ctxt) : Ctxt * varlist :=
        match Γ with
        | EmptyCtxt => (EmptyCtxt, nil)
        | VarExt Γ m τ =>
            match SplitVars Γ with
            | (Δ, vl) => (Δ, List.cons (m, τ) vl)
            end
        | LockExt Γ m =>
            if eqb m base then SplitVars Γ else (LockExt Γ m, nil)
        end.

      Lemma SplitVars_Exts : forall Γ,
          ctxt_equiv Γ (VarExts (fst (SplitVars Γ)) (snd (SplitVars Γ))).
      Proof using.
        intro Γ; induction Γ; cbn.
        - reflexivity.
        - destruct (SplitVars Γ); cbn; cbn in IHΓ.
          apply VarExtEquiv; exact IHΓ.
        - eq_bool; subst.
          -- apply LockNothingEquiv2; exact IHΓ.
          -- cbn. reflexivity.
      Qed.

      Lemma SplitVars_NonVar : forall Γ,
          NonVar (fst (SplitVars Γ)).
      Proof using.
        intro Γ; induction Γ; cbn.
        - constructor.
        - destruct (SplitVars Γ); cbn in *; assumption.
        - eq_bool; [assumption | cbn; constructor; auto].
      Qed.

      (* Ltac ctxt_leq_constructor := *)
      (*   match goal with *)
      (*   | [ H : ctxt_leq ?Γ ?Δ |- ctxt_leq ?Γ ?Δ ] => exact H *)
      (*   | [ |- ctxt_leq ?Γ ?Γ ] => apply ctxt_leq_refl *)
      (*   | [ |- ctxt_leq (VarExt ?Γ ?m ?τ) (VarExt ?Δ ?m ?τ) ] => *)
      (*       apply (VarExtLeq m τ); ctxt_leq_constructor *)
      (*   | [ |- ctxt_leq (LockExt ?Γ ?m) (LockExt ?Δ ?m) ] => *)
      (*       apply (LockExtLeq m); ctxt_leq_constructor *)
      (*   | [ |- ctxt_leq ?Γ (LockExt ?Δ base) ] => *)
      (*       apply LockNothingLeq1; ctxt_leq_constructor *)
      (*   | [ |- ctxt_leq (LockExt ?Γ (mod_app ?m1 ?m2)) ?Δ ] => *)
      (*       apply LockCollapseL; ctxt_leq_constructor *)
      (*   | [ |- ctxt_leq ?Γ (LockExt ?Δ (mod_app ?m1 ?m2)) ] => *)
      (*       apply LockCollapseR; ctxt_leq_constructor *)
      (*   end. *)

      (* Lemma SplitVars_leq1 : forall Γ Δ, *)
      (*     ctxt_leq Γ Δ -> *)
      (*     ctxt_leq (fst (SplitVars Γ)) (fst (SplitVars Δ)). *)
      (* Proof using. *)
      (*   intros Γ Δ lq; induction lq; cbn in *; eq_bool; subst; cbn in *; *)
      (*   repeat match goal with *)
      (*     | [ |- ctxt_leq ?a ?a ] => apply ctxt_leq_refl *)
      (*     | [ H : ?P |- ?P ] => exact H *)
      (*     | [ H : ?a <> ?a |- _ ] => exfalso; apply H; reflexivity *)
      (*     | [ H : ?a <> ?b, H' : ?a = ?b |- _ ] => exfalso; apply H; exact H' *)
      (*     | [ H : mod_app ?a ?b = base |- _ ] => *)
      (*         lazymatch goal with *)
      (*         | [_ : a = base, _ : b = base |- _ ] => fail *)
      (*         | _ => destruct (mod_app_base_inv a b H); subst *)
      (*         end *)
      (*     | [ H : base = mod_app ?a ?b |- _ ] => *)
      (*         lazymatch goal with *)
      (*         | [_ : a = base, _ : b = base |- _ ] => fail *)
      (*         | _ => destruct (mod_app_base_inv a b (eq_sym H)); subst *)
      (*         end *)
      (*     | [ H : context[SplitVars ?Γ] |- _ ] => *)
      (*         lazymatch type of H with *)
      (*         | SplitVars Γ = _ => fail *)
      (*         | _ => let H := fresh in *)
      (*               destruct (SplitVars Γ) eqn:H; cbn in * *)
      (*         end  *)
      (*     | [ |- context[SplitVars ?Γ] ] => *)
      (*         let H := fresh in *)
      (*         destruct (SplitVars Γ) eqn:H; cbn in * *)
      (*     end; try ctxt_leq_constructor. *)
      (* Qed. *)

      (* Lemma SplitVars_leq2 : forall Γ Δ, *)
      (*     ctxt_leq Γ Δ -> *)
      (*     forall m τ, *)
      (*       count_occurences m τ (snd (SplitVars Γ)) *)
      (*       <= count_occurences m τ (snd (SplitVars Δ)). *)
      (* Proof using. *)
      (*   intros Γ Δ lq; induction lq; intros m' τ'; cbn in *; try lia; *)
      (*     repeat match goal with *)
      (*       | [ H : ?P |- ?P ] => exact H *)
      (*       | [ |- context[SplitVars ?Γ] ] => *)
      (*           let H := fresh in *)
      (*           destruct (SplitVars Γ) eqn:H; subst; cbn in * *)
      (*       | [ |- context[eqb _ _] ] => eq_bool; subst; cbn in * *)
      (*       | [ IH: forall m τ, count_occurences m τ ?a <= count_occurences m τ ?b |- context[count_occurences ?m ?τ ?a]] => *)
      (*           lazymatch goal with *)
      (*           | [ _ : count_occurences m τ a <= count_occurences m τ b |- _ ] => fail *)
      (*           | _ => pose proof (IH m τ) *)
      (*           end  *)
      (*       | [ IH: forall m τ, count_occurences m τ ?a <= count_occurences m τ ?b |- context[count_occurences ?m ?τ ?b]] =>  *)
      (*           lazymatch goal with *)
      (*           | [ _ : count_occurences m τ a <= count_occurences m τ b |- _ ] => fail *)
      (*           | _ => pose proof (IH m τ) *)
      (*           end  *)
      (*          | [ IH : forall m τ, _ <= count_occurences m τ ?v0 |- context[count_occurences ?m ?τ ?v0] ] => specialize (IH m τ); eq_bool; subst; auto *)
      (*          | [ IH : forall m τ, count_occurences m τ ?v0 <= _ |- context[count_occurences ?m ?τ ?v0] ] => specialize (IH m τ); eq_bool; subst; auto *)
      (*       end; try lia. *)
      (*   apply mod_app_base_inv in eq. exfalso; apply neq; apply eq. *)
      (* Qed. *)

      
      
      (* Inductive ctxt_leq : Ctxt -> Ctxt -> renaming -> Type := *)
      (* | EmptyCtxtLeq (ξ : renaming) : *)
      (*   ctxt_leq EmptyCtxt EmptyCtxt ξ *)
      (* | VarExtLeq: forall {Γ Δ : Ctxt} (m : mod) (τ : type) {ξ1 : renaming} (ξ2 : renaming), *)
      (*     (forall n, ξ2 n = renup ξ1 n) -> *)
      (*     ctxt_leq Γ Δ ξ1 -> *)
      (*     ctxt_leq (VarExt Γ m τ) (VarExt Δ m τ) ξ2 *)
      (* | LockExtLeq : forall {Γ Δ : Ctxt} (m : mod) {ξ : renaming}, *)
      (*     ctxt_leq Γ Δ ξ -> ctxt_leq (LockExt Γ m) (LockExt Δ m) ξ *)
      (* | VarAddLeq : forall {Γ Δ : Ctxt} {ξ1 : renaming} (m : mod) (τ : type) (ξ2 : renaming), *)
      (*     (forall n, ξ2 n = S (ξ1 n)) -> *)
      (*     ctxt_leq Γ Δ ξ1 -> *)
      (*     ctxt_leq Γ (VarExt Δ m τ) ξ2 *)
      (* | VarSwapLeqL : forall {Γ Δ : Ctxt} (m1 m2 : mod) (τ1 τ2 : type) {ξ1 : renaming} (ξ2 : renaming), *)
      (*     (forall n, ξ2 n = match n with *)
      (*                  | 0 => ξ1 1 *)
      (*                  | 1 => ξ1 0 *)
      (*                  | S (S n) => ξ1 (S (S n)) *)
      (*                  end) -> *)
      (*     ctxt_leq (VarExt (VarExt Γ m1 τ1) m2 τ2) Δ ξ1 -> *)
      (*     ctxt_leq (VarExt (VarExt Γ m2 τ2) m1 τ1) Δ ξ2 *)
      (* | VarSwapLeqR : forall {Γ Δ : Ctxt} (m1 m2 : mod) (τ1 τ2 : type) {ξ1 : renaming} (ξ2 : renaming), *)
      (*     (forall n, ξ2 n = match n with *)
      (*                  | 0 => 1 *)
      (*                  | 1 => 0 *)
      (*                  | S (S n) => ξ1 (S (S n)) *)
      (*                  end) -> *)
      (*     ctxt_leq Γ (VarExt (VarExt Δ m1 τ1) m2 τ2) ξ1 -> *)
      (*     ctxt_leq Γ (VarExt (VarExt Δ m2 τ2) m1 τ1) ξ2 *)
      (* | LockCollapseLeq : forall {Γ Δ : Ctxt} (m1 m2 : mod) {ξ : renaming}, *)
      (*     ctxt_leq Γ Δ ξ -> *)
      (*     ctxt_leq (LockExt (LockExt Γ m1) m2) (LockExt Δ (mod_app m1 m2)) ξ *)
      (* | LockSplitLeq : forall {Γ Δ : Ctxt} (m1 m2 : mod) {ξ : renaming}, *)
      (*     ctxt_leq Γ Δ ξ -> *)
      (*     ctxt_leq (LockExt Γ (mod_app m1 m2)) (LockExt (LockExt Δ m1) m2) ξ *)
      (* | LockNothingLeq1 : forall {Γ Δ : Ctxt} {ξ : renaming}, *)
      (*     ctxt_leq Γ Δ ξ -> ctxt_leq Γ (LockExt Δ base) ξ *)
      (* | LockNothingLeq2 : forall {Γ Δ : Ctxt} {ξ : renaming}, *)
      (*     ctxt_leq Γ Δ ξ -> ctxt_leq (LockExt Γ base) Δ ξ. *)


      Hint Constructors Ctxt : ctxts.
      Hint Constructors ctxt_equiv : ctxts.
      Hint Constructors ctxt_leq : ctxts.
      Hint Constructors ctxt_leq' : ctxts.
      Hint Constructors ctxt_leq'' : ctxts.

      (* Program Fixpoint ctxt_leq_ext  {Γ Δ ξ1 ξ2} (eq : forall n, ξ1 n = ξ2 n)  (lq : ctxt_leq Γ Δ ξ1) : ctxt_leq Γ Δ ξ2 := *)
      (*   match lq with *)
      (*   | EmptyCtxtLeq _ => EmptyCtxtLeq _ *)
      (*   | @VarExtLeq Γ Δ m τ ξ1' _ eq lq => VarExtLeq m τ ξ2 eq (ctxt_leq_ext _ lq) *)
      (*   | LockExtLeq m lq => LockExtLeq m (ctxt_leq_ext eq lq) *)
      (*   | @VarAddLeq Γ Δ ξ1' m τ _ eq' lq => *)
      (*       VarAddLeq m τ ξ2 _ (ctxt_leq_ext _ lq) *)
      (*   | @VarSwapLeqL Γ Δ m1 m2 τ1 τ2 ξ1' _ eq' lq => *)
      (*       VarSwapLeqL m1 m2 τ1 τ2 _ _ (ctxt_leq_ext _ lq) *)
      (*   | @VarSwapLeqR Γ Δ m1 m2 τ1 τ2 ξ1' _ eq' lq => *)
      (*       VarSwapLeqR m1 m2 τ1 τ2 _ _ (ctxt_leq_ext _ lq) *)
      (*   | LockCollapseLeq m1 m2 lq => *)
      (*       LockCollapseLeq m1 m2 (ctxt_leq_ext eq lq) *)
      (*   | LockSplitLeq m1 m2 lq => LockSplitLeq m1 m2 (ctxt_leq_ext eq lq) *)
      (*   | LockNothingLeq1 lq => LockNothingLeq1 (ctxt_leq_ext eq lq) *)
      (*   | LockNothingLeq2 lq => LockNothingLeq2 (ctxt_leq_ext eq lq) *)
      (*   end. *)
      (* Next Obligation. *)
      (*   unfold ctxt_leq_ext_obligation_4; cbn; rewrite <- eq; rewrite eq'; reflexivity. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   unfold ctxt_leq_ext_obligation_7; cbn. *)
      (*   rewrite <- eq; apply eq'.  *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   unfold ctxt_leq_ext_obligation_10; cbn. rewrite <- eq; apply eq'. *)
      (* Defined. *)
              
      Lemma ctxt_leq_num_vars : forall Γ Δ,
          ctxt_leq Γ Δ ->
          num_vars Γ <= num_vars Δ.
      Proof using.
        intros Γ Δ lq; induction lq; cbn; auto; lia.
      Qed.

      Lemma ctxt_leq'_num_vars : forall Γ Δ,
          ctxt_leq' Γ Δ ->
          num_vars Γ <= num_vars Δ.
      Proof using.
        intros Γ Δ lq; induction lq; cbn; lia.
      Qed.

      (* Fixpoint CtxtLeqSize {Γ Δ} (lq : ctxt_leq Γ Δ) : nat := *)
      (*   match lq with *)
      (*   | EmptyCtxtLeq => 0 *)
      (*   | VarExtLeq m τ x => S (CtxtLeqSize x) *)
      (*   | LockExtLeq  m x => S (CtxtLeqSize x) *)
      (*   | VarAddLeq  m τ x => S (CtxtLeqSize x) *)
      (*   | @VarSwapLeqL Γ Δ m1 m2 τ1 τ2 x => S (CtxtLeqSize x) *)
      (*   | @VarSwapLeqR Γ Δ m1 m2 τ1 τ2 x => S (CtxtLeqSize x) *)
      (*   | @LockCollapseLeq Γ Δ m1 m2 x => S (CtxtLeqSize x) *)
      (*   | @LockSplitLeq Γ Δ m1 m2 x => S (CtxtLeqSize x) *)
      (*   | @LockNothingLeq1 Γ Δ x => S (CtxtLeqSize x) *)
      (*   | @LockNothingLeq2 Γ Δ x => S (CtxtLeqSize x) *)
      (*   end. *)

      (* Fixpoint renaming_of_ctxt_leq {Γ Δ : Ctxt} (lq : ctxt_leq Γ Δ) : renaming := *)
      (*   match lq with *)
      (*   | EmptyCtxtLeq => id_renaming *)
      (*   | VarExtLeq m τ lq => renup (renaming_of_ctxt_leq lq) *)
      (*   | LockExtLeq m lq => renaming_of_ctxt_leq lq *)
      (*   | VarAddLeq m τ lq => fun n => S (renaming_of_ctxt_leq lq n) *)
      (*   | @VarSwapLeqL Γ Δ m1 m2 τ1 τ2 lq => *)
      (*       fun n => *)
      (*         match n with *)
      (*         | 0 => renaming_of_ctxt_leq lq 1 *)
      (*         | 1 => renaming_of_ctxt_leq lq 0 *)
      (*         | S (S m) => renaming_of_ctxt_leq lq (S (S m)) *)
      (*         end *)
      (*   | @VarSwapLeqR Γ Δ m1 m2 τ1 τ2 lq => *)
      (*       fun n => *)
      (*         match renaming_of_ctxt_leq lq n with *)
      (*         | 0 => 1 *)
      (*         | 1 => 0 *)
      (*         | S (S m) => S (S m) *)
      (*         end *)
      (*   | @LockCollapseLeq Γ Δ m1 m2 lq => renaming_of_ctxt_leq lq *)
      (*   | @LockSplitLeq Γ Δ m1 m2 lq => renaming_of_ctxt_leq lq *)
      (*   | @LockNothingLeq1 Γ Δ lq => renaming_of_ctxt_leq lq *)
      (*   | @LockNothingLeq2 Γ Δ lq => renaming_of_ctxt_leq lq *)
      (*   end. *)

      Fixpoint ctxt_leq'_refl (Γ : Ctxt) : ctxt_leq' Γ Γ :=
        match Γ with
        | EmptyCtxt => EmptyCtxtLeq'
        | VarExt Γ m τ => VarExtLeq' m τ (ctxt_leq'_refl Γ)
        | LockExt Γ m => LockExtLeq' m (ctxt_leq'_refl Γ)
        end.
      
      (* Fixpoint ctxt_leq_refl (Γ : Ctxt) : ctxt_leq Γ Γ := *)
      (*   match Γ with *)
      (*   | EmptyCtxt => EmptyCtxtLeq *)
      (*   | VarExt Γ m τ => VarExtLeq m τ (ctxt_leq_refl Γ) *)
      (*   | LockExt Γ m => LockExtLeq m (ctxt_leq_refl Γ) *)
      (*   end. *)

      (* Hint Resolve ctxt_leq_refl : ctxts. *)
      Hint Resolve ctxt_leq'_refl : ctxts.

      Lemma ctxt_leq'_refl_id_renaming : forall Γ n, renaming_of_ctxt_leq' (ctxt_leq'_refl Γ) n = id_renaming n.
      Proof using.
        intro Γ; induction Γ as [| Γ IHΓ m τ | Γ IHΓ m]; intro n; destruct n; cbn;
          unfold id_renaming; cbn; try reflexivity.
        all: rewrite IHΓ; unfold id_renaming; reflexivity.
      Qed.
      
      (* Lemma ctxt_leq_refl_id_renaming : forall Γ n, renaming_of_ctxt_leq (ctxt_leq_refl Γ) n = id_renaming n. *)
      (* Proof using. *)
      (*   intro Γ; induction Γ as [| Γ IHΓ m τ | Γ IHΓ m]; intro n; destruct n; cbn; *)
      (*     unfold id_renaming; cbn; try reflexivity. *)
      (*   all: rewrite IHΓ; unfold id_renaming; reflexivity. *)
      (* Qed. *)
                
      (* Lemma ctxt_leq_ext_size : forall {Γ Δ ξ1} (ξ2 : renaming) (eq : forall n, ξ1 n = ξ2 n) (lq : ctxt_leq Γ Δ ξ1), *)
      (*     CtxtLeqSize lq = CtxtLeqSize (ctxt_leq_ext eq lq). *)
      (* Proof using. *)
      (*   intros Γ Δ ξ1 ξ2 eq lq; revert ξ2 eq; induction lq; try rename ξ2 into ξ1'; intros ξ2 eq; cbn; try reflexivity. *)
      (*   all: try (rewrite <- IHlq; reflexivity). *)
      (* Qed. *)
      (* Opaque ctxt_leq_ext. *)

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

      (* Local Obligation Tactic := idtac. *)
      (* Program Fixpoint CtxtRemoveLeq {Γ Δ} (lq : ctxt_leq Γ Δ) n :  *)
      (*   ctxt_leq (CtxtRemove Γ n) (CtxtRemove Δ (renaming_of_ctxt_leq lq n)) := *)
      (*   match lq with *)
      (*   | EmptyCtxtLeq => EmptyCtxtLeq *)
      (*   | VarExtLeq m τ lq => *)
      (*       match n with *)
      (*       | 0 => lq *)
      (*       | S k => VarExtLeq m τ (CtxtRemoveLeq lq k) *)
      (*       end *)
      (*   | LockExtLeq m lq => LockExtLeq m (CtxtRemoveLeq lq n) *)
      (*   | VarAddLeq m τ lq => VarAddLeq m τ (CtxtRemoveLeq lq n) *)
      (*   | VarSwapLeqL m1 m2 τ1 τ2 lq => *)
      (*       match n with *)
      (*       | 0 => CtxtRemoveLeq lq 1 *)
      (*       | 1 => CtxtRemoveLeq lq 0 *)
      (*       | S (S k) => VarSwapLeqL _ _ _ _ (CtxtRemoveLeq lq (S (S k))) *)
      (*       end *)
      (*   | @VarSwapLeqR _ Δ' m1 m2 τ1 τ2 lq => _ *)
      (*       match renaming_of_ctxt_leq lq n with *)
      (*       | 0 => CtxtRemoveLeq lq n *)
      (*       | 1 => CtxtRemoveLeq lq n *)
      (*       | S (S k) => _ (* @VarSwapLeqR _ Δ' m1 m2 τ1 τ2 (CtxtRemoveLeq lq n) *) *)
      (*       end *)
      (*   | LockCollapseLeq m1 m2 lq => _ *)
      (*   | LockSplitLeq m1 m2 lq => _ *)
      (*   | LockNothingLeq1 lq => _ *)
      (*   | LockNothingLeq2 lq => _ *)
      (*   end. *)
      (* Next Obligation. *)
      (*   destruct (renaming_of_ctxt_leq lq n). exact x. *)
      (*   destruct n0. exact x. *)
      (*   apply VarSwapLeqR. exact x. *)
      (* Defined. *)
      (* Next Obligation. *)
        
        



      (* (* #[local] Obligation Tactic := intros; subst. *) *)
      (* Program Fixpoint CtxtLeqTrans {Γ Δ E} *)
      (*   (lq1 : ctxt_leq Γ Δ) *)
      (*   (lq2 : ctxt_leq Δ E) *)
      (*   {measure (CtxtLeqSize lq1 + CtxtLeqSize lq2)} *)
      (*   : {pf : ctxt_leq Γ E | CtxtLeqSize pf <= CtxtLeqSize lq1 + CtxtLeqSize lq2 } := *)
      (*   match lq2 with *)
      (*   | EmptyCtxtLeq => *)
      (*       match lq1 with *)
      (*       | EmptyCtxtLeq => EmptyCtxtLeq *)
      (*       | VarExtLeq _ _ lq1 => _ *)
      (*       | LockExtLeq m lq => _ *)
      (*       | VarAddLeq m τ  lq => _ *)
      (*       | VarSwapLeqL m1 m2 τ1 τ2  lq => *)
      (*           VarSwapLeqL m1 m2 τ1 τ2 (CtxtLeqTrans lq EmptyCtxtLeq) *)
      (*       | VarSwapLeqR m1 m2 τ1 τ2  lq => _ *)
      (*       | LockCollapseLeq m1 m2 lq => _ *)
      (*       | LockSplitLeq m1 m2 lq => _ *)
      (*       | LockNothingLeq1 lq => _ *)
      (*       | LockNothingLeq2 lq => *)
      (*           LockNothingLeq2 (CtxtLeqTrans lq lq2) *)
      (*       end *)
      (*   | VarExtLeq m τ lq4 => *)
      (*       match lq1 with *)
      (*       | EmptyCtxtLeq => VarExtLeq m τ (CtxtLeqTrans lq1 lq4) *)
      (*       | VarExtLeq _ _ lq3 => *)
      (*           VarExtLeq m τ (CtxtLeqTrans lq3 lq4) *)
      (*       | LockExtLeq m lq => _ *)
      (*       | VarAddLeq _ _ lq3 => *)
      (*           VarAddLeq m τ (CtxtLeqTrans lq3 lq4) *)
      (*       | VarSwapLeqL m1 m2 τ1 τ2 lq => *)
      (*           VarSwapLeqL m1 m2 τ1 τ2 (CtxtLeqTrans lq lq2) *)
      (*       | VarSwapLeqR m1 m2 τ1 τ2 lq => _ *)
      (*       | LockCollapseLeq m1 m2 lq => _ *)
      (*       | LockSplitLeq m1 m2 lq => _ *)
      (*       | LockNothingLeq1 lq => _ *)
      (*       | LockNothingLeq2 lq => _ *)
      (*       end *)
      (*   | LockExtLeq m lq => _ *)
      (*   | VarAddLeq m τ lq => _ *)
      (*   | VarSwapLeqL m1 m2 τ1 τ2 lq => _ *)
      (*   | VarSwapLeqR m1 m2 τ1 τ2 lq => _ *)
      (*   | LockCollapseLeq m1 m2 lq => _ *)
      (*   | LockSplitLeq m1 m2 lq => _ *)
      (*   | LockNothingLeq1 lq => _ *)
      (*   | LockNothingLeq2 lq => _ *)
      (*   end. *)
      (* Next Obligation. *)
      (*   cbn; unfold eq_rect; cbn; destruct Heq_Δ; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (* (*   rewrite eq; destruct n; [reflexivity|]. *) *)
      (* (*   destruct n; [reflexivity|]. reflexivity. *) *)
      (* (* Defined. *) *)
      (* (* Next Obligation. *) *)
      (*   cbn; inversion Heq_lq1; apply Eqdep.EqdepTheory.inj_pair2 in H0; rewrite <- H0; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   match goal with *)
      (*   | [|- context[proj1_sig ?a]] => *)
      (*       let lq := fresh "lq" in *)
      (*       generalize a; intro lq *)
      (*   end; cbn. *)
      (*   pose proof (proj2_sig lq0) as H0; cbn in H0. *)
      (*   inversion Heq_lq1; apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   cbn; inversion Heq_lq1. *)
      (*   apply Eqdep.EqdepTheory.inj_pair2 in H0; rewrite <- H0; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   match goal with *)
      (*   | [|- context[proj1_sig ?a]] => *)
      (*       let lq := fresh "lq" in *)
      (*       let H := fresh "H" in  *)
      (*       generalize a; intro lq; pose proof (proj2_sig lq) as H; cbn in H *)
      (*   end; cbn. *)
      (*   inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (* (*   cbn. rewrite eq; rewrite eq0; unfold renup. *) *)
      (* (*   destruct n; reflexivity. *) *)
      (* (* Defined. *) *)
      (* (* Next Obligation. *) *)
      (*   cbn. elim_eq_rect; cbn. *)
      (*   inversion Heq_lq2. *)
      (*   apply Eqdep.EqdepTheory.inj_pair2 in H0; rewrite <- H0; cbn. *)
      (*   inversion Heq_lq1. inversion Heq_Δ. *)
      (*   destruct H5; destruct H6; destruct H7. *)
      (*   apply Eqdep.EqdepTheory.inj_pair2 in H4; rewrite <- H4; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   cbn. inversion Heq_Δ. destruct H1; destruct H2; destruct H3. repeat (elim_eq_rect; cbn). *)
      (*   match goal with *)
      (*   | [|- context[proj1_sig ?a]] => *)
      (*       let lq := fresh "lq" in *)
      (*       let H := fresh "H" in  *)
      (*       generalize a; intro lq; pose proof (proj2_sig lq) as H; cbn in H *)
      (*   end; cbn in *. *)
      (*   inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn. *)
      (*   inversion Heq_lq2. apply Eqdep.EqdepTheory.inj_pair2 in H2; rewrite <- H2; cbn. *)
      (*   lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (* (*   rewrite eq; rewrite eq0; unfold renup; reflexivity. *) *)
      (* (* Defined. *) *)
      (* (* Next Obligation. *) *)
      (*   cbn. elim_eq_rect; cbn. *)
      (*   inversion Heq_lq2. apply Eqdep.EqdepTheory.inj_pair2 in H0; rewrite <- H0; cbn. *)
      (*   inversion Heq_Δ. destruct H2; destruct H3; destruct H4. *)
      (*   inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn. *)
      (*   lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   inversion Heq_Δ. destruct H1; destruct H2; destruct H3; repeat (elim_eq_rect; cbn). *)
      (*   match goal with *)
      (*   | [|- context[proj1_sig ?a]] => *)
      (*       let lq := fresh "lq" in *)
      (*       let H := fresh "H" in  *)
      (*       generalize a; intro lq; pose proof (proj2_sig lq) as H; cbn in H *)
      (*   end; cbn in *. *)
      (*   inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn. *)
      (*   inversion Heq_lq2. apply Eqdep.EqdepTheory.inj_pair2 in H2; rewrite <- H2; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (* (*   destruct n; rewrite eq; [reflexivity | destruct n; reflexivity]. *) *)
      (* (* Defined. *) *)
      (* (* Next Obligation. *) *)
      (*   cbn; inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H0; rewrite <- H0; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   elim_eq_rect; cbn. *)
      (*   match goal with *)
      (*   | [|- context[proj1_sig ?a]] => *)
      (*       let lq := fresh "lq" in *)
      (*       let H := fresh "H" in  *)
      (*       generalize a; intro lq; pose proof (proj2_sig lq) as H; cbn in H *)
      (*   end; cbn in *. *)
      (*   inversion Heq_lq1. apply Eqdep.EqdepTheory.inj_pair2 in H1; rewrite <- H1; cbn; lia. *)
      (* Defined. *)
      (* Next Obligation. *)
      (*   rename wildcard'0 into Δ. *)
      (*   rename wildcard'2 into E. *)
        
      (* Lemma CtxtLeqTrans : forall Γ Δ E ξ1 ξ2, *)
      (*     ctxt_leq Γ Δ ξ1 -> *)
      (*     ctxt_leq Δ E ξ2 -> *)
      (*     ctxt_leq Γ E (fun n => ξ2 (ξ1 n)). *)
      (* Proof using. *)
      (*   intros Γ Δ E ξ1 ξ2 lq1 lq2; revert Γ ξ1 lq1; induction lq2; *)
      (*     intros Γ' ξ1' lq1. *)
      (*   - revert lq1; induction Γ'; intros lq1; eauto with ctxts. *)
      (*     inversion lq1; subst. *)
      (*     apply ctxt_leq_num_vars in lq1; cbn in lq1; lia. *)
      (*     inversion lq1; subst. apply IHΓ' in H4. *)
      (*     eauto with ctxts. *)
      (*   - inversion lq1; subst. *)
      (*     -- apply IHlq2 in H7. *)
      (*        eapply VarExtLeq with (ξ1 := fun n => ξ1 (ξ0 n)); try assumption. *)
      (*        intro n; rewrite H0; rewrite H6; unfold renup. *)
      (*        destruct n; reflexivity. *)
      (*     -- apply @VarAddLeq with (ξ1 := fun n => ξ1 (ξ0 n)). *)
      (*        intro n; rewrite H0; rewrite H6; unfold renup; reflexivity. *)
      (*        apply IHlq2; assumption. *)
      (*     -- eapply @VarAddLeq. *)
      (*        2: { eapply VarSwapLeqL. *)
      (*             2: { apply IHlq2. *)
      (*        intro n; rewrite H1; rewrite H0; destruct n; cbn. *)
            
      
      (* | CtxtLeqTrans : forall {Γ Δ E: Ctxt} {ξ1 ξ2 : renaming} (ξ3 : renaming), *)
      (*     (forall n, ξ3 n = ξ2 (ξ1 n)) -> *)
      (*     ctxt_leq Γ Δ ξ1 -> *)
      (*     ctxt_leq Δ E ξ2 -> *)
      (*     ctxt_leq Γ E ξ3. *)

      Theorem ctxt_equiv_leq' : forall {Γ Δ : Ctxt},
          ctxt_equiv Γ Δ ->
          exists (lq : ctxt_leq' Γ Δ), True.
      Proof using.
        intros Γ Δ eqv; induction eqv;
          repeat match goal with
            | [ H : exists (_ : ctxt_leq' _ _), True  |- _ ] =>
                destruct H
            | [ H : True |- _ ] => clear H
            end;
          try (eexists; econstructor;
               eauto with ctxts; fail).
      Qed.


        
      (* Theorem ctxt_equiv_leq : forall Γ Δ, *)
      (*     ctxt_equiv Γ Δ -> *)
      (*     ctxt_leq  Γ Δ id_renaming. *)
      (* Proof using. *)
      (*   intros Γ Δ eqv; induction eqv; try (econstructor; eauto; fail). *)
      (*   - apply VarExtLeq with (ξ1 := id_renaming); auto. *)
      (*     intro n; symmetry; apply renup_id. *)
      (*   - eapply CtxtLeqTrans; eauto. *)
      (*     intro n; unfold id_renaming; reflexivity. *)
      (* Qed. *)

      (* Corollary ctxt_equiv_leq' : forall Γ Δ, *)
      (*     ctxt_equiv Γ Δ -> *)
      (*     ctxt_leq Δ Γ id_renaming. *)
      (* Proof using. *)
      (*   intros Γ Δ H0; symmetry in H0; apply ctxt_equiv_leq; assumption. *)
      (* Qed. *)

      Lemma renup_id_inv : forall ξ1 ξ2 : renaming,
          (forall n, ξ1 n = n) ->
          (forall n, renup ξ2 n = ξ1 n) ->
          forall n, ξ2 n = n.
      Proof using.
        intros ξ1 ξ2 H0 H1 n;
          specialize (H1 (S n)); cbn in H1; rewrite H0 in H1; inversion H1; subst;
          repeat rewrite H3; reflexivity.
      Qed.

      (* Theorem ctxt_leq_equiv : forall Γ Δ ξ1 ξ2, *)
      (*     (forall n, ξ1 n = n) -> *)
      (*     (forall n, ξ2 n = n) -> *)
      (*     ctxt_leq Γ Δ ξ1 -> *)
      (*     ctxt_leq Δ Γ ξ2 -> *)
      (*     ctxt_equiv Γ Δ. *)
      (* Proof using. *)
      (*   intros Γ Δ ξ1 ξ2 ξ1_id ξ2_id lq1;  *)
      (*     revert ξ2 ξ1_id ξ2_id; induction lq1; *)
      (*     try rename ξ2 into ξ1'; *)
      (*     intros ξ2 ξ1_id ξ2_id lq2; try (constructor; fail). *)
      (*   - inversion lq2; subst. *)
      (*     2: { specialize (H6 0); specialize (ξ2_id 0); rewrite ξ2_id in H6; inversion H6. } *)
      (*     2: { specialize (H8 0); specialize (ξ2_id 0); rewrite ξ2_id in H8; inversion H8. } *)
      (*     2: { admit. } *)
      (*     -- apply VarExtEquiv. *)
      (*        apply IHlq1 with (ξ2 := ξ0); auto. *)
      (*        eapply renup_id_inv with (ξ1 := ξ1'); auto. *)
      (*        apply renup_id_inv with (ξ1 := ξ2); auto. *)
      (* Abort. *)

      (* Theorem in_leq_ctxt : forall Γ Δ ξ, *)
      (*     ctxt_leq Γ Δ ξ -> *)
      (*     forall n m τ m', InCtxt n m τ m' Γ -> InCtxt (ξ n) m τ m' Δ. *)
      (* Proof using. *)
      (*   intros Γ Δ ξ lq; induction lq; intros x m' τ' m'' i;  *)
      (*      try (inversion i; subst; auto; econstructor; eauto; fail); *)
      (*     try (rewrite H0; cbn; econstructor; eauto; fail). *)
      (*   - inversion i; subst;  rewrite H0; cbn; try (repeat constructor; auto; fail). *)
      (*   - inversion i; subst; [| inversion i0; subst]; rewrite H0; cbn; repeat constructor; auto. *)
      (*   - inversion i; subst; inversion i0; subst; rewrite mod_app_assoc; constructor; auto. *)
      (*   - inversion i; subst; rewrite <- mod_app_assoc; repeat constructor; auto. *)
      (*   - assert (m'' = mod_app m'' base) as base_eq by reflexivity; *)
      (*       rewrite base_eq; constructor; auto. *)
      (*   - rewrite H0; auto. *)
      (* Qed. *)

      (* Theorem ctxt_leq_proper : forall Γ Δ E Z ξ, *)
      (*     ctxt_equiv Γ E -> *)
      (*     ctxt_equiv Δ Z -> *)
      (*     ctxt_leq Γ Δ ξ -> *)
      (*     ctxt_leq E Z ξ. *)
      (* Proof using. *)
      (*   intros Γ Δ E Z ξ H0 H1 H2. *)
      (*   apply ctxt_equiv_leq' in H0. *)
      (*   apply ctxt_equiv_leq in H1. *)
      (*   apply @CtxtLeqTrans with (ξ1 := id_renaming) (ξ2 := ξ) (Δ := Γ); auto. *)
      (*   apply @CtxtLeqTrans with (ξ1 := ξ) (ξ2 := id_renaming) (Δ := Δ); auto. *)
      (* Qed. *)
          
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

      Theorem ctxt_leq'_all_locks : forall {Γ Δ : Ctxt},
          ctxt_leq' Γ Δ -> all_locks Γ = all_locks Δ.
      Proof using.
        intros Γ Δ lq; induction lq; cbn; auto.
        - rewrite IHlq; auto.
        - apply mod_app_assoc.
        - symmetry; apply mod_app_assoc.
        - transitivity (all_locks Δ); assumption.
      Qed.

      Theorem ctxt_leq''_all_locks : forall {Γ Δ : Ctxt} {ξ : renaming},
          ctxt_leq'' Γ ξ Δ -> all_locks Γ = all_locks Δ.
      Proof using.
        intros Γ Δ ξ lq; induction lq; cbn; auto.
        - rewrite IHlq; reflexivity.
        - apply mod_app_assoc.
        - symmetry; apply mod_app_assoc.
        - transitivity (all_locks Δ); assumption.
      Qed.

      Theorem ctxt_leq''_locks : forall {Γ Δ : Ctxt} {ξ : renaming},
          ctxt_leq'' Γ ξ Δ ->
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

      Theorem ctxt_leq'_remove_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p : PName},
          ctxt_leq' Γ1 Γ2 ->
          remove_lock_after Γ1 m p = Some Δ1 ->
          remove_lock_after Γ2 m p = Some Δ2 ->
          ctxt_leq' Δ1 Δ2.
      Proof using.
        intros Γ1 Γ2 Δ1 Δ2 m p lq; revert Δ1 Δ2 m p; induction lq; cbn;
          try rename m into m'; intros Δ1 Δ2 m p eq1 eq2;
          repeat match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            | [ H : Some ?a = Some ?b |- _ ] =>
                inversion H; subst; clear H
            | [ |- ctxt_leq' ?a ?a ] => apply ctxt_leq'_refl
            | [ H : ctxt_leq' ?Γ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
                rewrite <- (ctxt_leq'_all_locks H) in H'
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
            | [ IH : forall Δ1 Δ2 m p, remove_lock_after ?Γ1 m p = Some Δ1 -> remove_lock_after ?Γ2 m p = Some Δ2 -> ctxt_leq' Δ1 Δ2, H1 : remove_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : remove_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
                lazymatch goal with
                | [ H : ctxt_leq' Δ1 Δ2 |- _ ] => fail
                | _ => pose proof (IH Δ1 Δ2 m p H1 H2)
                end 
            end; try (econstructor; eauto; fail).
        - apply prefixb_PrefixOf in H0.
          assert (PrefixOf (cons m p) (mod_app (all_locks Γ) m1)) as H5
              by (transitivity (all_locks Γ); auto; apply PrefixOf_app).
          apply PrefixOf_prefixb in H5; rewrite H5 in H1; inversion H1.
        - pose proof (readd_remove_prefix H2); subst; clear H0 H2.
          pose proof (only_prefixes_changable H4).
          destruct (remove_Prefix (cons m0 p) m1) as [m5|] eqn:eqm5;
            [|exfalso; destruct (prefix_remove_Some H0) as [m5 eqm5']; rewrite eqm5' in eqm5; inversion eqm5].
          pose proof (readd_remove_prefix eqm5); subst; clear eqm5.
          rewrite mod_app_assoc in H3. rewrite change_mod_app in H3.
          inversion H3; subst; clear H0 H3.
          rewrite change_mod_app in H4; inversion H4; subst; clear H4.
          rewrite <- mod_app_assoc. apply LockCollapseLeq'.
        - pose proof (readd_remove_prefix H3); subst; clear H0 H1 H3.
          rewrite mod_app_assoc in H2. rewrite remove_app in H2; inversion H2; subst; clear H2.
          pose proof (only_prefixes_changable H5).
          destruct (remove_Prefix (cons m3 p) m2) as [m6|] eqn:eq.
          2: {
            exfalso; destruct (prefix_remove_Some H0) as [m6 eq']; rewrite eq' in eq; inversion eq.
          }
          pose proof (readd_remove_prefix eq); subst; clear H0 eq.
          rewrite <- mod_app_assoc in H4. cbn in H4.
          rewrite change_mod_app in H4; inversion H4; subst; clear H4.
          rewrite change_mod_app in H5; inversion H5; subst; clear H5.
          rewrite mod_app_assoc. apply LockCollapseLeq'.
        - pose proof (readd_remove_prefix H2); subst; clear H1 H2.
          pose proof (only_prefixes_changable H3).
          destruct (remove_Prefix (cons m0 p) m1) as [m5|] eqn:eq.
          2: {
            exfalso; destruct (prefix_remove_Some H1) as [m6 eq']; rewrite eq' in eq; inversion eq.
          }
          pose proof (readd_remove_prefix eq); subst; clear H0 eq.
          rewrite mod_app_assoc in H4; rewrite change_mod_app in H4; inversion H4; subst; clear H1 H4.
          rewrite change_mod_app in H3; inversion H3; subst; clear H3.
          rewrite <- mod_app_assoc. constructor.
        - assert (PrefixOf (cons m p) (mod_app (all_locks Γ) m1)) as H5
              by (transitivity (all_locks Γ); [apply prefixb_PrefixOf; auto | apply PrefixOf_app]).
          apply PrefixOf_prefixb in H5. rewrite H5 in H0. inversion H0.
        - pose proof (readd_remove_prefix H3); subst; clear H1 H3.
          pose proof (readd_remove_prefix H2); rewrite mod_app_assoc in H1; apply mod_app_inj in H1;
            subst; clear H2 H0.
          pose proof (only_prefixes_changable H4).
          destruct (remove_Prefix (cons m0 p) m2) as [m6|] eqn:eq.
          2: {
            exfalso; destruct (prefix_remove_Some H0) as [m6 eq']; rewrite eq' in eq; inversion eq.
          }
          pose proof (readd_remove_prefix eq); subst; clear H0 eq.
          rewrite change_mod_app in H4; inversion H4; subst; clear H4.
          rewrite <-  mod_app_assoc in H5; cbn in H5. rewrite change_mod_app in H5.
          inversion H5; subst; clear H5.
          rewrite mod_app_assoc. constructor.
        - eq_bool. inversion eq. inversion eq2.
        - eq_bool. inversion eq. inversion eq1.
        - destruct (remove_lock_after Δ m p) as [Δ3|] eqn:eqΔ3.
          2: {
            apply remove_lock_after_prefix in eq1. rewrite (ctxt_leq'_all_locks lq1) in eq1.
            exfalso; destruct (remove_lock_after_defined eq1); rewrite H0 in eqΔ3; inversion eqΔ3.
          }
          apply @CtxtLeq'Trans with (Δ := Δ3).
          eapply IHlq1; eauto.
          eapply IHlq2; eauto.
      Qed.

      Theorem ctxt_leq''_change_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p q : PName},
          ctxt_leq'' Γ1 ξ Γ2 ->
          change_lock_after Γ1 m p q = Some Δ1 ->
          change_lock_after Γ2 m p q = Some Δ2 ->
          ctxt_leq'' Δ1 ξ Δ2.
      Proof using.
        intros Γ1 Γ2 Δ1 Δ2 ξ m p q lq; revert Δ1 Δ2 m p q; induction lq; try rename m into m'; intros Δ1 Δ2 m p q eq1 eq2;
          cbn in *;
          repeat match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            | [ H : Some _ = None |- _ ] => inversion H
            | [ H : cons _ _ = base |- _ ] => inversion H
            | [ H : base = cons _ _ |- _ ] => inversion H
            | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
            | [ H : ctxt_leq'' ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
                rewrite <- (ctxt_leq''_all_locks H) in H'
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
            | [ IH : forall Δ1 Δ2 m p q, change_lock_after ?Γ1 m p q = Some Δ1 -> change_lock_after ?Γ2 m p q = Some Δ2 -> ctxt_leq'' Δ1 ?ξ Δ2, H1 : change_lock_after ?Γ1 ?m ?p ?q = Some ?Δ1, H2 : change_lock_after ?Γ2 ?m ?p ?q = Some ?Δ2 |- _ ] =>
                lazymatch goal with
                | [ H : ctxt_leq'' Δ1 ξ Δ2 |- _ ] => fail
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
            rewrite (ctxt_leq''_all_locks lq1) in lox;
            destruct (@change_lock_after_defined _ _ _ q lox) as [Δ3 eq3]; clear lox.
          pose proof (IHlq1 _ _ _ _ _ eq1 eq3).
          pose proof (IHlq2 _ _ _ _ _ eq3 eq2).
          eapply CtxtLeq''Trans; eauto.
      Qed.
          
      Theorem ctxt_leq''_remove_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p : PName},
          ctxt_leq'' Γ1 ξ Γ2 ->
          remove_lock_after Γ1 m p = Some Δ1 ->
          remove_lock_after Γ2 m p = Some Δ2 ->
          ctxt_leq'' Δ1 ξ Δ2.
      Proof using.
        intros Γ1 Γ2 Δ1 Δ2 ξ m p lq; revert Δ1 Δ2 m p; induction lq; try rename m into m'; intros Δ1 Δ2 m p eq1 eq2;
          cbn in *;
          repeat match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            | [ H : Some _ = None |- _ ] => inversion H
            | [ H : cons _ _ = base |- _ ] => inversion H
            | [ H : base = cons _ _ |- _ ] => inversion H
            | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
            | [ H : ctxt_leq'' ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
                rewrite <- (ctxt_leq''_all_locks H) in H'
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
            | [ IH : forall Δ1 Δ2 m p, remove_lock_after ?Γ1 m p = Some Δ1 -> remove_lock_after ?Γ2 m p = Some Δ2 -> ctxt_leq'' Δ1 ?ξ Δ2, H1 : remove_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : remove_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
                lazymatch goal with
                | [ H : ctxt_leq'' Δ1 ξ Δ2 |- _ ] => fail
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
          rewrite (ctxt_leq''_all_locks lq1) in H1.
          apply remove_lock_after_defined in H1.
          destruct H1 as [Δ3 eq3].
          specialize (IHlq1 _ _ _ _ eq1 eq3).
          specialize (IHlq2 _ _ _ _ eq3 eq2).
          apply @CtxtLeq''Trans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
      Qed.

      Theorem ctxt_leq''_add_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p : PName},
          ctxt_leq'' Γ1 ξ Γ2 ->
          add_lock_after Γ1 m p = Some Δ1 ->
          add_lock_after Γ2 m p = Some Δ2 ->
          ctxt_leq'' Δ1 ξ Δ2.
      Proof using.
        intros Γ1 Γ2 Δ1 Δ2 ξ m p lq; revert Δ1 Δ2 m p; induction lq; try rename m into m'; intros Δ1 Δ2 m p eq1 eq2;
          cbn in *;
          repeat match goal with
            | [ H : None = Some _ |- _ ] => inversion H
            | [ H : Some _ = None |- _ ] => inversion H
            | [ H : cons _ _ = base |- _ ] => inversion H
            | [ H : base = cons _ _ |- _ ] => inversion H
            | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
            | [ H : ctxt_leq'' ?Γ ?ξ ?Δ, H' : context[all_locks ?Δ] |- _ ] =>
                rewrite <- (ctxt_leq''_all_locks H) in H'
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
            | [ IH : forall Δ1 Δ2 m p, add_lock_after ?Γ1 m p = Some Δ1 -> add_lock_after ?Γ2 m p = Some Δ2 -> ctxt_leq'' Δ1 ?ξ Δ2, H1 : add_lock_after ?Γ1 ?m ?p = Some ?Δ1, H2 : add_lock_after ?Γ2 ?m ?p = Some ?Δ2 |- _ ] =>
                lazymatch goal with
                | [ H : ctxt_leq'' Δ1 ξ Δ2 |- _ ] => fail
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
          rewrite (ctxt_leq''_all_locks lq1) in H1.
          apply @add_lock_after_defined  with (p := p) in H1.
          destruct H1 as [Δ3 eq3].
          specialize (IHlq1 _ _ _ _ eq1 eq3).
          specialize (IHlq2 _ _ _ _ eq3 eq2).
          apply @CtxtLeq''Trans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
      Qed.

    End LockChanges.

  End Contexts.
  
  Section TypeSystem.

    Inductive Typed : Ctxt -> expr -> type -> Prop :=
    | VarTyping {Γ : Ctxt} {n : nat} {τ : type} (m : mod) (i : InCtxt n m τ m Γ)
      : Typed Γ (var n) τ
    | UnitTyping (Γ : Ctxt) : Typed Γ uu UnitT
    | AtTyping {Γ : Ctxt} {e : expr} {τ : type} (p : PName) (pf : Typed (LockExt Γ p) e τ)
      : Typed Γ (atE p e) (AtT p τ)
    | LetTyping {Γ : Ctxt} {e1 e2 : expr} {τ σ : type} {p : PName}
        (pf1 : Typed Γ e1 (AtT p τ)) (pf2 : Typed (VarExt Γ p τ) e2 σ)
      : Typed Γ (letAt p e1 e2) σ
    | PairTyping {Γ : Ctxt} {e1 e2 : expr} {τ1 τ2 : type}
        (pf1 : Typed Γ e1 τ1) (pf2 : Typed Γ e2 τ2)
      : Typed Γ (pair e1 e2) (TimesT τ1 τ2)
    | ProjLTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed Γ e (TimesT τ1 τ2))
      : Typed Γ (pi1 e) τ1
    | ProjRTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed Γ e (TimesT τ1 τ2))
      : Typed Γ (pi2 e) τ2
    | InlTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed Γ e τ1)
      : Typed Γ (inl e) (PlusT τ1 τ2)
    | InrTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed Γ e τ2)
      : Typed Γ (inr e) (PlusT τ1 τ2)
    | CaseTyping {Γ : Ctxt} {e1 e2 e3 : expr} {τ1 τ2 σ : type}
        (pf1 : Typed Γ e1 (PlusT τ1 τ2))
        (pf2 : Typed (VarExt Γ base τ1) e2 σ)
        (pf3 : Typed (VarExt Γ base τ2) e3 σ)
      : Typed Γ (caseE e1 e2 e3) σ
    | EfqlTyping {Γ : Ctxt} {e : expr}
        (pf : Typed Γ e VoidT) (τ : type)
      : Typed Γ (efql e) τ
    | LamTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed (VarExt Γ base τ1) e τ2)
      : Typed Γ (lam τ1 e) (ArrT τ1 τ2)
    | AppTyping {Γ : Ctxt} {e1 e2 : expr} {τ1 τ2 : type}
        (pf1 : Typed Γ e1 (ArrT τ1 τ2))
        (pf2 : Typed Γ e2 τ1)
      : Typed Γ (appE e1 e2) τ2
    | SendTyping {Γ Δ : Ctxt} {m : mod} {p q : PName} {e : expr} {τ : type}
        (eq : change_lock_after Γ m p q = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanSend (cons m p) (cons m q))
      : Typed Γ (send e m p q) τ
    | UpTyping {Γ Δ : Ctxt} {m : mod} {p : PName} {e : expr} {τ : type}
        (eq : remove_lock_after Γ m p = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanUp m (cons m p))
      : Typed Γ (up e m p) τ
    | DownTyping {Γ Δ : Ctxt} {m : mod} {p : PName} {e : expr} {τ : type}
        (eq : add_lock_after Γ m p = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanDown (cons m p) m)
      : Typed Γ (down e m p) τ
    .


    
    (* Lemma leq_lock_app : forall Γ Γ1 Γ2 (p : PName) Δ ξ, *)
    (*     ctxt_equiv Γ (ctxt_app (LockExt Γ1 p) Γ2) -> *)
    (*     ctxt_leq Γ Δ ξ -> *)
    (*     exists Δ1 Δ2, ctxt_equiv Δ (ctxt_app (LockExt Δ1 p) Δ2) /\ *)
    (*                ctxt_leq Γ1 Δ1 (fun n =>  ξ (num_vars Γ2 + n) - num_vars Δ2) /\ *)
    (*                ctxt_leq Γ2 Δ2 ξ. *)
    (* Proof using. *)
    (*   intros Γ Γ1 Γ2 p Δ ξ eqv lq; revert Γ1 Γ2 p eqv; induction lq; *)
    (*     intros Γ1 Γ2 p eqv. *)
    (* Admitted. *)
      
      (* intros Γ1 Γ2 p. *)
      (* generalize (eq_refl (ctxt_app (LockExt Γ1 p) Γ2)); *)
      (*   generalize (ctxt_app (LockExt Γ1 p) Γ2) at 1 3 as Γ; *)
      (*   intros Γ eq Δ ξ lq; revert Γ1 Γ2 p eq; induction lq; *)
      (*   intros Γ1 Γ2 p eq. *)
      (* - apply ctxt_app_empty_inv1 in eq; inversion eq. *)
      (* - destruct Γ2; cbn in *; inversion eq; subst. *)
      (*   specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*   destruct IHlq as [Δ1 [Δ2 [eqv [lq1 lq2]]]]. *)
      (*   exists Δ1; exists (VarExt Δ2 m0 t); cbn; split; [| split]. *)
      (*   -- constructor; eauto. *)
      (*   -- eapply ctxt_leq_ext; eauto. *)
      (*      intros n; rewrite H0; cbn; lia. *)
      (*   -- econstructor; eauto. *)
      (* - destruct Γ2; cbn in *; inversion eq; subst. *)
      (*   -- exists Δ; exists EmptyCtxt; cbn; split; [| split]. *)
      (*      --- reflexivity. *)
      (*      --- apply ctxt_leq_ext with (ξ1 := ξ); [intro n; lia | assumption]. *)
      (*      --- constructor. *)
      (*   -- specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*      destruct IHlq as [Δ1 [Δ2 [Δeq [lq1 lq2]]]]. *)
      (*      exists Δ1; exists (LockExt Δ2 m0); split; [| split]. *)
      (*      --- cbn; constructor; assumption. *)
      (*      --- cbn; assumption. *)
      (*      --- constructor; assumption. *)
      (* - specialize (IHlq Γ1 Γ2 p eq). *)
      (*   destruct IHlq as [Δ1 [Δ2 [eqΔ [lq1 lq2]]]]. *)
      (*   exists Δ1; exists (VarExt Δ2 m τ); split; [| split]. *)
      (*   -- cbn; constructor; assumption. *)
      (*   -- eapply ctxt_leq_ext; [| exact lq1]. *)
      (*      intro n; rewrite H0; cbn; lia. *)
      (*   -- econstructor; eauto. *)
      (* - do 2 (destruct Γ2; cbn in *; inversion eq; subst). *)
      (*   specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*   destruct IHlq as [Δ1 [Δ2 [eqΔ [lq1 lq2]]]]. *)
      (*   exists Δ1; exists (VarExt (VarExt Δ2 m t) m0 t0); split; [| split]. *)
      (*   -- cbn; do 2 constructor; assumption. *)
      (*   -- eapply ctxt_leq_ext; [| exact lq1]. *)
      (*      intro n; rewrite H0; cbn; reflexivity. *)
      (*   -- econstructor; eauto; fail. *)
      (* - destruct Γ2; [| |destruct Γ2 ]; cbn in *; inversion eq; subst. *)
      (*   -- exists (LockExt Δ m1); exists EmptyCtxt; split; [| split]. *)
      (*      --- cbn; assert (cons m1 p = mod_app m1 p) as eq' by reflexivity; rewrite eq'; *)
      (*            constructor; reflexivity. *)
      (*      --- cbn. econstructor. eapply ctxt_leq_ext; [| exact lq]. intro n; lia. *)
      (*      --- constructor. *)
      (*   -- exists Δ; exists (LockExt EmptyCtxt m); cbn; split; [| split]. *)
      (*      --- constructor; reflexivity. *)
      (*      --- eapply ctxt_leq_ext; [| exact lq]; intro n; lia. *)
      (*      --- repeat constructor. *)
      (*   -- specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*      destruct IHlq as [Δ1 [Δ2 [eqv [lq1 lq2]]]]. *)
      (*      exists Δ1; exists (LockExt Δ2 (mod_app m0 m)); split; [| split]. *)
      (*      --- constructor; assumption. *)
      (*      --- assumption. *)
      (*      --- econstructor; eauto. *)
      (* - destruct Γ2; cbn in *; inversion eq; subst. *)
      (*   -- exists Δ; exists EmptyCtxt; split; [| split]. *)
      (*      --- cbn; econstructor; reflexivity. *)
      (*      --- eapply ctxt_leq_ext; [| exact lq]; intro n; cbn; lia. *)
      (*      --- constructor. *)
      (*   -- specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*      destruct IHlq as [Δ1 [Δ2 [eqv [lq1 lq2]]]]. *)
      (*      exists Δ1; exists (LockExt (LockExt Δ2 m1) m2); split; [| split]. *)
      (*      --- cbn; do 2 constructor; assumption. *)
      (*      --- eapply ctxt_leq_ext; [| exact lq1]; intro n; cbn; lia. *)
      (*      --- constructor; auto. *)
      (* - specialize (IHlq Γ1 Γ2 p eq). *)
      (*   destruct IHlq as [Δ1 [Δ2 [eqv [lq1 lq2]]]]. *)
      (*   exists Δ1; exists Δ2; split; [constructor | split]; assumption. *)
      (* - destruct Γ2; cbn in *; inversion eq; subst. *)
      (*   specialize (IHlq Γ1 Γ2 p eq_refl). *)
      (*   destruct IHlq as [Δ1 [Δ2 [eqv [lq1 lq2]]]]. *)
      (*   exists Δ1; exists Δ2; split; [| split]; [|  | constructor]; assumption. *)
      (* - specialize (IHlq1 Γ1 Γ2 p eq). *)
        
    Lemma Typed_proper' : forall Γ Δ, ctxt_equiv Γ Δ -> forall e τ, Typed Γ e τ -> Typed Δ e τ.
    Proof using.
      intros Γ Δ eqv e τ typ; revert Δ eqv; induction typ; try rename Δ into Γ'; intros Δ eqv;
        try (econstructor; eauto; fail).
      - econstructor; eapply InCtxt_proper'; eauto.
      - econstructor; apply IHtyp; constructor; assumption.
      - econstructor. eapply IHtyp1; eauto. apply IHtyp2; constructor; assumption.
      - econstructor; [eapply IHtyp1 | apply IHtyp2; constructor | apply IHtyp3; constructor]; assumption.
      - constructor; apply IHtyp; constructor; assumption.
      - pose proof (change_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (@change_lock_after_defined Δ m p q pfx) as [E eqE].
        apply @SendTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (change_lock_equiv eqv eq eqE).
      - pose proof (remove_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (remove_lock_after_defined pfx) as [E eqE].
        apply @UpTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (remove_lock_equiv eqv eq eqE).
      - pose proof (add_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (@add_lock_after_defined Δ m p pfx) as [E eqE].
        apply @DownTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (add_lock_equiv eqv eq eqE).
    Qed.

    Theorem Typed_proper : forall Γ Δ, ctxt_equiv Γ Δ -> forall e τ, Typed Γ e τ <-> Typed Δ e τ.
    Proof using.
      intros Γ Δ H0 e τ; split; intro H1; [| symmetry in H0]; eapply Typed_proper'; eassumption.
    Qed.


    (* Lemma ctxt_leq_bound : forall Γ Δ ξ, *)
    (*     ctxt_leq Γ Δ ξ -> *)
    (*     forall n, n < num_vars Γ -> ξ n < num_vars Δ. *)
    
    (* Lemma ctxt_leq_app : forall Γ1 Γ2 Δ1 Δ2 ξ1 ξ2, *)
    (*     ctxt_leq Γ1 Γ2 ξ1 -> *)
    (*     ctxt_leq Δ1 Δ2 ξ2 -> *)
    (*     ctxt_leq (ctxt_app Γ1 Δ1) (ctxt_app Γ2 Δ2) (fun n => if PeanoNat.Nat.ltb n (num_vars Δ1) then ξ2 n else (ξ1 (n - num_vars Δ1) + num_vars Δ2)). *)
    (* Proof using. *)
    (*   intros Γ1 Γ2 Δ1 Δ2 ξ1 ξ2 lq1 lq2; revert Γ1 Γ2 ξ1 lq1; induction lq2; intros E1 E2 ξ4 lq1; *)
    (*     cbn; try (econstructor; eapply IHlq2; eauto; fail). *)
    (*   - eapply ctxt_leq_ext; [| exact lq1]; intro n; rewrite PeanoNat.Nat.sub_0_r; lia. *)
    (*   - eapply VarExtLeq. 2: apply IHlq2; eauto. *)
    (*     intro n; rewrite H0; unfold renup; cbn; destruct n; cbn; [reflexivity|]. *)
    (*     destruct (num_vars Γ). lia. *)
    (*     destruct (PeanoNat.Nat.leb_spec n n0); lia. *)
    (*   - econstructor; [| apply IHlq2; eauto]. *)
    (*     intro n; rewrite H0. destruct (num_vars Γ). *)
    (*     destruct (PeanoNat.Nat.ltb_spec n 0); lia. *)
    (*     cbn. destruct (PeanoNat.Nat.leb_spec n n0); lia. *)
    (*   - econstructor; [| eapply IHlq2; eauto; fail]. *)
    (*     intro n; rewrite H0; cbn. *)
    (*     destruct n; cbn; [reflexivity|]. *)
    (*     destruct n; cbn; [reflexivity|]. *)
    (*     destruct (num_vars Γ); [lia|]. *)
    (*     destruct (PeanoNat.Nat.leb_spec n n0); lia. *)
    (*   - eapply @CtxtLeqTrans with (Δ := ctxt_app E1 Δ). *)
    (*     2: apply IHlq2_1; apply ctxt_leq_refl. *)
    (*     2: apply IHlq2_2; exact lq1. *)
    (*     unfold id_renaming; intro n; cbn; repeat rewrite H0. *)
    (*     destruct (num_vars Δ) eqn:num_Δ; destruct (num_vars Γ) eqn:num_Γ. *)
    (*        -- repeat rewrite PeanoNat.Nat.sub_0_r; rewrite PeanoNat.Nat.add_0_r; reflexivity. *)
    (*        -- apply ctxt_leq_num_vars in lq2_1; lia. *)
    (*        -- repeat rewrite PeanoNat.Nat.sub_0_r. rewrite PeanoNat.Nat.add_sub. *)
    (*           destruct (PeanoNat.Nat.leb_spec (n + S n0) n0); lia. *)
    (*        -- destruct (PeanoNat.Nat.leb_spec n n1). *)
    (*     destruct (num_vars Γ) eqn:num_Γ. *)
    (*     -- destruct (num_vars Δ) eqn:num_Δ. *)
    (*        --- repeat rewrite PeanoNat.Nat.sub_0_r. unfold id_renaming. *)
    (*            rewrite PeanoNat.Nat.add_0_r. reflexivity. *)
    (*        --- unfold id_renaming. repeat rewrite PeanoNat.Nat.sub_0_r. *)
    (*            destruct (PeanoNat.Nat.leb_spec (n + S n0) n0). lia. *)
    (*            rewrite <- plus_n_Sm; cbn. rewrite PeanoNat.Nat.add_sub. reflexivity. *)
    (*     -- destruct (PeanoNat.Nat.leb_spec n n0); destruct (num_vars Δ) eqn:num_Δ. *)
    (*        --- apply ctxt_leq_num_vars in lq2_1; lia. *)
    (*        --- destruct (PeanoNat.Nat.leb_spec (ξ1 n) n1).  reflexivity. *)
    (*            apply ctxt_leq_num_vars in lq2_1; *)
    (*              apply ctxt_leq_num_vars in lq2_2. *)
    (*            rewrite num_Γ in lq2_1. *)
    (*            rewrite num_Δ in lq2_1. inversion lq2_1; subst. *)

    Lemma InCtxt_leq' : forall {Γ Δ : Ctxt} (lq : ctxt_leq' Γ Δ),
      forall n m1 τ m2, InCtxt n m1 τ m2 Γ -> InCtxt (renaming_of_ctxt_leq' lq n) m1 τ m2 Δ.
    Proof using.
      intros Γ Δ lq; induction lq; intros n m1' τ' m2' i; cbn; unfold id_renaming; cbn;
        eauto with ctxts; try (inversion i; subst; constructor; auto; fail).
      - destruct n as [| n]; [| destruct n]; cbn;
          inversion i; subst.
        do 2 constructor.
        inversion i0; subst. constructor.
        inversion i0; subst. do 2 constructor; assumption.
      - inversion i; subst.
        inversion i0; subst.
        rewrite mod_app_assoc; constructor; exact i1.
      - inversion i; subst.
        rewrite <- mod_app_assoc; do 2 constructor; exact i0.
      - rewrite <- (mod_app_base m2'); constructor; exact i.
      - inversion i; subst. rewrite mod_app_base; exact i0.
    Qed.

    Lemma InCtxt_leq'' : forall {Γ Δ : Ctxt} {ξ : renaming} (lq : ctxt_leq'' Γ ξ Δ),
      forall n m1 τ m2, InCtxt n m1 τ m2 Γ -> InCtxt (ξ n) m1 τ m2 Δ.
    Proof using.
      intros Γ Δ ξ lq; induction lq; try rename τ into τ'; try rename m1 into m1'; try rename m2 into m2'; intros n m1 τ m2 i; cbn; try rewrite H0; try (inversion i; subst; constructor; auto; fail).
      - inversion i; subst. rewrite H0; repeat (constructor; auto).
        inversion i0; subst. rewrite H1; constructor; auto.
        rewrite H2; repeat constructor; auto.
      - inversion i; subst.
        inversion i0; subst.
        rewrite mod_app_assoc. constructor; auto.
      - inversion i; subst.
        rewrite <- mod_app_assoc. repeat constructor; auto.
      - assert (m2 = mod_app m2 base) as H1 by reflexivity.
        rewrite H1; constructor; auto.
      - assert (m2 = mod_app m2 base) as H1 by reflexivity.
        rewrite H1 in i. inversion i; subst.
        cbn in *; subst. assumption.
      - apply IHlq1 in i. apply IHlq2 in i. exact i.
    Qed.

    Record ctxt_leq_append_left_ret (Γ1 Γ2 Δ : Ctxt) : Type :=
      {
        fst_ctxt : Ctxt;
        snd_ctxt : Ctxt;
        app_eq : ctxt_equiv Δ (ctxt_app fst_ctxt snd_ctxt);
        ctxt_leq'1 : ctxt_leq' Γ1 fst_ctxt;
        ctxt_leq'2 : ctxt_leq' Γ2 snd_ctxt
      }.

    Record ctxt_leq_append_left_ret_strong (Γ1 Γ2 Δ : Ctxt) : Type :=
      {
        fst_ctxt' : Ctxt;
        snd_ctxt' : Ctxt;
        app_eq' : ctxt_equiv Δ (ctxt_app fst_ctxt' snd_ctxt');
        ctxt_leq'1' : ctxt_leq' Γ1 fst_ctxt';
        ctxt_leq'2' : ctxt_leq' Γ2 snd_ctxt';
        nv : NonVar fst_ctxt'
      }.




    Lemma emptoid_leq'1 : forall Γ,
        Emptoid Γ ->
        ctxt_leq' Γ EmptyCtxt.
    Proof using.
      intro Γ; induction Γ; intro etd.
      - constructor.
      - exfalso; inversion etd.
      - assert (m = base)
          by (inversion etd; subst; reflexivity); subst.
        apply @CtxtLeq'Trans with (Δ := Γ).
        apply LockNothingLeq2'. apply IHΓ. inversion etd; subst; assumption.
    Qed.

    Lemma emptoid_leq'1_inv_general : forall Γ Δ,
        ctxt_leq' Γ Δ ->
        Emptoid Δ ->
        Emptoid Γ.
    Proof using.
      intros Γ Δ lq; induction lq; intro etd; try (constructor; auto; fail);
         try (exfalso; inversion etd; fail).
      - assert (m = base)
          by (inversion etd; subst; reflexivity); subst.
        inversion etd; subst. constructor. apply IHlq; assumption.
      - inversion etd; subst.
        symmetry in H2; apply mod_app_base_inv in H2; destruct H2; subst; cbn in *.
        do 2 constructor; assumption.
      - inversion etd; subst.
        inversion emptd; subst.
        cbn; constructor; assumption.
      - inversion etd; assumption.
      - apply IHlq1; apply IHlq2; assumption.
    Qed.

    Corollary emptoid_leq'1_inv  : forall Γ, ctxt_leq' Γ EmptyCtxt -> Emptoid Γ.
    Proof using.
      intros Γ X; apply emptoid_leq'1_inv_general in X; [assumption | constructor].
    Qed.

    Lemma emptoid_leq'2 : forall Γ,
        Emptoid Γ ->
        ctxt_leq' EmptyCtxt Γ.
    Proof using.
      intro Γ; induction Γ; intro etd.
      - constructor.
      - exfalso; inversion etd.
      - assert (m = base)
          by (inversion etd; subst; reflexivity); subst.
        apply @CtxtLeq'Trans with (Δ := Γ).
        apply IHΓ. inversion etd; subst; assumption.
        apply LockNothingLeq1'. 
    Qed.

    Corollary emptoid_leq' : forall Γ Δ,
        Emptoid Γ ->
        Emptoid Δ ->
        ctxt_leq' Γ Δ.
    Proof using.
      intros Γ Δ H0 H1.
      apply @CtxtLeq'Trans with (Δ := EmptyCtxt).
      apply emptoid_leq'1; assumption.
      apply emptoid_leq'2; assumption.
    Qed.

    Lemma emptoid_nonvar : forall Γ, Emptoid Γ -> NonVar Γ.
    Proof using.
      intro Γ; induction Γ; intro etd. constructor. exfalso; inversion etd.
      assert (m = base) by (inversion etd; subst; auto). subst.
      apply BaseLockNonVar. apply IHΓ. inversion etd; subst; auto.
    Qed.

    Fixpoint varext_snoc (m : mod) (τ : type) (Γ : Ctxt) : Ctxt :=
      match Γ with
      | EmptyCtxt => VarExt EmptyCtxt m τ
      | VarExt Γ m' τ' => VarExt (varext_snoc m τ Γ) m' τ'
      | LockExt Γ m' => LockExt (varext_snoc m τ Γ) m'
      end.

    Lemma varext_snoc_app : forall Γ Δ m τ,
        ctxt_app Γ (varext_snoc m τ Δ) = ctxt_app (VarExt Γ m τ) Δ.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ m' τ'; cbn;
        [reflexivity| |]; f_equal; apply IHΔ.
    Qed.

    Lemma skip_varext_snoc_leq'' : forall Γ m τ,
        ctxt_leq' Γ (varext_snoc m τ Γ).
    Proof using.
      intro Γ; induction Γ; intros m' τ'; cbn;
        try (econstructor; eauto; fail).
      apply VarAddLeq'; constructor.
    Qed.

    Lemma skip_varext_snoc_leq' : forall Γ Δ m τ,
        ctxt_leq' Γ Δ ->
        ctxt_leq' Γ (varext_snoc m τ Δ).
    Proof using.
      intros Γ Δ m τ lq; revert m τ; induction lq; intros m' τ'; cbn;
         try (econstructor; eauto; fail).
      - apply VarAddLeq'; econstructor.
      - eapply CtxtLeq'Trans. apply VarSwapLeq'.
        do 2 apply VarExtLeq'. apply skip_varext_snoc_leq''.
      - eapply CtxtLeq'Trans. apply LockCollapseLeq'.
        econstructor. apply skip_varext_snoc_leq''.
      - eapply CtxtLeq'Trans. apply LockSplitLeq'.
        do 2 apply LockExtLeq'. apply skip_varext_snoc_leq''.
      - eapply CtxtLeq'Trans. apply LockNothingLeq1'.
        apply LockExtLeq'. apply skip_varext_snoc_leq''.
      - eapply CtxtLeq'Trans. apply LockNothingLeq2'.
        apply skip_varext_snoc_leq''.
    Qed.


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
        

    (* Corollary ctxt_equiv_varoid' : forall Γ Δ E m τ, *)
    (*     Varoid Γ m τ Δ -> *)
    (*     ctxt_equiv E Δ ->  *)
    (*     Varoid Γ m τ E. *)
    (* Proof using. *)
    (*   intros Γ Δ E m τ H0 H1. *)
    (*   symmetry in H1. eapply ctxt_equiv_varoid; eauto. *)
    (* Qed. *)

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

    Theorem varoid_ctxt_leq' : forall Γ Γ' Δ E m τ,
        Varoid Γ m τ Δ ->
        Varoid Γ' m τ E ->
        ctxt_leq' Γ Γ' ->
        ctxt_leq' Δ E.
    Proof using.
      intros Γ Γ' Δ; revert Γ Γ'; induction Δ; intros Γ Γ' E m' τ' vdΔ vdE lq;
        try (exfalso; inversion vdΔ; fail).
      - assert (m = m' /\ t = τ' /\ Δ = Γ) as H0
            by (inversion vdΔ; subst; split;
                [reflexivity | split; reflexivity]);
          destruct H0 as [H1 [H2 H0]]; subst.
        induction E.
        -- exfalso; inversion vdE.
        -- assert (m = m' /\ t = τ' /\ E = Γ') as H1
               by (inversion vdE; subst; split;
                   [reflexivity | split; reflexivity]);
             destruct H1 as [H2 [H3 H1]]; subst.
           apply VarExtLeq'; assumption.
        -- assert (m = base /\ Varoid Γ' m' τ' E) as H0
               by (inversion vdE; subst; split; [reflexivity | assumption]);
             destruct H0 as [H1 H0]; subst.
           apply @CtxtLeq'Trans with (Δ := E); [|apply LockNothingLeq1'].
           apply IHE; assumption.
      - assert (m = base /\ Varoid Γ m' τ' Δ) as H0
            by (inversion vdΔ; subst; split; [reflexivity | assumption]);
          destruct H0 as [H1 H0]; subst.
        apply @CtxtLeq'Trans with (Δ := Δ); [ apply LockNothingLeq2' |].
        eapply IHΔ; eauto.
    Qed.

    Inductive multivaroid : Ctxt -> (list (mod * type)) -> Ctxt -> Prop :=
    | EmptyMultivaroid (Γ : Ctxt) : multivaroid Γ nil Γ
    | VarMultivaroid (Γ Δ : Ctxt) (m : mod) (τ : type) (l1 l2 : list (mod * type)) (mvd : multivaroid Γ l1 Δ) (perm : Permutation l1 (List.cons (m, τ) l2)) : multivaroid Γ l2 (VarExt Δ m τ)
    | LockMultivaroid (Γ Δ : Ctxt) (l : list (mod * type)) (mvd : multivaroid Γ l Δ)
      : multivaroid Γ l (LockExt Δ base).

    (* Inductive ctxt_leq'_varoid_ret (Γ Δ : Ctxt) (m : mod) (τ : type) : Type := *)
    (* | LeftVaroid (Γ' : Ctxt) (vd : Varoid Γ' m τ Γ) (lq : ctxt_leq' Γ' Δ) : ctxt_leq'_varoid_ret Γ Δ m τ *)
    (* | AddInv (lq : ctxt_leq' Γ Δ) : ctxt_leq'_varoid_ret Γ Δ m τ. *)

    (* Lemma ctxt_leq'_varoid : forall Γ Δ1 Δ2 m τ, *)
    (*     Varoid Δ1 m τ Δ2 -> *)
    (*     ctxt_leq' Γ Δ2 -> *)
    (*     ctxt_leq'_varoid_ret Γ Δ1 m τ. *)
    (* Proof using. *)
    (*   intros Γ Δ E m τ vd lq; revert Δ m τ vd; induction lq; *)
    (*     intros Δ' m' τ' vd; try (exfalso; inversion vd; fail). *)
    (*   - assert (m = m') by (inversion vd; auto); subst. *)
    (*     assert (τ = τ') by (inversion vd; auto); subst. *)
    (*     assert (Δ = Δ') by (inversion vd; auto); subst. *)
    (*     apply LeftVaroid with (Γ' := Γ). constructor. assumption. *)
    (*   - assert (m = base) by (inversion vd; reflexivity); subst. *)
    (*     assert (Varoid Δ' m' τ' Δ) by (inversion vd; subst; auto). *)
    (*     destruct (IHlq Δ' m' τ' H0). *)
    (*     apply LeftVaroid with (Γ' := Γ'); [constructor; assumption | assumption]. *)
    (*     apply AddInv; eapply CtxtLeq'Trans; [apply LockNothingLeq2' | assumption]. *)
    (*   - assert (m = m') by (inversion vd; auto); subst. *)
    (*     assert (τ = τ') by (inversion vd; auto); subst. *)
    (*     assert (Δ = Δ') by (inversion vd; auto); subst. *)
    (*     apply AddInv; assumption. *)
    (*   - assert (m1 = m') by (inversion vd; auto); subst. *)
    (*     assert (τ1 = τ') by (inversion vd; auto); subst. *)
    (*     assert (Δ' = VarExt Γ m2 τ2) by (inversion vd; auto); subst. *)
        
    
    
    (* Lemma ctxt_leq_append_left_ret_to_strong : forall {Γ1 Γ2 Δ : Ctxt}, *)
    (*     NonVar Γ1 -> *)
    (*     ctxt_leq_append_left_ret Γ1 Γ2 Δ -> ctxt_leq_append_left_ret_strong Γ1 Γ2 Δ. *)
    (* Proof using. *)
    (*   intros Γ1 Γ2 Δ nv r; destruct r; destruct fst_ctxt0. *)
    (*   - apply emptoid_leq'1_inv in ctxt_leq'3. *)
    (*     rewrite ctxt_app_identity_left in app_eq0. *)
    (*     econstructor. 2: apply emptoid_leq'1; assumption. *)
    (*     rewrite ctxt_app_identity_left. exact app_eq0. apply ctxt_leq'4. constructor. *)
    (*   - econstructor. *)
    (*     3: apply skip_varext_snoc_leq' with (m := m) (τ := t) (Δ := snd_ctxt0); assumption. *)
        
        


    Theorem ctxt_leq'_proper' : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt},
        ctxt_leq' Γ1 Δ1 ->
        ctxt_equiv Γ1 Γ2 ->
        ctxt_equiv Δ1 Δ2 ->
        exists _: ctxt_leq' Γ2 Δ2, True.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 lq eqv1 eqv2.
      symmetry in eqv1; destruct (ctxt_equiv_leq' eqv1) as [lq1 _].
      destruct (ctxt_equiv_leq' eqv2) as [lq2 _].
      unshelve eexists; [| trivial].
      apply @CtxtLeq'Trans with (Δ := Γ1); [assumption|].
      apply @CtxtLeq'Trans with (Δ := Δ1); assumption.
    Qed.

    (* Axiomatized in order to get around Rocq's Prop restrictions.
       As you can see above, it's sound. *)      
    Axiom ctxt_leq'_proper  : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt},
        ctxt_leq' Γ1 Δ1 ->
        ctxt_equiv Γ1 Γ2 ->
        ctxt_equiv Δ1 Δ2 ->
        ctxt_leq' Γ2 Δ2.

    Lemma ctxt_leq_append_left : forall {Γ Δ : Ctxt},
        ctxt_leq' Γ Δ ->
        forall Γ1 Γ2,
          NonVar Γ1 ->
          ctxt_equiv Γ (ctxt_app Γ1 Γ2) ->
          ctxt_leq_append_left_ret Γ1 Γ2 Δ.
    Proof using.
      intros Γ Δ lq; induction lq; intros Γ1 Γ2 nv eqv.
      - induction Γ2; cbn in *.
        -- econstructor. 2: apply ctxt_leq'_refl. 2: apply EmptyCtxtLeq'.
           cbn; assumption. 
        -- apply Emptoid_from_Equiv in eqv; [| constructor].
           exfalso; inversion eqv.
        -- assert (Emptoid (ctxt_app Γ1 Γ2)) as etd
               by (apply Emptoid_from_Equiv in eqv; [| constructor];
                   inversion eqv; assumption).
           specialize (IHΓ2 (emptoid_equiv etd)).
           assert (m = base)
             by (apply Emptoid_from_Equiv in eqv; [| constructor];
                 inversion eqv; reflexivity); subst.
           destruct IHΓ2. econstructor.
           2: apply ctxt_leq'_refl.
           2: apply LockNothingLeq2'.
           apply emptoid_equiv; assumption.
      - pose proof (ctxt_equiv_varoid (VarVaroid Γ m τ) eqv).
        induction Γ2; cbn in *.
        -- econstructor. 3: econstructor.
           cbn. reflexivity.
           apply @ctxt_leq'_proper with (Γ1 := VarExt Γ m τ) (Δ1 := VarExt Δ m τ);
             [| assumption | reflexivity ].
           apply VarExtLeq'; assumption.
        -- assert (m0 = m /\ t = τ) as H1 by
           (destruct (ctxt_equiv_varoid (VarVaroid Γ m τ) eqv) as [Γ' [vd eqv']];
            inversion vd; split; reflexivity); destruct H1; subst.
           pose proof (ctxt_equiv_varoid (VarVaroid Γ m τ) eqv).
           assert (ctxt_equiv Γ (ctxt_app Γ1 Γ2)) as eqv'
               by (destruct H0 as [Γ' [vd eqv']];
                   inversion vd; subst; exact eqv').
           specialize (IHlq Γ1 Γ2 nv eqv').
           destruct IHlq.
           econstructor.
           2: exact ctxt_leq'3.
           2: eapply VarExtLeq'; exact ctxt_leq'4.
           cbn. apply VarExtEquiv. assumption.
        -- assert (m0 = base) by 
             (destruct (ctxt_equiv_varoid (VarVaroid Γ m τ) eqv) as [Γ' [vrd eqv']];
              inversion vrd; subst; reflexivity); subst.
           assert (ctxt_equiv (VarExt Γ m τ) (ctxt_app Γ1 Γ2))
             by (apply LockNothingEquiv1_inv; assumption).
           specialize (IHΓ2 H1).
           assert (exists Γ', Varoid Γ' m τ (ctxt_app Γ1 Γ2) /\ ctxt_equiv Γ Γ')
             by (destruct H0 as [Γ' [vd eqv']];
                 exists Γ'; split; [| assumption]; inversion vd; subst; assumption).
           specialize (IHΓ2 H2).
           destruct IHΓ2.
           econstructor; try eassumption. apply @CtxtLeq'Trans with (Δ := Γ2).
           apply LockNothingLeq2'. assumption.
      - induction Γ2; cbn in *.
        -- econstructor. 3: econstructor.
           cbn; reflexivity.
           eapply ctxt_leq'_proper; [|exact eqv| reflexivity].
           apply LockExtLeq'; exact lq.
        -- 
           
    Admitted.



    Lemma ctxt_leq'_append' : forall {Γ1 Γ2 Δ : Ctxt} (lq : ctxt_leq' Γ1 Γ2),
        ctxt_leq' (ctxt_app Γ1 Δ) (ctxt_app Γ2 Δ).
    Proof using.
      intros Γ1 Γ2 Δ; revert Γ1 Γ2; induction Δ; intros Γ1 Γ2 lq; cbn; auto;
        try (econstructor; eauto; fail).
    Qed.      

    Theorem ctxt_leq'_append : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} (lq1 : ctxt_leq' Γ1 Δ1)
                                 (lq2 : ctxt_leq' Γ2 Δ2),
        ctxt_leq' (ctxt_app Γ1 Γ2) (ctxt_app Δ1 Δ2).
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 lq1 lq2; revert Γ1 Δ1 lq1; induction lq2; intros Γ1 Δ1 lq1;
        cbn; auto; try (econstructor; eauto; fail).
      - eapply CtxtLeq'Trans. apply VarSwapLeq'.
        exact (@ctxt_leq'_append' Γ1 Δ1 (VarExt (VarExt Γ m2 τ2) m1 τ1) lq1).
      - eapply CtxtLeq'Trans; [apply LockCollapseLeq'|].
        apply LockExtLeq'; apply ctxt_leq'_append'; assumption.
      - eapply CtxtLeq'Trans; [apply LockSplitLeq'|].
        apply LockExtLeq'; apply LockExtLeq'; apply ctxt_leq'_append'; assumption.
      - eapply CtxtLeq'Trans; [apply LockNothingLeq1'|].
        apply LockExtLeq'; apply ctxt_leq'_append'; assumption.
      - eapply CtxtLeq'Trans; [apply LockNothingLeq2'|].
        apply ctxt_leq'_append'; assumption.
      - eapply CtxtLeq'Trans. apply IHlq2_1; eassumption.
        apply IHlq2_2. apply ctxt_leq'_refl.
    Qed.                    


    Theorem weakening : forall {Γ Δ : Ctxt} {ξ : renaming} (lq : ctxt_leq'' Γ ξ Δ)
                          (e : expr) (τ : type),
        Typed Γ e τ ->
        Typed Δ (ren e ξ) τ.
    Proof using.
      intros Γ Δ ξ lq e τ typ; revert Δ ξ lq; induction typ; intros E ξ lq; cbn;
        try (econstructor; eauto; fail).
      - econstructor; apply (InCtxt_leq'' lq); exact i.
      - constructor. specialize (IHtyp (LockExt E p) ξ (LockExtLeq'' p lq)).
        cbn in IHtyp. assumption.
      - econstructor. apply IHtyp1; auto.
        specialize (IHtyp2 (VarExt E p τ) (renup ξ) (VarExtLeq'' p τ (fun n => eq_refl) lq)).
        cbn in IHtyp2. assumption.
      - econstructor. apply IHtyp1; assumption.
        specialize (IHtyp2 (VarExt E base τ1) (renup ξ) (VarExtLeq'' base τ1 (fun n => eq_refl) lq));
          cbn in IHtyp2; assumption.
        specialize (IHtyp3 (VarExt E base τ2) (renup ξ) (VarExtLeq'' base τ2 (fun n => eq_refl) lq));
          cbn in IHtyp3; assumption.
      - constructor;
          specialize (IHtyp (VarExt E base τ1) (renup ξ) (VarExtLeq'' base τ1 (fun n => eq_refl) lq));
          cbn in IHtyp; assumption.
      - pose proof (change_lock_after_prefix eq).
        rewrite (ctxt_leq''_all_locks lq) in H0.
        destruct (@change_lock_after_defined E m p q H0) as [Δ' eq'].
        apply @SendTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq''_change_lock_after lq eq eq').
        apply IHtyp; auto.
      - pose proof (remove_lock_after_prefix eq).
        rewrite (ctxt_leq''_all_locks lq) in H0.
        destruct (remove_lock_after_defined H0) as [Δ' eq'].
        apply @UpTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq''_remove_lock_after lq eq eq').
        apply IHtyp; auto.
      - pose proof (add_lock_after_prefix eq).
        rewrite (ctxt_leq''_all_locks lq) in H0.
        destruct (@add_lock_after_defined E m p H0) as [Δ' eq'].
        apply @DownTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq''_add_lock_after lq eq eq').
        apply IHtyp; auto.
    Qed.
        
  End TypeSystem.

  (* Section Substitution. *)

  (*   Definition TypedSubst (Γ : Ctxt) (σ : substitution) (Δ : Ctxt) := *)
  (*     all_locks Γ = all_locks Δ /\ *)
  (*     forall x m, *)
  (*       mod_app m (locks Γ x) = fst (vars Γ x) ->  *)
  (*       Typed (add_lock Δ m) (σ x) (snd (vars Γ x)). *)

  (*   Lemma id_subst_typed: forall Γ, TypedSubst Γ (fun x => var x) Γ. *)
  (*   Proof using. *)
  (*     intros Γ; split; [reflexivity | intros x m eq]. *)
  (*     apply VarTyping with (m := fst (vars Γ x)); cbn; auto. *)
  (*     apply surjective_pairing. *)
  (*   Qed.       *)

  (*   Lemma substup_typed : forall Γ Δ σ g τ, *)
  (*       TypedSubst Γ σ Δ -> TypedSubst (add_var Γ g τ) (substup σ) (add_var Δ g τ). *)
  (*   Proof using. *)
  (*     intros Γ Δ σ g τ [al_eqv typd]; split; [exact al_eqv|]; intros x m eq. *)
  (*     destruct x; cbn in *; subst. *)
  (*     - apply VarTyping with (m := g); cbn; reflexivity. *)
  (*     - eapply weakening with (Δ := add_lock Δ m). *)
  (*       split; [|split]; try (intro y); cbn; auto. *)
  (*       apply typd; auto. *)
  (*       Unshelve. *)
  (*       intros n m0 H0; cbn; apply mod_app_mono_l; apply locks_mono; auto. *)
  (*   Qed. *)

  (*   Theorem subst_typed : forall Γ Δ e σ τ, Typed Γ e τ -> TypedSubst Γ σ Δ -> Typed Δ (subst e σ) τ. *)
  (*   Proof using. *)
  (*     intros Γ Δ e σ τ typed; revert Δ σ; induction typed; try (rename σ into τ'); *)
  (*       intros Γ'' σ typeds; cbn; *)
  (*       try (econstructor; eauto; *)
  (*            repeat lazymatch goal with *)
  (*              | [ H : ?P |- ?P ] => exact H *)
  (*              | [ IH : forall Δ σ, TypedSubst ?Γ σ Δ -> Typed Δ (subst ?e σ) ?τ, H : TypedSubst ?Γ ?σ ?Δ |- Typed ?Δ (subst ?e ?σ) ?τ ] => *)
  (*                  exact (IH Δ σ H) *)
  (*              | [H : TypedSubst ?Γ ?σ ?Δ |- context[add_var ?Δ ?p ?τ] ] => *)
  (*                  lazymatch goal with *)
  (*                  | [ _ : TypedSubst (add_var Γ p τ) (substup σ) (add_var Δ p τ) |- _ ] => fail *)
  (*                  | _ =>  *)
  (*                      assert (TypedSubst (add_var Γ p τ) (substup σ) (add_var Δ p τ)) by (exact (substup_typed Γ Δ σ p τ H)) *)
  (*                  end *)
  (*              | [ H : TypedSubst ?Γ ?σ ?Δ |- context[all_locks ?Δ]] => *)
  (*                  lazymatch goal with *)
  (*                  | [_ : all_locks Γ = all_locks Δ |- _ ] => fail *)
  (*                  | _ => let eq := fresh "eq" in assert (all_locks Γ = all_locks Δ) as eq by (destruct H as [al_eqv _]; exact al_eqv); *)
  (*                                               rewrite <- eq *)
  (*                  end *)
  (*         end; fail). *)
  (*     - destruct typeds as [al_eqv typeds]. *)
  (*       specialize (typeds n base); cbn in typeds. *)
  (*       rewrite pf1 in typeds; cbn in typeds. *)
  (*       rewrite mod_base_app in typeds; specialize (typeds pf2). *)
  (*       apply type_ext with (Γ := add_lock Γ'' base); [exact typeds | symmetry; apply add_base_lock]. *)
  (*     - apply AtTyping; apply IHtyped. *)
  (*       destruct typeds as [al_eqv typeds]; split; [cbn; rewrite al_eqv; reflexivity|]. *)
  (*       intros x m; cbn; intro eq. *)
  (*       apply type_ext with (Γ := add_lock Γ'' (mod_app m p)); [|apply add_two_locks]. *)
  (*       rewrite <- mod_app_assoc in eq. *)
  (*       apply typeds; exact eq. *)
  (*   Qed.                                              *)

  (* End Substitution. *)
  
End CorpsTypes.

