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

    Fixpoint lock_location (Γ : Ctxt) (m : mod) : option nat :=
      match Γ with
      | EmptyCtxt =>
          match m with
          | Modalities.base => Some 0
          | _ => None
          end
      | VarExt Γ _ _ =>
          match lock_location Γ m with
          | Some n => Some (S n)
          | None => None
          end
      | LockExt Γ m' =>
          let m'' := all_locks Γ in
          if prefixb m m''
          then lock_location Γ m
          else if prefixb m (mod_app m'' m')
               then Some 0
               else None
      end.

    Lemma lock_location_Some : forall {Γ : Ctxt} {m : mod},
        PrefixOf m (all_locks Γ) ->
        exists n, lock_location Γ m = Some n.
    Proof using.
      intros Γ; induction Γ; intros m' pfx; cbn in *.
      - apply PrefixOf_base in pfx; subst; exists 0; reflexivity.
      - destruct (IHΓ m' pfx) as [m'' eq_m'']; rewrite eq_m''.
        exists (S m''); reflexivity.
      - destruct (prefixb m' (all_locks Γ)) eqn:pfx_eq.
        -- apply IHΓ; apply prefixb_PrefixOf; assumption.
        -- rewrite (PrefixOf_prefixb pfx). exists 0; reflexivity.
    Qed.

    Lemma lock_location_prefix : forall {Γ : Ctxt} {m : mod} {n : nat},
        lock_location Γ m = Some n ->
        PrefixOf m (all_locks Γ).
    Proof using.
      intros Γ; induction Γ; intros m' n eq; cbn in *.
      - destruct m'; inversion eq; subst; clear eq; reflexivity.
      - destruct (lock_location Γ m') eqn:eq'; inversion eq; subst; clear eq.
        eapply IHΓ; eauto.
      - destruct (prefixb m' (all_locks Γ)) eqn:pfx_eq.
        apply prefixb_PrefixOf in pfx_eq;
          transitivity (all_locks Γ); [assumption | apply PrefixOf_app].
        destruct (prefixb m' (mod_app (all_locks Γ) m)) eqn:pfx_eq';
          inversion eq; subst; clear eq.
        apply prefixb_PrefixOf; assumption.
    Qed.        

    Corollary lock_location_None : forall {Γ : Ctxt} {m : mod},
        ~ PrefixOf m (all_locks Γ) ->
        lock_location Γ m = None.
    Proof using.
      intros Γ m H0; destruct (lock_location Γ m) eqn:eq; [| reflexivity].
      apply lock_location_prefix in eq; destruct (H0 eq).
    Qed.

    Corollary lock_location_not_prefix : forall {Γ : Ctxt} {m : mod},
        lock_location Γ m = None ->
        ~ PrefixOf m (all_locks Γ).
    Proof using.
      intros Γ m H0. destruct (prefixb m (all_locks Γ)) eqn:eq.
      2: { apply prefixb_not_PrefixOf in eq; assumption. }
      apply prefixb_PrefixOf in eq; destruct (lock_location_Some eq) as [m' eqm'].
      rewrite eqm' in H0; inversion H0.
    Qed.

    Lemma BaseLockLocation : forall {Γ : Ctxt},
        lock_location Γ base = Some (num_vars Γ).
    Proof using.
      intro Γ; induction Γ; cbn; try rewrite IHΓ; try reflexivity.
      rewrite (PrefixOf_prefixb (base_Prefix (all_locks Γ))).
      reflexivity.
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

    Lemma InCtxt_lt : forall {Γ : Ctxt} {n : nat} {m1 m2 : mod} {τ : type},
        InCtxt n m1 τ m2 Γ ->
        n < num_vars Γ.
    Proof using.
      intros Γ n m1 m2 τ i; induction i; cbn; lia.
    Qed.
    
  End InContext.

  Section ContextEquivalence.

    Inductive ctxt_equiv : Ctxt -> Ctxt -> Prop :=
    | EmptyCtxtEquiv : ctxt_equiv EmptyCtxt EmptyCtxt
    | VarExtEquiv: forall {Γ Δ : Ctxt} (m : mod) (τ : type), ctxt_equiv Γ Δ -> ctxt_equiv (VarExt Γ m τ) (VarExt Δ m τ)
    | LockExtEquiv : forall {Γ Δ : Ctxt} (m : mod), ctxt_equiv Γ Δ -> ctxt_equiv (LockExt Γ m) (LockExt Δ m)
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

    Lemma lock_location_proper : forall {Γ Δ} m, ctxt_equiv Γ Δ -> lock_location Γ m = lock_location Δ m.
    Proof using.
      intros Γ Δ m eqv; revert m; induction eqv; intro m'; cbn;
      repeat match goal with
        | [ |- ?a = ?a ] => reflexivity
        | [ H : ?P |- ?P ] => exact P
        | [ H1 : ?P, H2 : ~ ?P |- _ ] => destruct (H2 H1)
             (* | [ |- context[lock_location ?Γ ?m]] => *)
             (*     lazymatch goal with *)
             (*     | [ |- lock_location Γ m = _ ] => fail *)
             (*     | [ |- _ = lock_location Γ m ] => fail *)
             (*     | [ H : lock_location Γ m = _ |- _ ] => rewrite H *)
             (*     | _ => let eq := fresh "eq" in destruct (lock_location Γ m) eqn:eq *)
                                 (*     end *)
        | [ H : context[mod_app ?m1 (mod_app ?m2 ?m3)] |- _ ] =>
            rewrite <- mod_app_assoc in H
        | [ H1 : PrefixOf ?m1 ?m2, H2 : context[mod_app ?m2 ?m3] |- _ ] =>
            lazymatch goal with
            | [_ : PrefixOf m1 (mod_app m2 m3) |- _ ] => fail
            | _ => assert (PrefixOf m1 (mod_app m2 m3))
                by (transitivity m2; [exact H1 | apply PrefixOf_app ])
            end
        | [ H1 : PrefixOf ?m1 ?m2 |- context[mod_app ?m2 ?m3]] =>
            lazymatch goal with
            | [_ : PrefixOf m1 (mod_app m2 m3) |- _ ] => fail
            | _ => assert (PrefixOf m1 (mod_app m2 m3))
                by (transitivity m2; [exact H1 | apply PrefixOf_app ])
            end
        | [ H : ctxt_equiv ?Γ ?Δ |- context[all_locks ?Γ]] =>
            rewrite (all_locks_proper H)
        | [ IH : forall m, lock_location ?Γ m = lock_location Δ m |- context[lock_location ?Γ ?m]] => rewrite (IH m)
        | [ |- context[prefixb ?m1 ?m2]] =>
            lazymatch goal with
            | [H : prefixb m1 m2 = _ |- _ ] => rewrite H
            | [H : PrefixOf m1 m2 |- _ ] => rewrite (PrefixOf_prefixb H)
            | [H : ~ PrefixOf m1 m2 |- _ ] => rewrite (not_PrefixOf_prefixb H)
            | _ => let eq := fresh "eq" in
                  destruct (prefixb m1 m2) eqn:eq;
                  [pose proof (prefixb_PrefixOf eq) | pose proof (prefixb_not_PrefixOf eq)]
            end 
        end.
      2: symmetry.
      1,2: apply lock_location_None; assumption.
      transitivity (lock_location Δ m'); auto.
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

    Lemma EmptoidLockLocation : forall {Γ : Ctxt} {m : mod} {i : nat},
        Emptoid Γ ->
        lock_location Γ m = Some i ->
        m = base /\ i = 0.
    Proof using.
      intros Γ m i eqv; revert m i; induction eqv; intros m' i eqi; cbn in *.
      - destruct m'; inversion eqi; subst; auto.
      - destruct (prefixb m' (all_locks Γ)) eqn:pfx; [| inversion eqi].
        apply IHeqv; auto.
    Qed.

    Lemma emptoid_all_locks : forall {Γ : Ctxt},
        Emptoid Γ ->
        all_locks Γ = base.
    Proof using.
      intros Γ etd; induction etd; cbn. reflexivity. apply IHetd.
    Qed.

    Lemma emptoid_num_vars : forall {Γ : Ctxt},
        Emptoid Γ ->
        num_vars Γ = 0.
    Proof using.
      intros Γ etd; induction etd; cbn; auto.
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
    | EmptyCtxtLeq {ξ : renaming} :
      (forall n, ξ n = n) -> 
      ctxt_leq EmptyCtxt ξ EmptyCtxt
    | VarExtLeq : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
        (forall n, ξ2 n = renup ξ1 n) -> 
        ctxt_leq Γ ξ1 Δ ->
        ctxt_leq (VarExt Γ m τ) ξ2 (VarExt Δ m τ)
    | LockExtLeq : forall {Γ Δ : Ctxt} {ξ : renaming} (m : mod),
        ctxt_leq Γ ξ Δ ->
        ctxt_leq (LockExt Γ m) ξ (LockExt Δ m)
    | VarAddLeq : forall {Γ Δ : Ctxt} {ξ1 ξ2 : renaming} (m : mod) (τ : type),
        ctxt_leq Γ ξ1 Δ ->
        (forall n, ξ2 n = S (ξ1 n)) ->
        ctxt_leq Γ ξ2 (VarExt Δ m τ)
    | VarSwapLeq : forall (Γ : Ctxt) (m1 m2 : mod) (τ1 τ2 : type) (ξ : renaming),
        (ξ 0 = 1) ->
        (ξ 1 = 0) ->
        (forall n, ξ (S (S n)) = S (S n)) ->
        ctxt_leq (VarExt (VarExt Γ m1 τ1) m2 τ2) ξ (VarExt (VarExt Γ m2 τ2) m1 τ1)
    | LockCollapseLeq : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt (LockExt Γ m1) m2) ξ (LockExt Γ (mod_app m1 m2))
    | LockSplitLeq : forall (Γ : Ctxt) (ξ : renaming) (m1 m2 : mod),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt Γ (mod_app m1 m2)) ξ (LockExt (LockExt Γ m1) m2)
    | LockNothingLeq1'' : forall (Γ : Ctxt) (ξ : renaming),
        (forall n, ξ n = n) ->
        ctxt_leq Γ ξ (LockExt Γ base)
    | LockNothingLeq2'' : forall (Γ : Ctxt) (ξ : renaming),
        (forall n, ξ n = n) ->
        ctxt_leq (LockExt Γ base) ξ Γ
    | CtxtLeqTrans : forall {Γ Δ E : Ctxt} {ξ1 ξ2 : renaming} (ξ3 : renaming),
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
      - apply EmptyCtxtLeq. intro n. rewrite <- ext_eq. apply H0.
      - apply @VarExtLeq with (ξ1 := ξ1); auto.
        intro n. rewrite <- ext_eq. apply H0.
      - apply @VarAddLeq with (ξ1 := ξ1); auto.
        intro n; rewrite <- ext_eq; apply H0.
      - apply VarSwapLeq. 3 : intro n. all: rewrite <- ext_eq; auto.
      - apply LockCollapseLeq; intro n; transitivity (ξ n); auto.
      - apply LockSplitLeq; intro n; transitivity (ξ n); auto.
      - apply LockNothingLeq1''; intro n; transitivity (ξ n); auto.
      - apply LockNothingLeq2''; intro n; transitivity (ξ n); auto.
      - apply @CtxtLeqTrans with (ξ2 := ξ2) (ξ1 := ξ1) (Δ := Δ); auto.
        intro n; transitivity (ξ3 n); auto.
    Qed.

    Fixpoint ctxt_leq_refl (Γ : Ctxt) : ctxt_leq Γ id_renaming Γ :=
      match Γ with
      | EmptyCtxt => EmptyCtxtLeq (fun n => eq_refl)
      | VarExt Γ m τ => @VarExtLeq Γ Γ id_renaming id_renaming m τ (fun n => eq_sym (renup_id n)) (ctxt_leq_refl Γ)
      | LockExt Γ m => @LockExtLeq Γ Γ id_renaming m (ctxt_leq_refl Γ)
      end.

    Theorem ctxt_leq_refl' : forall (Γ1 Γ2 : Ctxt),
        ctxt_equiv Γ1 Γ2 ->
        ctxt_leq Γ1 id_renaming Γ2.
    Proof using.
      intros Γ1 Γ2 eqv; induction eqv; cbn;
        try (econstructor; eauto; fail).
      - eapply VarExtLeq; eauto. intro n; unfold id_renaming; destruct n; reflexivity.
      - eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                  (ξ2 := id_renaming)
                                  (Δ := LockExt Γ (mod_app m1 m2)); eauto.
        -- eapply LockCollapseLeq; intro n; reflexivity.
        -- eapply LockExtLeq; eauto.
      - eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                  (ξ2 := id_renaming)
                                  (Δ := LockExt Δ (mod_app m1 m2)); eauto.
        -- eapply LockExtLeq; eauto.
        -- eapply LockSplitLeq; eauto.
      - eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                  (ξ2 := id_renaming)
                                  (Δ := Δ); eauto.
        eapply LockNothingLeq1''; auto.
      - eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                  (ξ2 := id_renaming)
                                  (Δ := Γ); eauto.
        eapply LockNothingLeq2''; auto.
      - eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                  (ξ2 := id_renaming)
                                  (Δ := Δ); eauto.
    Qed.

    Theorem ctxt_leq_proper : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming},
        ctxt_equiv Γ1 Γ2 ->
        ctxt_equiv Δ1 Δ2 ->
        ctxt_leq Γ1 ξ Δ1 ->
        ctxt_leq Γ2 ξ Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 ξ H0 H1 H2. symmetry in H0.
      eapply @CtxtLeqTrans with (ξ1 := id_renaming)
                                (ξ2 := ξ)
                                (Δ := Γ1); eauto.
      apply ctxt_leq_refl'; auto.
      eapply @CtxtLeqTrans with (ξ1 := ξ)
                                (ξ2 := id_renaming)
                                (Δ := Δ1); eauto.
      apply ctxt_leq_refl'; auto.
    Qed.

    Theorem ctxt_leq_numvars: forall Γ Δ ξ,
        ctxt_leq Γ ξ Δ ->
        num_vars Γ <= num_vars Δ.
    Proof using.
      intros Γ Δ ξ lq; induction lq; cbn; try lia.
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

    Lemma ctxt_leq_below_lock_exists : forall {Γ Δ : Ctxt} {ξ : renaming},
        ctxt_leq Γ ξ Δ ->
        forall m k,
          lock_location Δ m = Some k ->
          exists k', lock_location Γ m = Some k'.
    Proof using.
      intros Γ Δ ξ lq; induction lq; intros m' k eq; cbn in *;
        repeat match goal with
          | [ |- exists k, Some ?a = Some k ] => exists a; reflexivity
          | [ H : Some ?a = None |- _ ] => inversion H
          | [ H : None = Some ?a |- _ ] => inversion H
          | [ H : Some ?a = Some ?b |- _ ] =>
              inversion H; subst; clear H
          | [ IH : forall m k, lock_location ?Δ m = Some k -> exists k', lock_location ?Γ m = Some k',
                H : context[lock_location ?Δ ?m] |- _] =>
              lazymatch goal with
              | [ _ : lock_location Γ m = _ |- _] => fail
              | [ H : lock_location Δ m = None |- _] => fail
              | [ H : lock_location Δ m = Some ?k |- _] =>
                  destruct (IH m k H)
              | _ =>
                  let H' := fresh in
                  destruct (lock_location Δ m) eqn: H';
                  cbn in H;
                  lazymatch goal with
                  | [ H : lock_location Δ m = Some ?k |- _] =>
                      destruct (IH m k H)
                  | _ => idtac
                  end 
              end
          | [ H : lock_location ?Γ ?m = Some _ |- context[lock_location ?Γ ?m]] => rewrite H
          | [ H : lock_location ?Γ ?m = None |- context[lock_location ?Γ ?m]] => rewrite H
          | [ H : context [prefixb ?m ?Γ] |- _ ] =>
              lazymatch type of H with
              | prefixb m Γ = _ => fail
              | _ =>
                  lazymatch goal with
                  | [ H' : prefixb m Γ = _ |- _ ] => rewrite H' in H
                  | _ =>
                      let H' := fresh "eq" in
                      destruct (prefixb m Γ) eqn: H'
                  end
              end
          end.
      - destruct m'; inversion eq; subst; clear eq. exists 0; reflexivity.
      - rewrite (ctxt_leq_all_locks lq); rewrite eq0; exists x; reflexivity.
      - rewrite (ctxt_leq_all_locks lq); rewrite eq0; rewrite eq1; exists 0; reflexivity.
      - rewrite (ctxt_leq_all_locks lq); rewrite eq0; rewrite eq1; exists 0; reflexivity.
      - destruct (lock_location Γ m') eqn:eq'; inversion eq; subst; clear eq.
        eexists; reflexivity.
      - apply prefixb_PrefixOf in eq0.
        assert (PrefixOf m' (mod_app (all_locks Γ) m1)) as H1
            by (transitivity (all_locks Γ); [assumption | apply PrefixOf_app]).
        apply PrefixOf_prefixb in H1. rewrite H1. eexists; reflexivity.
      - destruct (prefixb m' (mod_app (all_locks Γ) m1)) eqn:eq2.
        eexists; reflexivity.
        rewrite mod_app_assoc. rewrite eq1. eexists; eauto.
      - rewrite <- mod_app_assoc.
        assert (PrefixOf m' (mod_app (mod_app (all_locks Γ) m1) m2)) as H1
            by (transitivity (mod_app (all_locks Γ) m1);
                [apply prefixb_PrefixOf; assumption | apply PrefixOf_app]).
        apply PrefixOf_prefixb in H1. rewrite H1. eexists; reflexivity.
      - assert (~ PrefixOf m' (all_locks Γ)) as H1
            by (apply prefixb_not_PrefixOf in eq0;
                intro H1; apply eq0; transitivity (all_locks Γ); [assumption | apply PrefixOf_app]).
        apply not_PrefixOf_prefixb in H1. rewrite H1.
        rewrite <- mod_app_assoc. rewrite eq1. eexists; reflexivity.
      - pose proof (lock_location_prefix eq). rewrite (PrefixOf_prefixb H1). eexists; reflexivity.
    Qed.
    
    Theorem ctxt_leq_below_lock' : forall {Γ Δ : Ctxt} {ξ : renaming},
        ctxt_leq Γ ξ Δ ->
        forall n m k,
          lock_location Δ m = Some k ->
          ξ n < k ->
          exists k', lock_location Γ m = Some k' /\ n < k'.
    Proof using.
      intros Γ Δ ξ lq; induction lq; intros n m' k eq xi_n_lt_k; cbn in eq; cbn;
                repeat match goal with
          | [ |- exists k, Some ?a = Some k ] => exists a; reflexivity
          | [ H : Some ?a = None |- _ ] => inversion H
                  | [ H : None = Some ?a |- _ ] => inversion H
                  | [ H : ?a < 0 |- _ ] => inversion H
          | [ H : Some ?a = Some ?b |- _ ] =>
              inversion H; subst; clear H
          | [ IH : forall m k, lock_location ?Δ m = Some k -> exists k', lock_location ?Γ m = Some k',
                H : context[lock_location ?Δ ?m] |- _] =>
              lazymatch goal with
              | [ _ : lock_location Γ m = _ |- _] => fail
              | [ H : lock_location Δ m = None |- _] => fail
              | [ H : lock_location Δ m = Some ?k |- _] =>
                  destruct (IH m k H)
              | _ =>
                  let H' := fresh in
                  destruct (lock_location Δ m) eqn: H';
                  cbn in H;
                  lazymatch goal with
                  | [ H : lock_location Δ m = Some ?k |- _] =>
                      destruct (IH m k H)
                  | _ => idtac
                  end 
              end
          | [ H : lock_location ?Γ ?m = Some _ |- context[lock_location ?Γ ?m]] => rewrite H
          | [ H : lock_location ?Γ ?m = None |- context[lock_location ?Γ ?m]] => rewrite H
          | [ H : context [prefixb ?m ?Γ] |- _ ] =>
              lazymatch type of H with
              | prefixb m Γ = _ => fail
              | _ =>
                  lazymatch goal with
                  | [ H' : prefixb m Γ = _ |- _ ] => rewrite H' in H
                  | _ =>
                      let H' := fresh "eq" in
                      destruct (prefixb m Γ) eqn: H'
                  end
              end
          end.
      - rewrite H0 in xi_n_lt_k; destruct m'; inversion eq; subst; clear eq.
        inversion xi_n_lt_k.
      - destruct (lock_location Δ m') eqn:eqΔ; inversion eq; subst; clear eq.
        rewrite H0 in xi_n_lt_k.
        destruct n; cbn in xi_n_lt_k.
        destruct (ctxt_leq_below_lock_exists lq m' n0 eqΔ). rewrite H1.
        eexists; split; [reflexivity| lia].
        rewrite <- PeanoNat.Nat.succ_lt_mono in xi_n_lt_k.
        destruct (IHlq n m' n0 eqΔ xi_n_lt_k) as [x [H1 H2]].
        rewrite H1. exists (S x); split; [reflexivity| rewrite <- PeanoNat.Nat.succ_lt_mono; assumption].
      - rewrite (ctxt_leq_all_locks lq); rewrite eq0.
        destruct (IHlq n m' k eq xi_n_lt_k) as [k' [eq' lt']].
        eexists; split; eassumption.
      (* - rewrite (ctxt_leq_all_locks lq); rewrite eq0; rewrite eq1. *)
      (*   inversion xi_n_lt_k. *)
      - destruct (lock_location Δ m') eqn:eq'; inversion eq; subst; clear eq.
        rewrite H0 in xi_n_lt_k; rewrite <- PeanoNat.Nat.succ_lt_mono in xi_n_lt_k.
        apply IHlq with (k := n0); auto.
      - destruct (lock_location Γ m') eqn:eq'; inversion eq; subst; clear eq.
        eexists; split; [reflexivity |].
        destruct n. lia. destruct n; try lia. rewrite H2 in xi_n_lt_k. assumption.
      - assert (PrefixOf m' (mod_app (all_locks Γ) m1)) as pfx
            by (transitivity (all_locks Γ); [apply prefixb_PrefixOf; assumption| apply PrefixOf_app]).
        rewrite (PrefixOf_prefixb pfx). rewrite H0 in xi_n_lt_k.
        eexists; split; [reflexivity | assumption].
      - rewrite H0 in xi_n_lt_k; destruct (prefixb m' (mod_app (all_locks Γ) m1)) eqn:eq2;
          eexists; split; eauto.
      - rewrite H0 in xi_n_lt_k; eexists; split; eauto.
      - rewrite (PrefixOf_prefixb (lock_location_prefix eq)). rewrite H0 in xi_n_lt_k.
        eexists; split; eauto.
      - rewrite H0 in xi_n_lt_k. destruct (IHlq2 (ξ1 n) m' k eq xi_n_lt_k) as [k' [eqΔ ltk']].
        apply IHlq1 with (k := k'); auto.
    Qed.

    Theorem ctxt_leq_below_lock'' : forall {Γ Δ : Ctxt} {ξ : renaming},
        ctxt_leq Γ ξ Δ ->
        forall n m k k',
          lock_location Δ m = Some k ->
          lock_location Γ m = Some k' ->
          k' <= n ->
          k <= ξ n.
    Proof using.
      intros Γ Δ ξ H0 n m k k' H1 H2 H3.
      destruct (Compare_dec.le_gt_dec k (ξ n)); auto.
      destruct (ctxt_leq_below_lock' H0 n m k H1 ltac:(lia)) as [k'' [eq n_lt_k'']].
      rewrite H2 in eq; inversion eq; subst; clear eq. lia.
    Qed.      
    
    Hint Constructors Ctxt : ctxts.
    Hint Constructors ctxt_equiv : ctxts.
    Hint Constructors ctxt_leq : ctxts.
    
    Lemma Inctxt_leq : forall {Γ Δ : Ctxt} {ξ : renaming} (lq : ctxt_leq Γ ξ Δ),
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
          | Some Δ => Some (VarExt Δ base UnitT)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb (cons m p) (all_locks Γ)
          then change_lock_after Γ m p q 
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => if prefixb (cons m'' p) m'
                            then Some (LockExt Γ (cons m'' q))
                            else None
               end
      end.
    
    Fixpoint remove_lock_after (Γ : Ctxt) (m : mod) (p : PName) : option Ctxt :=
      match Γ with
      | EmptyCtxt => None
      | VarExt Γ m' τ =>
          match remove_lock_after Γ m p with
          | Some Δ => Some (VarExt Δ base UnitT)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb (cons m p) (all_locks Γ)
          then remove_lock_after Γ m p
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => if prefixb (cons m'' p) m'
                            then Some (LockExt Γ m'')
                            else None
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
          | Some Δ => Some (VarExt Δ base UnitT)
          | None => None
          end
      | LockExt Γ m' =>
          if prefixb m (all_locks Γ)
          then add_lock_after Γ m p
          else match remove_Prefix (all_locks Γ) m with
               | None => None
               | Some m'' => if prefixb m'' m'
                            then Some (LockExt Γ (cons m'' p))
                            else None
               end
      end.

    


    Theorem change_lock_vars : forall {Γ Δ : Ctxt} {m1 : mod} {p q : PName} {m2 : mod} {τ : type} {n m : nat},
        lock_location Γ (cons m1 p) = Some m ->
        m <= n ->
        vars Γ n = Some (m2, τ) ->
        change_lock_after Γ m1 p q = Some Δ ->
        vars Δ n = Some (m2, τ).
    Proof using.
      intro Γ; induction Γ; intros Δ m1 p q m2 τ n m' m'eq m'len vseq Δeq; cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : None = Some _ |- _ ] => inversion H
          end; auto.
      - destruct (lock_location Γ (cons m1 p)) eqn:m'eq';
          inversion m'eq; subst; clear m'eq.
        destruct (change_lock_after Γ m1 p q) eqn:Δeq'; inversion Δeq; subst;
          destruct n; [inversion m'len|].
        cbn.
        apply le_S_n in m'len.
        eapply IHΓ; eauto.
      - destruct (prefixb (cons m1 p) (all_locks Γ)) eqn:eq_pfx1;
          [eapply IHΓ; eauto|].
        destruct (prefixb (cons m1 p) (mod_app (all_locks Γ) m)) eqn:eq_pfx2;
          inversion m'eq; subst; clear m'eq.
        pose proof (extended_suffix_prefix (prefixb_PrefixOf eq_pfx2) (prefixb_not_PrefixOf eq_pfx1)).
        inversion H0; subst.
        rewrite H3 in eq_pfx1. apply prefixb_not_PrefixOf in eq_pfx1.
        exfalso; apply eq_pfx1; reflexivity.
        destruct (prefix_remove_Some pf) as [m'' eq_m''].
        rewrite eq_m'' in Δeq.
        destruct (prefixb (cons m'' p) m) eqn:eq_pfx3; inversion Δeq; subst.
        cbn; assumption.
    Qed.

    Theorem remove_lock_vars : forall {Γ Δ : Ctxt} {m1 : mod} {p : PName} {m2 : mod} {τ : type} {n m : nat},
        lock_location Γ (cons m1 p) = Some m ->
        m <= n ->
        vars Γ n = Some (m2, τ) ->
        remove_lock_after Γ m1 p = Some Δ ->
        vars Δ n = Some (m2, τ).
    Proof using.
      intro Γ; induction Γ; intros Δ m1 p m2 τ i j eq m'len vseq Δeq; cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H
          | [ H : None = Some _ |- _ ] => inversion H
          end; auto.
      - destruct (lock_location Γ (cons m1 p)) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
        destruct (remove_lock_after Γ m1 p) as [Δ'|] eqn:Δeq'; inversion Δeq; subst; clear Δeq;
          rename Δeq' into Δeq; rename Δ' into Δ.
        cbn; destruct i; [inversion m'len |].
        eapply IHΓ; eauto; lia.
      - destruct (prefixb (cons m1 p) (all_locks Γ)) eqn:pfx; [eapply IHΓ; eauto|].
        destruct (remove_Prefix (all_locks Γ) m1) as [m3|] eqn:eqm3; [| inversion Δeq].
        destruct (prefixb (cons m3 p) m); inversion Δeq; subst.
        cbn; assumption.
    Qed.
        
    Theorem add_lock_vars : forall {Γ Δ : Ctxt} {m1 : mod} {p : PName} {m2 : mod} {τ : type} {n m : nat},
        lock_location Γ m1 = Some m ->
        m <= n ->
        vars Γ n = Some (m2, τ) ->
        add_lock_after Γ m1 p = Some Δ ->
        vars Δ n = Some (m2, τ).
    Proof using.
      intro Γ; induction Γ; intros Δ m1 p m2 τ i j eq jeq veq Δeq; cbn in *.
      - inversion veq.
      - destruct (lock_location Γ m1) eqn:eq'; inversion eq; subst; clear eq; rename eq' into eq.
        destruct (add_lock_after Γ m1 p) as [Δ'|] eqn:Δeq'; inversion Δeq; subst; clear Δeq;
          rename Δ' into Δ; rename Δeq' into Δeq.
        cbn; destruct i; inversion veq; subst. inversion jeq.
        rewrite H1; eapply IHΓ; eauto; lia.
      - destruct (prefixb m1 (all_locks Γ)) eqn:pfx. eapply IHΓ; eauto.
        destruct (remove_Prefix (all_locks Γ) m1) as [m3|] eqn:eqm3; [| inversion Δeq].
        destruct (prefixb m3 m) eqn:pfx'; inversion Δeq; subst; clear Δeq.
        cbn; assumption.
    Qed.
    
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
           pose proof (remove_Some_prefix eqm'').
           destruct (PrefixOf_peel H0) as [m2 eqm2]; subst.
           rewrite remove_app in eqm''; inversion eqm''; subst.
           assert (cons (mod_app (all_locks Γ) m'') p = mod_app (all_locks Γ) (cons m'' p)) as H1 by reflexivity; rewrite H1 in pfx; clear H1.
           apply mod_app_prefix in pfx.
           rewrite (PrefixOf_prefixb pfx).
           eexists; eauto.
    Qed.

    Theorem remove_lock_after_defined : forall {Γ : Ctxt} {m : mod} {p : PName},
        PrefixOf (cons m p) (all_locks Γ) ->
        exists (Δ : Ctxt), remove_lock_after Γ m p = Some Δ.
    Proof using.
      intro Γ; induction Γ; intros m_pre p pfx; cbn in *; try (inversion pfx; fail).
      - destruct (IHΓ m_pre p pfx) as [Δ Δeq]; rewrite Δeq.
        eexists; auto.
      - destruct (prefixb (cons m_pre p) (all_locks Γ)) eqn:eq_pre.
        -- apply IHΓ; apply prefixb_PrefixOf; assumption.
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
           rewrite (PrefixOf_prefixb (PrefixOf_app (cons m' p) m'')).
           eexists; reflexivity.
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
           rewrite (PrefixOf_prefixb (PrefixOf_app m'' m''')).
           eexists; reflexivity.
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
        -- destruct (remove_Prefix (all_locks Γ) m) eqn: eq'; inversion eq; subst; clear eq.
           destruct (prefixb (cons m0 p) m') eqn:eq''; inversion H1; subst; clear H1.
           pose proof (remove_Some_prefix eq') as pfx.
           destruct (PrefixOf_peel pfx) as [m2 eqm2]; subst.
           rewrite remove_app in eq'; inversion eq'; subst; clear eq'.
           assert (cons (mod_app (all_locks Γ) m0) p = mod_app (all_locks Γ) (cons m0 p))
             as H0 by reflexivity; rewrite H0; clear H0.
           apply mod_app_mono_l. apply prefixb_PrefixOf; assumption.
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
           destruct (prefixb (cons m0 p) m') eqn:pfx; inversion eq; subst; clear eq.
           pose proof (remove_Some_prefix eq_rmv).
           destruct (PrefixOf_peel H0) as [m2 eqm2]; subst.
           apply prefixb_PrefixOf in pfx; destruct (PrefixOf_peel pfx) as [m3 eqm3]; subst.
           rewrite remove_app in eq_rmv; inversion eq_rmv; subst; clear eq_rmv.
           assert (cons (mod_app (all_locks Γ) m0) p = mod_app (all_locks Γ) (cons m0 p))
             as H1 by reflexivity; rewrite H1; clear H1.
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
        -- cbn. transitivity (all_locks Γ). apply prefixb_PrefixOf; assumption.
           apply PrefixOf_app.
        -- destruct (remove_Prefix (all_locks Γ) m) eqn:eq_rmv; [| inversion eq].
           destruct (prefixb m0 m') eqn:pfx; inversion eq; subst; clear eq; cbn.
           pose proof (remove_Some_prefix eq_rmv).
           destruct (PrefixOf_peel H0) as [m2 eqm2]; subst.
           apply mod_app_mono_l.
           rewrite remove_app in eq_rmv; inversion eq_rmv; subst; clear eq_rmv.
           apply prefixb_PrefixOf; assumption.
    Qed.
    
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

    Lemma change_lock_after_num_vars : forall {Γ Δ : Ctxt} {m : mod} {p q : PName},
        change_lock_after Γ m p q = Some Δ ->
        num_vars Γ = num_vars Δ.
    Proof using.
      intros Γ; induction Γ; intros Δ m' p q eqΔ; cbn in *.
      - inversion eqΔ.
      - destruct (change_lock_after Γ m' p q) eqn:eq; inversion eqΔ; subst; clear eqΔ.
        apply IHΓ in eq; cbn; f_equal; assumption.
      - destruct (prefixb (cons m' p) (all_locks Γ)).
        -- apply IHΓ in eqΔ; assumption.
        -- destruct (remove_Prefix (all_locks Γ) m') eqn:eq; [| inversion eqΔ].
           destruct (prefixb (cons m0 p) m) eqn:eq'; inversion eqΔ; subst; clear eqΔ.
           cbn; reflexivity.
    Qed.

    Lemma remove_lock_after_num_vars : forall {Γ Δ : Ctxt} {m : mod} {p : PName},
        remove_lock_after Γ m p = Some Δ ->
        num_vars Γ = num_vars Δ.
    Proof using.
      intro Γ; induction Γ; intros Δ m' p eqΔ; cbn in *.
      - inversion eqΔ.
      - destruct (remove_lock_after Γ m' p) as [Δ'|] eqn:eqΔ'; inversion eqΔ; subst; clear eqΔ;
          rename eqΔ' into eqΔ; rename Δ' into Δ.
        cbn; f_equal; eapply IHΓ; exact eqΔ.
      - destruct (prefixb (cons m' p) (all_locks Γ)) eqn:pfx.
        -- eapply IHΓ; exact eqΔ.
        -- destruct (remove_Prefix (all_locks Γ) m') eqn:eq; [| inversion eqΔ].
           destruct (prefixb (cons m0 p) m) eqn:eq'; inversion eqΔ; subst; clear eqΔ.
           cbn; reflexivity.
    Qed.

    Lemma add_lock_after_num_vars : forall {Γ Δ : Ctxt} {m : mod} {p : PName},
        add_lock_after Γ m p = Some Δ ->
        num_vars Γ = num_vars Δ.
    Proof using.
      intro Γ; induction Γ; intros Δ m' p eqΔ; cbn in *.
      - eq_bool; subst; inversion eqΔ; subst; cbn; reflexivity.
      - destruct (add_lock_after Γ m' p) as [Δ'|] eqn:eqΔ'; inversion eqΔ; subst; clear eqΔ;
          rename eqΔ' into eqΔ; rename Δ' into Δ.
        cbn; f_equal; eapply IHΓ; exact eqΔ.
      - destruct (prefixb m' (all_locks Γ)) eqn:pfx.
        -- eapply IHΓ; exact eqΔ.
        -- destruct (remove_Prefix (all_locks Γ) m') eqn:eq; [| inversion eqΔ].
           destruct (prefixb m0 m) eqn:eq'; inversion eqΔ; subst; clear eqΔ.
           cbn; reflexivity.
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

    Theorem change_lock_after_proper' : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p q : PName},
        ctxt_equiv Γ1 Γ2 ->
        change_lock_after Γ1 m p q = Some Δ1 ->
        change_lock_after Γ2 m p q = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p q eqv1; revert Δ1 Δ2 m p q; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p q eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H 
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
      - rewrite mod_app_assoc in H8; cbn in H8. apply mod_app_inj in H8; subst.
        assert (cons (mod_app m1 m) q = mod_app m1 (cons m q)) as eq by reflexivity; rewrite eq; clear eq.
        transitivity (LockExt Γ (mod_app m1 (cons m q))); [constructor; reflexivity |].
        constructor; exact eqv1.
      - (* apply PrefixOf_peel in H5; destruct H5 as [m3 eqm3]; subst. *)
        rewrite mod_app_assoc in H8; apply mod_app_inj in H8; subst.
        transitivity (LockExt Δ (mod_app m1 (cons m0 q))).
        cbn; constructor; assumption.
        constructor; reflexivity.
      - rename Δ2 into Δ3; rename eq2 into eq3.
        pose proof (change_lock_after_prefix eq1).
        rewrite @all_locks_proper with (Δ := Δ) in H0; [| assumption].
        destruct (@change_lock_after_defined Δ m p q H0) as [Δ2 eq2].
        transitivity Δ2. eapply IHeqv1_1; eauto. eapply IHeqv1_2; eauto.
    Qed.

    
    Theorem change_lock_after_proper : forall {Γ1 Γ2 Δ1 : Ctxt} {m : mod} {p q : PName},
        change_lock_after Γ1 m p q = Some Δ1 ->
        ctxt_equiv Γ1 Γ2 ->
        exists Δ2, change_lock_after Γ2 m p q = Some Δ2 /\ ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 m p q H0 H1.
      pose proof (change_lock_after_prefix H0).
      rewrite (all_locks_proper H1) in H2.
      eapply @change_lock_after_defined with (q := q) in H2.
      destruct H2 as [Δ2 eqΔ2].
      exists Δ2; split; [exact eqΔ2|].
      eapply change_lock_after_proper'; eauto.
    Qed.

    Theorem remove_lock_after_proper' : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        remove_lock_after Γ1 m p = Some Δ1 ->
        remove_lock_after Γ2 m p = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p eqv1; revert Δ1 Δ2 m p; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H
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
      1,2: rewrite mod_app_assoc in H8; apply mod_app_inj in H8; subst;
      constructor; auto.
      destruct (remove_lock_after Δ m p) as [Δ3|] eqn:eq3;
        [| rewrite (remove_lock_equiv_none' eqv1_1 eq3) in eq1; inversion eq1].
      transitivity Δ3. apply IHeqv1_1 with (m := m) (p := p); assumption.
      apply IHeqv1_2 with (m := m) (p := p); assumption.
    Qed.

    Theorem remove_lock_after_proper : forall {Γ1 Γ2 Δ1 : Ctxt} {m : mod} {p : PName},
        remove_lock_after Γ1 m p = Some Δ1 ->
        ctxt_equiv Γ1 Γ2 ->
        exists Δ2, remove_lock_after Γ2 m p = Some Δ2 /\ ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 m p H0 H1.
      pose proof (remove_lock_after_prefix H0).
      rewrite (all_locks_proper H1) in H2.
      eapply @remove_lock_after_defined in H2.
      destruct H2 as [Δ2 eqΔ2].
      exists Δ2; split; [exact eqΔ2|].
      eapply remove_lock_after_proper'; eauto.
    Qed.

    
    Theorem add_lock_after_proper' : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {m : mod} {p : PName},
        ctxt_equiv Γ1 Γ2 ->
        add_lock_after Γ1 m p = Some Δ1 ->
        add_lock_after Γ2 m p = Some Δ2 ->
        ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 m p eqv1; revert Δ1 Δ2 m p; induction eqv1;
        try (rename m into m'); intros Δ1 Δ2 m p eq1 eq2; cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H
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
          end;
        repeat match goal with
          | [ H : mod_app ?m1 ?m4 = mod_app (mod_app ?m1 ?m2) ?m3 |- _ ] =>
              symmetry in H; rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app (mod_app ?m1 ?m2) ?m3 = mod_app ?m1 ?m4 |- _ ] =>
              rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app ?m1 ?m2 = mod_app ?m1 ?m3 |- _ ] => apply mod_app_inj in H; subst
        end; try lia.
      - destruct m0; cbn in H2; try lia.
        destruct m1; cbn in H2; try lia.
        cbn in *. exfalso; apply H4; reflexivity.
      - assert (cons (mod_app m1 m) p = mod_app m1 (cons m p)) as eq by reflexivity; rewrite eq; clear eq.
        constructor; auto.
      - destruct m1; cbn in H4; try lia.
        destruct m0; cbn in H4; try lia.
        cbn in *; exfalso; apply H1; reflexivity.
      - assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq; clear eq.
        constructor; auto.
      - apply readd_remove_prefix in H2. cbn in H2. rewrite H2 in H1. exfalso; apply H1; reflexivity.
      - apply readd_remove_prefix in H2. cbn in H2. rewrite H2 in H1. exfalso; apply H1; reflexivity.
      - destruct (add_lock_after Δ m p) as [Δ3|] eqn:eq3;
          [| rewrite (add_lock_equiv_none' eqv1_1 eq3) in eq1; inversion eq1].
        transitivity Δ3. apply IHeqv1_1 with (m := m) (p := p); assumption.
        apply IHeqv1_2 with (m := m) (p := p); assumption.
    Qed.                                             

    Theorem add_lock_after_proper : forall {Γ1 Γ2 Δ1 : Ctxt} {m : mod} {p : PName},
        add_lock_after Γ1 m p = Some Δ1 ->
        ctxt_equiv Γ1 Γ2 ->
        exists Δ2, add_lock_after Γ2 m p = Some Δ2 /\ ctxt_equiv Δ1 Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 m p H0 H1.
      pose proof (add_lock_after_prefix H0).
      rewrite (all_locks_proper H1) in H2.
      eapply @add_lock_after_defined in H2.
      destruct H2 as [Δ2 eqΔ2].
      exists Δ2; split; [exact eqΔ2|].
      eapply add_lock_after_proper'; eauto.
    Qed.

    
    (* Corollary remove_lock_after_equiv : forall {Γ Δ : Ctxt} {m : mod} {p : PName}, *)
    (*     remove_lock_after Γ m p = Some Δ -> *)
    (*     exists (Γ1 Γ2 : Ctxt), ctxt_equiv Γ (ctxt_app (LockExt Γ1 p) Γ2) /\ ctxt_equiv Δ (ctxt_app Γ1 Γ2). *)
    (* Proof using. *)
    (*   intros Γ Δ m p eq. *)
    (*   pose proof (remove_lock_after_prefix eq) as pfx. *)
    (*   destruct (all_locks_prefix_equiv' pfx) as [Γ1 [Γ2 [eqv eq']]]. *)
    (*   assert (remove_lock_after (LockExt Γ1 p) m p = Some (LockExt Γ1 base)). *)
    (*   cbn; destruct (prefixb (cons m p) (all_locks Γ1)) eqn:eq_pfxb; *)
    (*     [apply prefixb_PrefixOf in eq_pfxb; rewrite eq' in eq_pfxb; *)
    (*      apply PrefixOf_size in eq_pfxb; cbn in eq_pfxb; lia|]. *)
    (*   rewrite eq'. rewrite remove_all_mod. eq_bool. reflexivity. *)
    (*   apply @remove_lock_after_app with (Γ2 := Γ2) in H0. *)
    (*   pose proof (remove_lock_equiv eqv eq H0). *)
    (*   exists Γ1; exists Γ2; split; auto. transitivity (ctxt_app (LockExt Γ1 base) Γ2); auto. *)
    (*   apply ctxt_app_proper; [apply LockNothingEquiv2|]; reflexivity. *)
    (* Qed. *)

    Theorem ctxt_leq_change_lock_after : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {ξ : renaming} {m : mod} {p q : PName},
        ctxt_leq Γ1 ξ Γ2 ->
        change_lock_after Γ1 m p q = Some Δ1 ->
        change_lock_after Γ2 m p q = Some Δ2 ->
        ctxt_leq Δ1 ξ Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 ξ m p q lq; revert Δ1 Δ2 m p q; induction lq; try rename m into m'; intros Δ1 Δ2 m p q eq1 eq2;
        cbn in *;
        repeat match goal with
          | [ H : ?P |- ?P ] => exact H 
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
              | _ =>
                  lazymatch goal with
                  | [ H' : change_lock_after Γ m p q = _ |- _ ] => rewrite H' in H
                  | _ => let H := fresh in destruct (change_lock_after Γ m p q) eqn: H
                  end
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
      - rewrite eq1 in eq2; inversion eq2; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite mod_app_assoc in H9; apply mod_app_inj in H9; subst.
        apply @CtxtLeqTrans with (ξ1 := id_renaming) (ξ2 := id_renaming) (Δ := LockExt Γ (mod_app m1 (cons m q))). intro n; rewrite H0; reflexivity.
        constructor. intro n; reflexivity.
        apply ctxt_leq_refl.
      - rewrite eq1 in eq2; inversion eq2; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite mod_app_assoc in H9; apply mod_app_inj in H9; subst.
        apply @CtxtLeqTrans with (ξ1 := id_renaming) (ξ2 := id_renaming) (Δ := LockExt Γ (mod_app m1 (cons m0 q))).
        intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
        constructor. intro n; reflexivity.
      - rewrite eq1 in eq2; inversion eq2; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite eq1 in eq2; inversion eq2; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming). intro n; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - pose proof (change_lock_after_prefix eq1) as lox;
          rewrite (ctxt_leq_all_locks lq1) in lox;
          destruct (@change_lock_after_defined _ _ _ q lox) as [Δ3 eq3]; clear lox.
        pose proof (IHlq1 _ _ _ _ _ eq1 eq3).
        pose proof (IHlq2 _ _ _ _ _ eq3 eq2).
        eapply CtxtLeqTrans; eauto.
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
          | [ H : ?P |- ?P ] => exact H
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
          end;
        repeat match goal with
          | [ H : mod_app ?m1 ?m4 = mod_app (mod_app ?m1 ?m2) ?m3 |- _ ] =>
              symmetry in H; rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app (mod_app ?m1 ?m2) ?m3 = mod_app ?m1 ?m4 |- _ ] =>
              rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app ?m1 ?m2 = mod_app ?m1 ?m3 |- _ ] => apply mod_app_inj in H; subst
          end; try lia; try (econstructor; eauto with ctxts; fail).
      - rewrite eq2 in eq1; inversion eq1; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite eq2 in eq1; inversion eq1; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite eq2 in eq1; inversion eq1; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - rewrite eq2 in eq1; inversion eq1; subst.
        apply @ctxt_leq_ext with (ξ1 := id_renaming).
        intro n; unfold id_renaming; rewrite H0; reflexivity.
        apply ctxt_leq_refl.
      - pose proof (remove_lock_after_prefix eq1).
        rewrite (ctxt_leq_all_locks lq1) in H1.
        apply remove_lock_after_defined in H1.
        destruct H1 as [Δ3 eq3].
        specialize (IHlq1 _ _ _ _ eq1 eq3).
        specialize (IHlq2 _ _ _ _ eq3 eq2).
        apply @CtxtLeqTrans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
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
          | [ H : ?P |- ?P ] => exact H
          | [ H : None = Some _ |- _ ] => inversion H
          | [ H : Some _ = None |- _ ] => inversion H
          | [ H : cons _ _ = base |- _ ] => inversion H
          | [ H : base = cons _ _ |- _ ] => inversion H
          | [ H : ~ PrefixOf ?a ?a |- _ ] =>
              exfalso; apply H; reflexivity
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
          | [ H1 : ?a = Some ?b, H2 : ?a = Some ?c |- _ ] =>
              tryif unify b c
              then fail
              else rewrite H2 in H1; inversion H1; subst
          | [ H : forall n, ?ξ n = n |- ctxt_leq ?Δ ?ξ ?Δ ] =>
              apply @ctxt_leq_ext with (ξ1 := id_renaming);
              [ intro n; unfold id_renaming; rewrite H0; reflexivity
              | apply ctxt_leq_refl ]
          end; try (econstructor; eauto with ctxts; fail); cbn in *;
        repeat match goal with
          | [ H : context[mod_size (mod_app _ _)] |- _] =>
              rewrite mod_app_size in H; cbn in H
          end;
                repeat match goal with
          | [ H : mod_app ?m1 ?m4 = mod_app (mod_app ?m1 ?m2) ?m3 |- _ ] =>
              symmetry in H; rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app (mod_app ?m1 ?m2) ?m3 = mod_app ?m1 ?m4 |- _ ] =>
              rewrite mod_app_assoc in H; apply mod_app_inj in H; subst
          | [ H : mod_app ?m1 ?m2 = mod_app ?m1 ?m3 |- _ ] => apply mod_app_inj in H; subst
          end; try lia; try (econstructor; eauto with ctxts; fail).
      - do 2 constructor; assumption.
      - destruct m0; cbn in H3; try lia.
        destruct m1; cbn in H3; try lia.
        cbn in *. exfalso; apply H5; reflexivity.
      - destruct m0; cbn in H5; try lia.
        destruct m1; cbn in H5; try lia.
        cbn in *. exfalso; apply H2; reflexivity.
      - assert (cons (mod_app m1 m0) p = mod_app m1 (cons m0 p)) as eq by reflexivity; rewrite eq; clear eq.
        constructor; auto.
      - exfalso; apply H2; reflexivity.
      - exfalso; apply H2; reflexivity.
      - pose proof (add_lock_after_prefix eq1).
        rewrite (ctxt_leq_all_locks lq1) in H1.
        apply @add_lock_after_defined  with (p := p) in H1.
        destruct H1 as [Δ3 eq3].
        specialize (IHlq1 _ _ _ _ eq1 eq3).
        specialize (IHlq2 _ _ _ _ eq3 eq2).
        apply @CtxtLeqTrans with (ξ1 := ξ1) (ξ2 := ξ2) (Δ := Δ3); auto.
    Qed.

    Lemma change_lock_after_no_locks : forall {Γ1 : Ctxt} {m : mod} {p q : PName},
        all_locks Γ1 = base ->
        change_lock_after Γ1 m p q = None.
    Proof using.
      intro Γ1; induction Γ1; intros m' p q eq; cbn in *.
      - reflexivity.
      - rewrite (IHΓ1 m' p q eq); reflexivity.
      - destruct (mod_app_base_inv _ _ eq); subst; clear eq.
        destruct (prefixb (cons m' p) (all_locks Γ1)) eqn:eq'.
        exact (IHΓ1 m' p q H0).
        rewrite H0. rewrite (remove_base_prefix m').
        destruct (prefixb (cons m' p) base) eqn:eq; [| reflexivity].
        apply prefixb_PrefixOf in eq; apply PrefixOf_base in eq; inversion eq.
    Qed.

    Lemma remove_lock_after_no_locks : forall {Γ1 : Ctxt} {m : mod} {p : PName},
        all_locks Γ1 = base ->
        remove_lock_after Γ1 m p = None.
    Proof using.
      intro Γ1; induction Γ1; intros m' p eq; cbn in *.
      - reflexivity.
      - rewrite (IHΓ1 m' p eq); reflexivity.
      - destruct (mod_app_base_inv _ _ eq); subst; clear eq.
        destruct (prefixb (cons m' p) (all_locks Γ1)) eqn:pfx.
        exact (IHΓ1 m' p H0).
        rewrite H0. rewrite (remove_base_prefix m').
        destruct (prefixb (cons m' p) base) eqn:eq; [| reflexivity].
        apply prefixb_PrefixOf in eq; apply PrefixOf_base in eq; inversion eq.
    Qed.

    Lemma add_lock_emptoid : forall {Γ1 : Ctxt} {m : mod} {p : PName} {Γ2 : Ctxt},
        Emptoid Γ1 ->
        add_lock_after Γ1 m p = Some Γ2 ->
        m = base /\ Γ2 = LockExt EmptyCtxt p.
    Proof using.
      intros Γ1 m p Γ2 etd; revert m p Γ2; induction etd; intros m p Γ2; cbn; intro eq.
      - eq_bool; subst; inversion eq; subst. split; reflexivity.
      - destruct (prefixb m (all_locks Γ)) eqn:eq'.
        destruct (IHetd m p Γ2 eq); split; assumption.
        rewrite (emptoid_all_locks etd) in eq; rewrite remove_base_prefix in eq.
        eq_bool; subst; inversion eq; subst.
        apply prefixb_not_PrefixOf in eq'; exfalso; apply eq'; apply base_Prefix.
    Qed.

    Fixpoint unit_ctxt (n : nat) : Ctxt :=
      match n with
      | 0 => EmptyCtxt
      | S n => VarExt (unit_ctxt n) base UnitT
      end.

    Lemma add_lock_no_locks : forall {Γ1 : Ctxt} {m : mod} {p : PName} {Γ2 : Ctxt},
        all_locks Γ1 = base ->
        add_lock_after Γ1 m p = Some Γ2 ->
        Γ2 = ctxt_app (LockExt EmptyCtxt p) (unit_ctxt (num_vars Γ1)).
    Proof using.
      intro Γ1; induction Γ1; intros m' p Γ2 eq1 eq2; cbn in *.
      - eq_bool; subst; inversion eq2; subst; reflexivity.
      - destruct (add_lock_after Γ1 m' p) as [Δ'|] eqn:eq2'; inversion eq2; subst; clear eq2;
          rename eq2' into eq2; rename Δ' into Δ.
        apply IHΓ1 in eq2; subst; auto.
      - apply mod_app_base_inv in eq1; destruct eq1 as [eq1 eq1']; subst.
        rewrite eq1 in eq2.
        destruct (prefixb m' base) eqn:eq2'; subst. apply IHΓ1 in eq2; auto.
        rewrite remove_base_prefix in eq2.
        rewrite eq2' in eq2; inversion eq2.
    Qed.        

  End LockChanges.

End Contexts.
