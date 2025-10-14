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

Section Contexts.
  Context {PName : Type} `{EqBool PName}.
  #[local] Abbreviation mod := (@mod PName).
  #[local] Definition ptm := @proc_to_mod PName.
  #[local] Definition PrefixOfT := @PrefixOfT PName.
  Coercion ptm : PName >-> mod.
  #[local] Abbreviation type := (type PName).
  #[local] Abbreviation expr := (expr PName).

  Record Ctxt :=
    {
      vars : nat -> mod * type;
      locks : nat -> mod;
      all_locks : mod;
      locks_mono : forall {n m}, n <= m -> PrefixOf (locks n) (locks m);
      locks_bound : forall n, PrefixOf (locks n) all_locks
    }.
  
  Definition add_lock (Γ : Ctxt) (m : mod) : Ctxt :=
    {|
      vars n := vars Γ n;
      locks n := mod_app m (locks Γ n);
      all_locks := mod_app m (all_locks Γ);
      locks_mono := fun j k leq => PrefixOf_app_mono m (locks_mono Γ leq);
      locks_bound := fun n => PrefixOf_app_mono m (locks_bound Γ n); 
    |}.
  
  Definition remove_lock (Γ : Ctxt) (m : mod) : option Ctxt.
    refine (match PrefixOfT_dec m (locks Γ 0) with
            | None => None
            | Some pfx =>
                Some ({|
                      vars n :=  vars Γ n;
                      locks n := @remove_PrefixT PName m (locks Γ n) (prefixT_prefix_trans pfx (@locks_mono Γ 0 n ltac:(lia)));
                      all_locks := @remove_PrefixT PName m (all_locks Γ) (prefixT_prefix_trans pfx (@locks_bound Γ 0));
                      locks_mono := _;
                      locks_bound := _;
                    |})
            end).
    - intros n m0 H0; apply remove_prefix_mono; apply (locks_mono Γ H0).
    - intros n; apply remove_prefix_mono; apply (locks_bound Γ).
  Defined.

  Program Definition add_var (Γ : Ctxt) (m : mod) (τ : type) : Ctxt :=
    {|
      vars n :=
        match n with
        | 0 => (m, τ)
        | S n' => vars Γ n'
        end;
      locks n :=
        match n with
        | 0 => base
        | S n' => locks Γ n'
        end;
      all_locks := all_locks Γ;
    |}.
  Next Obligation.
    induction H0. destruct n; reflexivity.
    destruct n. apply base_Prefix.
    apply locks_mono; lia.
  Defined.
  Next Obligation.
    destruct n; [apply base_Prefix | apply locks_bound].
  Qed.

  Definition ctxt_equiv' (Γ Δ : Ctxt) : Prop :=
    (forall x, snd (vars Γ x) = snd (vars Δ x))
    /\ (forall x, exists m m', all_locks Γ = mod_app (locks Γ x) m /\ all_locks Δ = mod_app (locks Δ x) m'
                  /\ mod_app (fst (vars Γ x)) m = mod_app (fst  (vars Δ x)) m')
    /\ all_locks Γ = all_locks Δ.

  Lemma ctxt_equiv'_refl (Γ : Ctxt) : ctxt_equiv' Γ Γ.
  Proof using H.
    split; [| split]; intros; try reflexivity.
    destruct (prefix_remove_Some (locks Γ x) (all_locks Γ) (locks_bound Γ x)) as [m eq].
    exists m; exists m; split; [| split].
    1,2: symmetry; apply readd_remove_prefix with (m2 := all_locks Γ); exact eq.
    reflexivity.
  Qed.

  Theorem add_lock_ext' : forall (Γ Δ : Ctxt) m, ctxt_equiv' Γ Δ -> ctxt_equiv' (add_lock Γ m) (add_lock Δ m).
  Proof using.
    intros Γ Δ m eqv; destruct eqv as [vars_eq [locks_eq all_locks_eq]]; split; [| split]; cbn;
      auto.
    2: rewrite all_locks_eq; reflexivity.
    intro x; destruct (locks_eq x) as [m1 [m2 [m1_eq [m2_eq locks_eq']]]].
    exists m1; exists m2; split; [| split].
    rewrite m1_eq. 2: rewrite m2_eq. 1,2: rewrite mod_app_assoc; reflexivity.
    exact locks_eq'.
  Qed.

  Theorem add_var_ext' : forall (Γ Δ : Ctxt) m τ, ctxt_equiv' Γ Δ -> ctxt_equiv' (add_var Γ m τ) (add_var Δ m τ).
  Proof using.
    intros Γ Δ m τ [vars_eq [locks_eq al_eq]]; split; [| split]; cbn.
    - intro x; destruct x; auto.
    - intro x; destruct x; auto.
      exists (all_locks Γ); exists (all_locks Δ); split; [symmetry; apply mod_base_app| split; [symmetry; apply mod_base_app|]].
      cbn. rewrite al_eq. reflexivity.
    - exact al_eq.
  Qed.

  #[global] Instance CtxtEquiv'Refl : Reflexive ctxt_equiv' := ctxt_equiv'_refl.

  Lemma ctxt_equiv'_sym : forall Γ Δ, ctxt_equiv' Γ Δ -> ctxt_equiv' Δ Γ.
  Proof using H.
    intros Γ Δ [typ_eqv [locks_eqv al_eqv]]; split; [| split]; try intro x; try (symmetry; auto; fail).
    destruct (locks_eqv x) as [m [m' [eq_m_Γ [eq_m'_Δ vars_eq]]]].
    exists m'; exists m; auto.
  Qed.

  #[global] Instance CtxtEquiv'Sym : Symmetric ctxt_equiv' := ctxt_equiv'_sym.

  Lemma mod_app_inj2 : forall (m m1 m2 : mod) , mod_app m m1 = mod_app m m2 -> m1 = m2.
  Proof using H.
    intros m m1; revert m; induction m1 as [| m1 IHm1 p]; cbn; intros m m2 eq.
    - symmetry; apply mod_app_id_inv with (m1 := m); exact eq.
    - destruct m2 as [|m2 q].
      -- cbn in eq.
         assert (mod_size (cons (mod_app m m1) p) = mod_size m) as eq' by (rewrite eq; reflexivity).
         cbn in eq'; rewrite mod_app_size in eq'; lia.
      -- cbn in eq; inversion eq; subst; apply IHm1 in H1; rewrite H1; reflexivity.
  Qed.
    
  
  Lemma ctxt_equiv'_trans : forall Γ Δ E : Ctxt, ctxt_equiv' Γ Δ -> ctxt_equiv' Δ E -> ctxt_equiv' Γ E.
  Proof using H.
    intros Γ Δ E [typ_eqv1 [locks_eqv1 al_eqv1]] [typ_eqv2 [locks_eqv2 al_eqv2]];
      split; [intro x; etransitivity; eauto| split; [| etransitivity; eauto ]].
    intro x; destruct (locks_eqv1 x) as [m1 [m2 [m1_eq [m2_eq vars_eq1]]]];
      destruct (locks_eqv2 x) as [m2' [m3 [m2'_eq [m3_eq vars_eq2]]]].
    assert (m2' = m2) as Heq by (apply mod_app_inj2 with (m := locks Δ x); transitivity (all_locks Δ); auto); subst.
    exists m1; exists m3; split; [| split]; auto. transitivity (mod_app (fst (vars Δ x)) m2); auto.
  Qed.
    
  #[global] Instance CtxtEquiv'Trans : Transitive ctxt_equiv' := ctxt_equiv'_trans.

  Definition ctxt_equiv (Γ Δ : Ctxt) : Prop :=
    (forall x, vars Γ x = vars Δ x)
    /\ (forall x, locks Γ x = locks Δ x)
    /\ all_locks Γ = all_locks Δ.

  Lemma ctxt_equiv_refl (Γ : Ctxt) : ctxt_equiv Γ Γ.
  Proof using.
    split; [|split]; intros; reflexivity.
  Qed.

  #[global] Instance CtxtEquivRefl : Reflexive ctxt_equiv := ctxt_equiv_refl.

  Lemma ctxt_equiv_symm : forall Γ Δ : Ctxt, ctxt_equiv Γ Δ -> ctxt_equiv Δ Γ.
  Proof using.
    intros Γ Δ [vars_eqv [locks_eqv all_locks_eqv]];
      split; [| split]; intros; symmetry; auto.
  Qed.

  #[global] Instance CtxtEquivSym : Symmetric ctxt_equiv := ctxt_equiv_symm.

  Lemma ctxt_equiv_trans : forall Γ Δ E : Ctxt, ctxt_equiv Γ Δ -> ctxt_equiv Δ E -> ctxt_equiv Γ E.
  Proof using.
    intros Γ Δ E [vars_eqv1 [locks_eqv1 all_locks_eqv1]] [vars_eqv2 [locks_eqv2 all_locks_eqv2]];
      split; [|split]; intros; etransitivity; eauto.
  Qed.

  #[global] Instance CtxtEquivTrans : Transitive ctxt_equiv := ctxt_equiv_trans.

  #[global] Instance CtxtEquivEquiv : Equivalence ctxt_equiv :=
    {|
      Equivalence_Reflexive := CtxtEquivRefl;
      Equivalence_Symmetric := CtxtEquivSym;
      Equivalence_Transitive := CtxtEquivTrans;
    |}.

  Theorem add_lock_ext : forall (Γ Δ : Ctxt) m, ctxt_equiv Γ Δ -> ctxt_equiv (add_lock Γ m) (add_lock Δ m).
  Proof using.
    intros Γ Δ m eqv; destruct eqv as [vars_eq [locks_eq all_locks_eq]]; split; [| split]; cbn;
      auto.
    - intros x; destruct x; cbn; auto.
      all: rewrite locks_eq; reflexivity.
    - rewrite all_locks_eq; reflexivity.
  Qed.

  Theorem add_var_ext : forall (Γ Δ : Ctxt) m τ, ctxt_equiv Γ Δ -> ctxt_equiv (add_var Γ m τ) (add_var Δ m τ).
  Proof using.
    intros Γ Δ m τ [vars_eq [locks_eq all_locks_eq]]; split; [| split]; cbn.
    1,2 : intro x; destruct x.
    all: auto.
  Qed.

  Lemma ctxt_equiv_to_equiv' : forall Γ Δ, ctxt_equiv Γ Δ -> ctxt_equiv' Γ Δ.
  Proof using H PName.
    intros Γ Δ [vars_eqv [locks_eqv al_eqv]]; split; [| split]; [ intro x; rewrite vars_eqv; reflexivity | | apply al_eqv].
    intro x. rewrite vars_eqv; rewrite locks_eqv; rewrite al_eqv.
    destruct (prefix_remove_Some (locks Δ x) (all_locks Δ) (locks_bound Δ x)) as [m eq].
    exists m; exists m; split; [| split].
    1,2: symmetry; apply readd_remove_prefix with (m2 := all_locks Δ); exact eq.
    reflexivity.
  Qed.

  Lemma add_base_lock : forall Γ, ctxt_equiv Γ (add_lock Γ base).
  Proof using.
    intro Γ; split; [|split]; intros; cbn; try rewrite mod_base_app; reflexivity.
  Qed.

  Lemma add_two_locks : forall Γ m1 m2, ctxt_equiv (add_lock Γ (mod_app m1 m2)) (add_lock (add_lock Γ m2) m1).
  Proof using.
    intros Γ m1 m2; split; [|split]; intros; cbn; try reflexivity; apply mod_app_assoc.
  Qed.
  
  Section ChangeLock.
    
    Program Definition change_lock (Γ : Ctxt) {m1 m2 : mod} (inv : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2) :=
      {|
        vars := vars Γ;
        locks n :=
          match change_prefix m1 (locks Γ n) m2 with
          | Some m => m
          | None => locks Γ n
          end;
        all_locks := match change_prefix m1 (all_locks Γ) m2 with
                    | Some m => m
                    | None => all_locks Γ
                    end
      |}.
    Next Obligation.
      destruct (change_prefix m1 (locks Γ n) m2) eqn:eq0;
        destruct (change_prefix m1 (locks Γ m) m2) eqn:eq1.
      - apply change_prefix_of_prefix' with (m1 := m1) (m3 := m2) (m2 := locks Γ n) (m2' := locks Γ m);
          auto; apply locks_mono; auto.
      - apply only_prefixes_changable in eq0.
        assert (PrefixOf m1 (locks Γ m)) 
          by (transitivity (locks Γ n); [exact eq0 | apply locks_mono; exact H0]).
        exfalso; apply change_prefix_of_prefix in eq1; auto.
      - destruct (inv n);
          [exfalso; apply change_prefix_of_prefix in eq0; auto|].
        apply prefix_changed_to_prefix in eq1.
        transitivity m2; auto.
      - apply locks_mono; exact H0.
    Qed.
    Next Obligation.
      destruct (change_prefix m1 (locks Γ n) m2) eqn:eq0;
        destruct (change_prefix m1 (all_locks Γ) m2) eqn:eq1.
      - apply change_prefix_of_prefix' with (m1 := m1) (m2 := locks Γ n) (m2' := all_locks Γ) (m3 := m2);
          auto; apply locks_bound.
      - exfalso. apply only_prefixes_changable in eq0.
        apply change_prefix_of_prefix in eq1; auto.
        transitivity (locks Γ n); auto. apply locks_bound.
      - destruct (inv n); [exfalso; apply change_prefix_of_prefix in eq0; auto|].
        apply prefix_changed_to_prefix in eq1; transitivity m2; auto.
      - apply locks_bound.
    Qed.

    Lemma inv_ext : forall  {Γ Δ : Ctxt} {m1 m2 : mod},
        ctxt_equiv Γ Δ ->
        (forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2) ->
        forall n, PrefixOf m1 (locks Δ n) \/ PrefixOf (locks Δ n) m2.
    Proof using.
      intros Γ Δ m1 m2 [vars_equiv [locks_equiv al_eqv]] Γ_inv n.
      destruct (Γ_inv n) as [pfx | pfx]; [left | right]; rewrite <- locks_equiv; auto.
    Qed.
    
    Lemma change_lock_inv_ext : forall {Γ : Ctxt} {m1 m2 : mod} (inv1 inv2 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2),
        ctxt_equiv (change_lock Γ inv1) (change_lock Γ inv2).
    Proof using.
      intros Γ m1 m2 inv1 inv2; destruct Γ; cbn in *.
      split; [| split]; try intro x; cbn; auto.
    Qed.

    Lemma change_lock_inv_ext' : forall {Γ : Ctxt} {m1 m2 : mod} (inv1 inv2 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2),
        ctxt_equiv' (change_lock Γ inv1) (change_lock Γ inv2).
    Proof using.
      intros Γ m1 m2 inv1 inv2; apply ctxt_equiv_to_equiv'; apply change_lock_inv_ext.
    Qed.

    Lemma change_lock_ctxt_ext : forall {Γ Δ : Ctxt} {m1 m2 : mod} (inv : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2)
                                        (eqv : ctxt_equiv Γ Δ),
        ctxt_equiv (change_lock Γ inv) (change_lock Δ (inv_ext eqv inv)).
    Proof using.
      intros Γ Δ m1 m2 inv [vars_eqv [locks_eqv al_eqv]].
      split; [| split]; try intro x; cbn; auto.
      rewrite locks_eqv; reflexivity.
      rewrite al_eqv; reflexivity.
    Qed.


    Lemma change_prefix_base : forall m1 m2, change_prefix base m1 m2 = Some (mod_app m2 m1).
    Proof using.
      intros m1; induction m1; intro m2; cbn; eq_bool; subst.
      - reflexivity.
      - inversion eq.
      - rewrite IHm1. reflexivity.
    Qed.

    Lemma change_prefix_mod_app : forall m1 m2 m3 m4 m5,
        change_prefix m1 m2 m3 = Some m4 -> change_prefix m1 (mod_app m2 m5) m3 = Some (mod_app m4 m5).
    Proof using.
      intros m1 m2 m3 m4 m5; revert m1 m2 m3 m4; induction m5; intros m1 m2 m3 m4 eq; cbn in *; eq_bool; subst.
      - exact eq.
      - exfalso. pose proof (only_prefixes_changable _ _ _ _ eq) as pfx.
        apply PrefixOf_size in pfx; cbn in pfx; rewrite mod_app_size in pfx; lia.
      - rewrite IHm5 with (m4 := m4); auto.
    Qed.



    
    (* Lemma change_lock_ctxt_ext' : forall {Γ Δ : Ctxt} {m1 m2 : mod} (inv1 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2) *)
    (*                                 (inv2 : forall n, PrefixOf m1 (locks Δ n) \/ PrefixOf (locks Δ n) m2) *)
    (*                                 (eqv : ctxt_equiv' Γ Δ), *)
    (*     ctxt_equiv' (change_lock Γ inv1) (change_lock Δ inv2). *)
    (* Proof using. *)
    (*   intros Γ Δ m1 m2 inv1 inv2 [vars_eqv [locks_eqv al_eqv]]. *)
    (*   split; [|split]; try intro x; cbn; auto. *)
    (*   - destruct (locks_eqv x) as [m [m' [m_eq [m'_eq m_prime_eq]]]]. *)
    (*     destruct (change_prefix m1 (locks Γ x) m2) eqn:eq1; [rewrite m_eq; rewrite (change_prefix_mod_app _ _ _ _ _ eq1)|]; *)
    (*       destruct (change_prefix m1 (locks Δ x) m2) eqn:eq2. *)
    (*     -- rewrite m'_eq; rewrite (change_prefix_mod_app _ _ _ _ _ eq2). exists m; exists m'; split; [| split]; auto. *)
    (*     -- destruct (change_prefix m1 (all_locks Δ) m2) eqn:eq3. *)
    (*        2: { exists m; exists m'; split; [| split]; auto. } *)
    (*        pose proof (prefix_changed_to_prefix _ _ _ _ eq3) as pfx. *)
    (*        destruct (inv2 x) as [pfx' | pfx']; [apply change_prefix_of_prefix with (m3 := m2) in pfx'; apply pfx' in eq2; destruct eq2|]. *)
    (*        destruct (PrefixOf_peel pfx) as [m3' eq_m3']. *)
    (*        destruct (PrefixOf_peel pfx') as [m2' eq_m2']. *)
    (*        rewrite eq_m2' in eq_m3'. rewrite mod_app_assoc in eq_m3'. *)
    (*        exists m; exists (mod_app m2' m3'); split; [| split]; auto. *)
           

    (*   change_prefix m1 m2 m3 = Some m4 -> change_prefix m1 (mod_app m2 m5) m3 = Some (mod_app m4 m5) *)
    (*   destruct (change_prefix m1 (all_locks Γ) m2) eqn:eq2. *)
    (*   2: { exfalso; apply change_prefix_of_prefix in eq2; auto. rewrite m_eq. transitivity (locks Γ x); auto. apply PrefixOf_app. } *)
      
    (*   rewrite m_eq. *)
      
    (* Admitted. *)

    Lemma change_lock_ext : forall {Γ Δ : Ctxt} {m1 m2 : mod} (inv1 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2)
                              (inv2 : forall n, PrefixOf m1 (locks Δ n) \/ PrefixOf (locks Δ n) m2),
        ctxt_equiv Γ Δ ->
        ctxt_equiv (change_lock Γ inv1) (change_lock Δ inv2).
    Proof using.
      intros Γ Δ m1 m2 inv1 inv2 eqv;
        transitivity (change_lock Δ (inv_ext eqv inv1)); [apply change_lock_ctxt_ext | apply change_lock_inv_ext].
    Qed.

    Lemma change_locks_prefix_pres : forall {Γ : Ctxt} {m1 m2 : mod} {inv : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2}
                                       (n m : nat),
        PrefixOf (locks Γ n) (locks Γ m) ->
        PrefixOf (locks (change_lock Γ inv) n) (locks (change_lock Γ inv) m).
    Proof using.
      intros Γ m1 m2 inv n m pfx; cbn.
      destruct (change_prefix m1 (locks Γ n) m2) eqn:eq1;
        destruct (change_prefix m1 (locks Γ m) m2) eqn:eq2.
      - eapply change_prefix_of_prefix'; eauto.
      - pose proof (only_prefixes_changable _  _ _ _ eq1) as pfx_n.
        exfalso; apply change_prefix_of_prefix in eq2; auto.
        transitivity (locks Γ n); auto.
      - pose proof (only_prefixes_changable _  _ _ _ eq2) as pfx_m.
        destruct (common_suffix _ _ _ pfx pfx_m). 
        2: apply change_prefix_of_prefix in eq1; auto; destruct eq1.
        apply prefix_changed_to_prefix in eq2.
        transitivity m2; auto.
        destruct (inv n); auto.
        apply change_prefix_of_prefix in eq1; auto; destruct eq1.
      - exact pfx.
    Qed.

    Theorem change_lock_inv_send_all : forall {Γ : Ctxt} {m : mod} {p : PName} (q : PName),
        PrefixOf (cons m p) (all_locks Γ) ->
        forall n, PrefixOf (cons m p) (locks Γ n)  \/ PrefixOf (locks Γ n) (cons m q).
    Proof using.
      intros Γ m p q pfx n.
      destruct (common_suffix _ _ _ pfx (locks_bound Γ n)) as [pfx' | pfx']; [left; exact pfx'|].
      inversion pfx'; subst.
      left; reflexivity.
      right; apply PO_step; exact pf.
    Qed.
    
    Theorem change_lock_inv_send : forall {Γ : Ctxt} {m : mod} {p : PName} (q : PName) {seen : nat},
        PrefixOf (cons m p) (locks Γ seen) ->
        forall n, PrefixOf (cons m p) (locks Γ n)  \/ PrefixOf (locks Γ n) (cons m q).
    Proof using.
      intros Γ m p q seen pfx n.
      destruct (PeanoNat.Nat.leb_spec n seen).
      pose proof (locks_mono Γ H0) as prefix_n_seen.
      destruct (common_suffix _ _ _ pfx prefix_n_seen); auto.
      inversion H1; subst; [left; reflexivity | right; apply PO_step; auto].
      left; transitivity (locks Γ seen); [auto | apply locks_mono; apply PeanoNat.Nat.lt_le_incl; auto].
    Qed.

    Theorem change_lock_inv_up_all : forall {Γ : Ctxt} {m : mod} (p : PName),
        PrefixOf m (all_locks Γ) ->
        forall n, PrefixOf m (locks Γ n) \/ PrefixOf (locks Γ n) (cons m p).
    Proof using.
      intros Γ m p pfx n.
      destruct (common_suffix _ _ _ pfx (locks_bound Γ n)) as [pfx' | pfx']; [left; exact pfx'|].
      right; apply PO_step; exact pfx'.
    Qed.

    Theorem change_lock_inv_up : forall {Γ : Ctxt} {m : mod} (p : PName) {seen : nat},
        PrefixOf m (locks Γ seen) ->
        forall n, PrefixOf m (locks Γ n) \/ PrefixOf (locks Γ n) (cons m p).
    Proof using.
      intros Γ m p seen pfx n.
      destruct (PeanoNat.Nat.leb_spec n seen).
      pose proof (locks_mono Γ H0) as pfx'.
      destruct (common_suffix _ _ _ pfx pfx'); auto.
      right; constructor; auto.
      left; transitivity (locks Γ seen); [| apply locks_mono; apply PeanoNat.Nat.lt_le_incl]; auto.
    Qed.

    Theorem change_lock_inv_down_all : forall {Γ : Ctxt} {m : mod} {p : PName},
        PrefixOf (cons m p) (all_locks Γ) ->
        forall n, PrefixOf (cons m p) (locks Γ n) \/ PrefixOf (locks Γ n) m.
    Proof using.
      intros Γ m p pfx n.
      destruct (common_suffix _ _ _ pfx (locks_bound Γ n)) as [pfx' | pfx']; [left; exact pfx'|].
      inversion pfx'; subst.
      left; reflexivity.
      right; exact pf.
    Qed.
    
    Theorem change_lock_inv_down : forall {Γ : Ctxt} {m : mod} {p : PName} {seen : nat},
        PrefixOf (cons m p) (locks Γ seen) ->
        forall n, PrefixOf (cons m p) (locks Γ n) \/ PrefixOf (locks Γ n) m.
    Proof using.
      intros Γ m p seen pfx n.
      destruct (PeanoNat.Nat.leb_spec n seen).
      pose proof (locks_mono Γ H0) as prefix_n_seen.
      destruct (common_suffix _ _ _ pfx prefix_n_seen); auto.
      inversion H1; subst; auto; left; reflexivity.
      left; transitivity (locks Γ seen); [auto | apply locks_mono; apply PeanoNat.Nat.lt_le_incl; auto].
    Qed.

  End ChangeLock.

  Section RemoveLocks.

    Program Definition owner_unqualified (Γ : Ctxt) (x : nat) : mod :=
      match remove_Prefix (locks Γ x) (all_locks Γ) with
      | Some m => mod_app (fst (vars Γ x)) m
      | None => _
      end.
    Next Obligation.
      exfalso; destruct (prefix_remove_Some (locks Γ x) (all_locks Γ) (locks_bound Γ x)) as [m eqm].
      rewrite eqm in Heq_anonymous; inversion Heq_anonymous.
    Defined.

    Definition is_owner_unqual (Γ : Ctxt) (x : nat) (m : mod) : Prop :=
      exists m', mod_app (locks Γ x) m' = all_locks Γ /\
              m = mod_app (fst (vars Γ x)) m'.

    (* This is easily seen to be true, but Coq can't recognize it because of stupidity. *)
    Axiom owner_unqualified_spec : forall Γ x m,
        is_owner_unqual Γ x m <-> owner_unqualified Γ x = m.

    Program Definition remove_locks (Γ : Ctxt) : Ctxt :=
      {|
        vars n := (owner_unqualified Γ n, snd (vars Γ n));
        locks n := base;
        all_locks := base
      |}.
    Next Obligation.
      reflexivity.
    Defined.
    Next Obligation.
      reflexivity.
    Defined.

    Lemma remove_locks_equiv' : forall (Γ : Ctxt),
        ctxt_equiv' Γ (add_lock (remove_locks Γ) (all_locks Γ)).
    Proof using.
      intro Γ; split; [intro x; reflexivity | split; [| reflexivity]]; cbn.
      intro x.
      destruct (prefix_remove_Some (locks Γ x) (all_locks Γ) (locks_bound Γ x)) as [m eqm].
      exists m; exists base; split; [| split; [cbn; reflexivity|]].
      - symmetry; apply readd_remove_prefix; exact eqm.
      - assert (is_owner_unqual Γ x (mod_app (fst (vars Γ x)) m)) as ou by (exists m; split; auto; apply readd_remove_prefix; exact eqm).
        rewrite owner_unqualified_spec in ou. rewrite ou.
        rewrite mod_app_base. reflexivity.
    Qed.
      
  End RemoveLocks.

  Section LockChanging.
    Definition ctxt_ren (Γ : Ctxt) (ξ : renaming) (mono : forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m))): Ctxt :=
      {|
        vars n := vars Γ (ξ n);
        locks n := locks Γ (ξ n);
        all_locks := all_locks Γ;
        locks_mono n m lt := mono n m lt;
        locks_bound n := locks_bound Γ (ξ n);
      |}.

    Lemma ctxt_ren_ext : forall Γ ξ mono mono',
        ctxt_equiv (ctxt_ren Γ ξ mono) (ctxt_ren Γ ξ mono').
    Proof using.
      intros Γ ξ mono mono'; split; [| split]; cbn; reflexivity.
    Qed.

    Lemma renup_mono : forall (ξ : renaming) (Γ : Ctxt) g τ, (forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m))) ->
                                                        forall n m, n <= m -> PrefixOf (locks (add_var Γ g τ) (renup ξ n)) (locks (add_var Γ g τ) (renup ξ m)).
    Proof using.
      intros ξ Γ g τ mono n m n_le_m.
      destruct n; destruct m; cbn.
      - constructor.
      - apply PrefixOf_base.
      - inversion n_le_m.
      - apply mono; apply le_S_n; exact n_le_m.
    Qed.

    Lemma lock_ren_mono : forall (ξ : renaming) (Γ : Ctxt) p, (forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m))) ->
                                                     forall n m, n <= m -> PrefixOf (locks (add_lock Γ p) (ξ n)) (locks (add_lock Γ p) (ξ m)).
    Proof using.
      intros ξ Γ p mono n m n_le_m.
      cbn. apply PrefixOf_app_mono; auto.
    Qed.

    Lemma renup_nochange : forall ξ l, (forall n, n <= l -> ξ n = n) -> forall n, n <= S l -> renup ξ n = n.
    Proof using.
      intros ξ l nochange n n_le_Sl; destruct n; cbn; auto.
      apply le_S_n in n_le_Sl. rewrite nochange. reflexivity. exact n_le_Sl.
    Qed.

    Lemma renup_nochange' : forall ξ l, (forall n, n < l -> ξ n = n) -> forall n, n < S l -> renup ξ n = n.
    Proof using.
      intros ξ l nochange n n_lt_Sl; destruct n; cbn; auto.
      apply PeanoNat.lt_S_n in n_lt_Sl. rewrite nochange. reflexivity. exact n_lt_Sl.
    Qed.

    Lemma nolocks_change_mono : forall {Γ : Ctxt} {ξ : renaming},
        (forall n, locks Γ n = locks Γ (ξ n)) ->
        forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m)).
    Proof using.
      intros Γ ξ H0 n m H1; repeat rewrite <- H0; apply locks_mono; exact H1.
    Qed.

    Lemma mono_mono_locks : forall (Γ : Ctxt) (ξ : renaming),
        (forall n m, n <= m -> ξ n <= ξ m) -> forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m)).
    Proof using.
      intros Γ ξ H0 n m H1; apply locks_mono; apply H0; exact H1.
    Qed.

    Lemma mono_renup : forall ξ, (forall n m, n <= m -> ξ n <= ξ m) -> forall n m, n <= m -> renup ξ n <= renup ξ m.
    Proof using.
      intros ξ mono n m n_le_m.
      destruct n; cbn; [apply le_0_n|].
      destruct m; cbn; [inversion n_le_m|].
      apply le_S_n in n_le_m; apply le_n_S; apply mono; exact n_le_m.
    Qed.

    Lemma add_mono : forall n x y, x <= y -> x + n <= y + n. Proof using. lia. Qed.

  End LockChanging.
  
  Section FiniteContexts.
      Inductive FiniteCtxt : Type :=
    | emptyFC : FiniteCtxt
    | varFC (m : mod) (τ : type) (Δ : FiniteCtxt) : FiniteCtxt
    | lockFC (m : mod) (Δ : FiniteCtxt) : FiniteCtxt.

    Fixpoint FiniteCtxt_eqb (Γ Δ : FiniteCtxt) : bool :=
      match Γ, Δ with
      | emptyFC, emptyFC => true
      | varFC m1 τ1 Γ', varFC m2 τ2 Δ' => eqb m1 m2 && eqb τ1 τ2 && FiniteCtxt_eqb Γ' Δ'
      | lockFC m1 Γ', lockFC m2 Δ' => eqb m1 m2 && FiniteCtxt_eqb Γ' Δ'
      | _, _ => false 
      end.

    #[global] Program Instance FiniteCtxtEqBool : EqBool FiniteCtxt :=
      {
        eqb := FiniteCtxt_eqb;
      }.
    Next Obligation.
      revert y H0; solve_eqb_liebniz x.
    Defined.
    Next Obligation.
      solve_eqb_refl.
    Defined.

    Fixpoint FiniteCtxtSize (Δ : FiniteCtxt) : nat :=
      match Δ with
      | emptyFC => 0
      | varFC _ _ Δ => S (FiniteCtxtSize Δ)
      | lockFC _ Δ => FiniteCtxtSize Δ
      end.

    Fixpoint addFiniteCtxt (Γ : Ctxt) (Δ : FiniteCtxt) : Ctxt :=
      match Δ with
      | emptyFC => Γ
      | varFC m τ Δ => addFiniteCtxt (add_var Γ m τ) Δ
      | lockFC m Δ => addFiniteCtxt (add_lock Γ m) Δ
      end.

    Fixpoint vars_of_finite_ctxt (Δ : FiniteCtxt) : list (mod * type) :=
      match Δ with
      | emptyFC => nil
      | varFC m τ Δ => List.app (vars_of_finite_ctxt Δ) (List.cons (m, τ) nil)
      | lockFC m Δ => vars_of_finite_ctxt Δ
      end.

    Definition nth_var (Δ : FiniteCtxt) (n : nat) := List.nth_error (vars_of_finite_ctxt Δ) n.

    Lemma vars_of_finite_ctxt_size : forall Δ, FiniteCtxtSize Δ = List.length (vars_of_finite_ctxt Δ).
    Proof using.
      intro Δ; induction Δ; cbn; [reflexivity | |]; rewrite IHΔ; [| reflexivity].
      rewrite length_app; cbn. rewrite PeanoNat.Nat.add_1_r. reflexivity.
    Qed.

    Lemma nth_var_size1 : forall Δ n, n < FiniteCtxtSize Δ -> exists m τ, nth_var Δ n = Some (m, τ).
    Proof using.
      intros Δ n n_lt_size.
      destruct (nth_var Δ n) as [[m τ]|] eqn:eq; [exists m; exists τ; reflexivity|].
      apply nth_error_None in eq; rewrite vars_of_finite_ctxt_size in n_lt_size; lia.
    Qed.

    Lemma nth_var_size2 : forall Δ n, FiniteCtxtSize Δ <= n -> nth_var Δ n = None.
    Proof using.
      intros Δ n n_lt_size.
      destruct (nth_var Δ n) as [pr|] eqn:eq;[|reflexivity].
      unfold nth_var in eq.
      assert (nth_error (vars_of_finite_ctxt Δ) n <> None) as neq by (intro eq'; rewrite eq' in eq; inversion eq).
      apply nth_error_Some in neq. rewrite vars_of_finite_ctxt_size in n_lt_size. lia.
    Qed.

    Lemma vars_past_finite_ctxt : forall Γ Δ n,
        FiniteCtxtSize Δ <= n ->
        vars (addFiniteCtxt Γ Δ) n = vars Γ (n - FiniteCtxtSize Δ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ n size_le_n; cbn in *.
      - rewrite PeanoNat.Nat.sub_0_r; reflexivity.
      - specialize (IHΔ (add_var Γ m τ) n ltac:(lia)); rewrite IHΔ.
        destruct n; [lia|]. rewrite PeanoNat.Nat.sub_succ_l; [|lia]. rewrite PeanoNat.Nat.sub_succ.
        reflexivity.
      - rewrite IHΔ; cbn; [reflexivity | exact size_le_n].
    Qed.        

    Lemma nth_var_add_ctxt : forall Γ Δ n pr,
        nth_var Δ n = Some pr ->
        vars (addFiniteCtxt Γ Δ) n = pr.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ n pr eq; unfold nth_var in eq; cbn in *.
      - destruct n; cbn in eq; inversion eq.
      - assert (n < (length (vars_of_finite_ctxt Δ ++ [(m, τ)]))) as n_lt_length
            by (apply nth_error_Some; rewrite eq; discriminate).
        rewrite length_app in n_lt_length; cbn in n_lt_length.
        rewrite PeanoNat.Nat.add_1_r in n_lt_length.
        apply PeanoNat.lt_n_Sm_le in n_lt_length.
        destruct (Compare_dec.le_lt_eq_dec _ _ n_lt_length) as [l|l].
        -- apply nth_error_app1 with (l' := [(m, τ)]) in l; rewrite eq in l; symmetry in l.
           apply IHΔ with (Γ := add_var Γ m τ) in l. exact l.
        -- assert (length (vars_of_finite_ctxt Δ) <= n) as l' by (apply PeanoNat.Nat.eq_le_incl; auto).
           apply nth_error_app2 with (l' := [(m, τ)]) in l'; rewrite eq in l'; symmetry in l'; subst.
           rewrite PeanoNat.Nat.sub_diag in l'; cbn in l'; inversion l'; subst.
           rewrite vars_past_finite_ctxt; rewrite vars_of_finite_ctxt_size; [| reflexivity].
           rewrite PeanoNat.Nat.sub_diag; reflexivity.
      - apply IHΔ. unfold nth_var; auto.
    Qed.

    Lemma vars_in_finite_ctxt : forall Γ Δ n,
        n < FiniteCtxtSize Δ ->
        nth_var Δ n = Some (vars (addFiniteCtxt Γ Δ) n).
    Proof using.
      intros Γ Δ n H0.
      destruct (nth_var Δ n) eqn:eq.
      rewrite nth_var_add_ctxt with (pr := p); auto.
      unfold nth_var in eq; apply nth_error_None in eq; rewrite vars_of_finite_ctxt_size in H0; lia.
    Qed.

    Fixpoint FiniteCtxtLocks (Δ : FiniteCtxt) : mod :=
      match Δ with
      | emptyFC => base
      | varFC _ _ Δ => FiniteCtxtLocks Δ
      | lockFC m Δ => mod_app (FiniteCtxtLocks Δ) m
      end.

    Fixpoint locks_at_finite_ctxt_vars (Δ : FiniteCtxt) :=
      match Δ with
      | emptyFC => nil
      | varFC _ _ Δ => locks_at_finite_ctxt_vars Δ ++ [FiniteCtxtLocks Δ]
      | lockFC _ Δ => locks_at_finite_ctxt_vars Δ
      end.

    Lemma locks_at_finite_ctxt_vars_size : forall Δ, length (locks_at_finite_ctxt_vars Δ) = FiniteCtxtSize Δ.
    Proof using.
      intro Δ; induction Δ; cbn; auto; rewrite length_app; cbn; lia.
    Qed.

    Definition locks_at (Δ : FiniteCtxt) (x : nat) := nth_error (locks_at_finite_ctxt_vars Δ) x.

    Theorem AddFiniteCtxt_AllLocks : forall (Γ : Ctxt) (Δ : FiniteCtxt),
        all_locks (addFiniteCtxt Γ Δ) = mod_app (FiniteCtxtLocks Δ) (all_locks Γ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intro Γ; cbn; try (rewrite IHΔ; cbn); symmetry;
        [ apply mod_base_app | reflexivity | apply mod_app_assoc].
    Qed.

    Theorem AddFiniteCtxt_locks1 : forall (Γ : Ctxt) (Δ : FiniteCtxt) (x : nat),
        (FiniteCtxtSize Δ) <= x ->
        locks (addFiniteCtxt Γ Δ) x = mod_app (FiniteCtxtLocks Δ) (locks Γ (x - FiniteCtxtSize Δ)).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ x size_le_x; cbn in *.
      - rewrite PeanoNat.Nat.sub_0_r. symmetry; apply mod_base_app.
      - rewrite IHΔ; [| lia]. f_equal.
        destruct x; [inversion size_le_x|]; cbn.
        destruct (FiniteCtxtSize Δ) eqn:eq_size.
        -- rewrite PeanoNat.Nat.sub_0_r; reflexivity.
        -- destruct (x - n) eqn:eq_n'. exfalso; lia.
           assert (x - S n = n0) as eq by lia; rewrite eq; reflexivity.
      - rewrite IHΔ; [| exact size_le_x].
        rewrite mod_app_assoc; reflexivity.
    Qed.

    Theorem AddFiniteCtxt_locks2 : forall (Γ : Ctxt) (Δ : FiniteCtxt) (x : nat),
        x < FiniteCtxtSize Δ ->
        Some (locks (addFiniteCtxt Γ Δ) x) = locks_at Δ x.
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ x x_lt_size; cbn in *.
      - inversion x_lt_size.
      - pose proof (PeanoNat.lt_n_Sm_le _ _ x_lt_size) as x_le_size.
        destruct (Compare_dec.le_lt_eq_dec _ _ x_le_size).
        -- rewrite IHΔ; auto.
           unfold locks_at at 2; cbn; rewrite nth_error_app1; [|rewrite locks_at_finite_ctxt_vars_size; auto].
           unfold locks_at; reflexivity.
        -- rewrite AddFiniteCtxt_locks1; [| subst; reflexivity].
           rewrite e at 1; rewrite PeanoNat.Nat.sub_diag. cbn.
           unfold locks_at; cbn; rewrite nth_error_app2; [|rewrite locks_at_finite_ctxt_vars_size; lia].
           rewrite e; rewrite locks_at_finite_ctxt_vars_size; rewrite PeanoNat.Nat.sub_diag; cbn.
           reflexivity.
      - apply IHΔ; auto.
    Qed.

    Theorem extend_rename : forall (Γ : Ctxt) (Δ : FiniteCtxt),
        ctxt_equiv (ctxt_ren (addFiniteCtxt Γ Δ) (fun n => n + FiniteCtxtSize Δ) (mono_mono_locks (addFiniteCtxt Γ Δ)  (fun n => n + FiniteCtxtSize Δ) (add_mono (FiniteCtxtSize Δ))))
          (add_lock Γ (FiniteCtxtLocks Δ)).
    Proof using.
      intros Γ Δ; split; [| split]; try intro x; cbn.
      - rewrite vars_past_finite_ctxt; [| lia].
        assert (x + FiniteCtxtSize Δ - FiniteCtxtSize Δ = x) as e by lia; rewrite e; reflexivity.
      - rewrite (AddFiniteCtxt_locks1 Γ Δ (x + FiniteCtxtSize Δ)); [| lia].
        assert (x + FiniteCtxtSize Δ - FiniteCtxtSize Δ = x) as e by lia; rewrite e; reflexivity.
      - apply AddFiniteCtxt_AllLocks.
    Qed.

    Fixpoint add_end_var (Δ : FiniteCtxt) (m : mod) (τ : type) : FiniteCtxt :=
      match Δ with
      | emptyFC => varFC m τ emptyFC
      | varFC m' τ' Δ => varFC m' τ' (add_end_var Δ m τ)
      | lockFC m' Δ => lockFC m' (add_end_var Δ m τ)
      end.

    Theorem add_end_var_eqv : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m : mod) (τ : type),
        ctxt_equiv (addFiniteCtxt Γ (add_end_var Δ m τ)) (add_var (addFiniteCtxt Γ Δ) m τ).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ m' τ'; cbn; try rewrite IHΔ; reflexivity.
    Qed.

    Lemma add_end_var_size : forall Δ m τ, FiniteCtxtSize (add_end_var Δ m τ) = S (FiniteCtxtSize Δ).
    Proof using.
      intro Δ; induction Δ; intros m' τ'; cbn; try rewrite IHΔ; reflexivity.
    Qed.
    
    Fixpoint add_end_lock (Δ : FiniteCtxt) (m : mod) : FiniteCtxt :=
      match Δ with
      | emptyFC => lockFC m emptyFC
      | varFC m' τ Δ => varFC m' τ (add_end_lock Δ m)
      | lockFC m' Δ => lockFC m' (add_end_lock Δ m)
      end.

    Theorem add_end_lock_eqv : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m : mod),
        ctxt_equiv (addFiniteCtxt Γ (add_end_lock Δ m)) (add_lock (addFiniteCtxt Γ Δ) m).
    Proof using.
      intros Γ Δ; revert Γ; induction Δ; intros Γ lck; cbn; try rewrite IHΔ; reflexivity.
    Qed.

    Lemma add_end_lock_size : forall Δ m, FiniteCtxtSize (add_end_lock Δ m) = FiniteCtxtSize Δ.
    Proof using.
      intro Δ; induction Δ; intro m'; cbn; try rewrite IHΔ; reflexivity.
    Qed.

    Fixpoint FiniteChangeLock (Δ : FiniteCtxt) (m1 m2 : mod) : option FiniteCtxt :=
      match Δ with
      | emptyFC => Some emptyFC
      | varFC m τ Δ =>
          match FiniteChangeLock Δ m1 m2 with
          | Some Δ => Some (varFC m τ Δ)
          | None => None
          end
      | lockFC m Δ =>
          match change_prefix m1 m m2 with
          | Some m' => Some (lockFC m' Δ)
          | None =>
              match remove_Prefix m m1, remove_Prefix m m2 with
              | Some m1', Some m2' =>
                  match FiniteChangeLock Δ m1' m2' with
                  | Some Δ => Some (lockFC m Δ)
                  | None => None
                  end 
              | _, _ => None
              end
          end
      end.

    Lemma change_lock_before_finite_ctxt_inv: forall (Γ : Ctxt) (Δ : FiniteCtxt) (m1 m2 m1' m2' : mod)
                                            (inv : forall n, PrefixOf m1 (locks (addFiniteCtxt Γ Δ) n) \/ PrefixOf (locks (addFiniteCtxt Γ Δ) n) m2),
        m1 = mod_app (FiniteCtxtLocks Δ) m1' ->
        m2 = mod_app (FiniteCtxtLocks Δ) m2' ->
        forall n, PrefixOf m1' (locks Γ n) \/ PrefixOf (locks Γ n) m2'.
    Proof using.
      intros Γ Δ m1 m2 m1' m2' inv eq1 eq2 n.
      destruct (inv (n + FiniteCtxtSize Δ)) as [pfx | pfx]; rewrite AddFiniteCtxt_locks1 in pfx; try lia; rewrite PeanoNat.Nat.add_sub in pfx.
      - left. rewrite eq1 in pfx. apply mod_app_prefix with (m1 := FiniteCtxtLocks Δ); exact pfx.
      - right. rewrite eq2 in pfx. apply mod_app_prefix with (m1 := FiniteCtxtLocks Δ); exact pfx.
    Qed.

    Lemma FiniteCtxtLocks_LocksAt : forall (Δ : FiniteCtxt) (m : mod) (x : nat),
        locks_at Δ x = Some m ->
        PrefixOf m (FiniteCtxtLocks Δ).
    Proof using.
      intros Δ; induction Δ as [| m' τ Δ IHΔ | m' Δ IHΔ]; intros m x eq; unfold locks_at in eq; cbn in *.
      - destruct x; cbn in eq; inversion eq.
      - destruct (Compare_dec.lt_eq_lt_dec (FiniteCtxtSize Δ) x) as [[size_lt_x | size_eq_x] | x_lt_size].
        -- rewrite nth_error_app2 in eq; [|rewrite locks_at_finite_ctxt_vars_size; lia].
           destruct (x - length (locks_at_finite_ctxt_vars Δ)) eqn:eq'.
           rewrite locks_at_finite_ctxt_vars_size in eq'; exfalso; lia.
           cbn in eq; destruct n; inversion eq.
        -- rewrite nth_error_app2 in eq; [|rewrite locks_at_finite_ctxt_vars_size; lia].
           rewrite locks_at_finite_ctxt_vars_size in eq. rewrite size_eq_x in eq. rewrite PeanoNat.Nat.sub_diag in eq. cbn in eq; inversion eq.
           reflexivity.
        -- rewrite nth_error_app1 in eq; [| rewrite locks_at_finite_ctxt_vars_size; exact x_lt_size].
           apply IHΔ with (x := x); unfold locks_at; exact eq.
      - transitivity (FiniteCtxtLocks Δ). eapply IHΔ; eauto.
        apply PrefixOf_app.
    Qed.
    
    Lemma change_lock_before_finite_ctxt : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m1 m2 m1' m2' : mod)
                                                         (inv : forall n, PrefixOf m1 (locks (addFiniteCtxt Γ Δ) n) \/ PrefixOf (locks (addFiniteCtxt Γ Δ) n) m2)
                                                         (eq1 : m1 = mod_app (FiniteCtxtLocks Δ) m1')
                                                         (eq2 : m2 = mod_app (FiniteCtxtLocks Δ) m2'),
        m1' <> base ->
        ctxt_equiv (change_lock (addFiniteCtxt Γ Δ) inv)
          (addFiniteCtxt (change_lock Γ (change_lock_before_finite_ctxt_inv Γ Δ m1 m2 m1' m2' inv eq1 eq2)) Δ).
    Proof using.
      intros Γ Δ m1 m2 m1' m2' inv eq1 eq2 neq; split; [| split].
      - intro x. cbn.
        destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) x) as [size_le_x | x_lt_size].
        -- repeat (rewrite vars_past_finite_ctxt; [|exact size_le_x]); reflexivity.
        -- pose proof (vars_in_finite_ctxt Γ Δ x x_lt_size) as H0;
             pose proof (vars_in_finite_ctxt (change_lock Γ (change_lock_before_finite_ctxt_inv Γ Δ m1 m2 m1' m2' inv eq1 eq2)) Δ x x_lt_size) as H1.
           rewrite H1 in H0; inversion H0; reflexivity.
      - intro x.
        destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) x) as [size_le_x | x_lt_size].
        -- repeat (rewrite AddFiniteCtxt_locks1; [| exact size_le_x]).
           cbn.
           rewrite (change_common_prefix _ (locks (addFiniteCtxt Γ Δ) x) _ _ _ _ _ eq1 (AddFiniteCtxt_locks1 Γ Δ x size_le_x) eq2).
           destruct (change_prefix m1' (locks Γ (x - FiniteCtxtSize Δ)) m2') eqn:eq.
           reflexivity.
           apply AddFiniteCtxt_locks1; auto.
        -- pose proof (AddFiniteCtxt_locks2 (change_lock Γ (change_lock_before_finite_ctxt_inv Γ Δ m1 m2 m1' m2' inv eq1 eq2)) Δ x x_lt_size) as H0.
           pose proof (AddFiniteCtxt_locks2 Γ Δ x x_lt_size) as H1.
           rewrite <- H1 in H0; inversion H0.
           cbn. rewrite H3.
           destruct (change_prefix m1 (locks (addFiniteCtxt Γ Δ) x) m2) eqn:eq; [| reflexivity].
           pose proof (only_prefixes_changable _ _ _ _ eq).
           assert (PrefixOf (FiniteCtxtLocks Δ) m1) as H4 by (rewrite eq1; apply PrefixOf_app).
           symmetry in H1; apply FiniteCtxtLocks_LocksAt in H1.
           assert (PrefixOf (FiniteCtxtLocks Δ) (locks (addFiniteCtxt Γ Δ) x)) as H5 by (etransitivity; eauto).
           pose proof (PrefixOf_antisym H1 H5) as H6.
           rewrite H6 in H2. pose proof (PrefixOf_antisym H2 H4) as H7. clear H0 H3; rewrite H7 in eq1.
           apply mod_app_id_inv in eq1. destruct (neq eq1).
      - rewrite AddFiniteCtxt_AllLocks.  cbn. rewrite AddFiniteCtxt_AllLocks.
        rewrite (change_common_prefix _ _ _ _ _ (all_locks Γ) _ eq1 eq_refl eq2).
        destruct (change_prefix m1' (all_locks Γ) m2') eqn:eq; reflexivity.
    Qed.

    Lemma change_lock_after_finite_ctxt : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m1 m2 m1' m2' : mod)
                                                         (inv : forall n, PrefixOf m1 (locks (addFiniteCtxt Γ Δ) n) \/ PrefixOf (locks (addFiniteCtxt Γ Δ) n) m2),
        PrefixOf m1 (locks
        ctxt_equiv (change_lock (addFiniteCtxt Γ Δ) inv)
          (addFiniteCtxt (change_lock Γ (change_lock_before_finite_ctxt_inv Γ Δ m1 m2 m1' m2' inv eq1 eq2)) Δ).
           
    End FiniteContexts.
  
End Contexts.
