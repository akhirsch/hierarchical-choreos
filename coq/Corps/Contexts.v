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
  #[local] Notation mod := (@mod PName).
  #[local] Definition ptm := @proc_to_mod PName.
  #[local] Definition PrefixOfT := @PrefixOfT PName.
  Coercion ptm : PName >-> mod.
  #[local] Notation type := (type PName).
  #[local] Notation expr := (expr PName).

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

  Lemma add_base_lock : forall Γ, ctxt_equiv Γ (add_lock Γ base).
  Proof using.
    intro Γ; split; [|split]; intros; cbn; try rewrite mod_base_app; reflexivity.
  Qed.

  Lemma add_two_locks : forall Γ m1 m2, ctxt_equiv (add_lock Γ (mod_app m1 m2)) (add_lock (add_lock Γ m2) m1).
  Proof using.
    intros Γ m1 m2; split; [|split]; intros; cbn; try reflexivity; apply mod_app_assoc.
  Qed.


  
  Section Lockpointer.

    Record lockpointer (Γ : Ctxt) (m : mod) :=
      {
        index : nat;
        prefix : mod;
        pred_index : (index = 0 /\ prefix = base) \/ (exists k, index = S k /\ locks Γ k = prefix);
        at_index : locks Γ index = mod_app prefix m
      }.

    Lemma before_index : forall (Γ : Ctxt) (m : mod) (ptr : lockpointer Γ m) (n : nat),
        n < index Γ m ptr ->
        PrefixOf (locks Γ n) (prefix Γ m ptr).
    Proof using.
      intros Γ m ptr n n_lt_index.
      destruct (pred_index Γ m ptr) as [[eq0 eq_base] | [k [eqS eq_locks]]].
      - rewrite eq0 in n_lt_index; inversion n_lt_index.
      - transitivity (locks Γ k).
        -- apply locks_mono; rewrite eqS in n_lt_index; apply PeanoNat.lt_n_Sm_le; exact n_lt_index.
        -- rewrite eq_locks; reflexivity.
    Qed.

    
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

    Lemma change_lock_ctxt_ext : forall {Γ Δ : Ctxt} {m1 m2 : mod} (inv : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2)
                                        (eqv : ctxt_equiv Γ Δ),
        ctxt_equiv (change_lock Γ inv) (change_lock Δ (inv_ext eqv inv)).
    Proof using.
      intros Γ Δ m1 m2 inv [vars_eqv [locks_eqv al_eqv]].
      split; [| split]; try intro x; cbn; auto.
      rewrite locks_eqv; reflexivity.
      rewrite al_eqv; reflexivity.
    Qed.

    Lemma change_lock_ext : forall {Γ Δ : Ctxt} {m1 m2 : mod} (inv1 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2)
                              (inv2 : forall n, PrefixOf m1 (locks Δ n) \/ PrefixOf (locks Δ n) m2),
        ctxt_equiv Γ Δ ->
        ctxt_equiv (change_lock Γ inv1) (change_lock Δ inv2).
    Proof using.
      intros Γ Δ m1 m2 inv1 inv2 eqv;
        transitivity (change_lock Δ (inv_ext eqv inv1)); [apply change_lock_ctxt_ext | apply change_lock_inv_ext].
    Qed.
    
    Theorem change_lock_inv_send : forall {Γ : Ctxt} {m : mod} {p : PName} (q : PName) {seen : nat},
        locks Γ seen = cons m p ->
        forall n, PrefixOf (cons m p) (locks Γ n)  \/ PrefixOf (locks Γ n) (cons m q).
    Proof using.
      intros Γ m p q seen seen_cons n.
      destruct (PeanoNat.Nat.leb_spec n seen).
      pose proof (locks_mono Γ H0) as prefix_n_seen; dependent destruction prefix_n_seen.
      - left; rewrite x; rewrite seen_cons; reflexivity.
      - rewrite seen_cons in x; inversion x; subst; clear x.
        right. apply PO_step. exact prefix_n_seen.
      - left; transitivity (locks Γ seen). rewrite seen_cons; reflexivity.
        apply locks_mono; apply PeanoNat.Nat.lt_le_incl; exact H0.
    Qed.           

    Theorem change_lock_inv_up : forall {Γ : Ctxt} {m : mod} (p : PName) {seen : nat},
        locks Γ seen = m ->
        forall n, PrefixOf m (locks Γ n) \/ PrefixOf (locks Γ n) (cons m p).
    Proof using.
      intros Γ m p seen seen_cons n.
      destruct (PeanoNat.Nat.leb_spec n seen) as [n_le_seen | seen_lt_n].
      - pose proof (locks_mono Γ n_le_seen) as prefix_n_seen; dependent destruction prefix_n_seen.
        -- left; rewrite <- seen_cons; rewrite <- x; reflexivity.
        -- rewrite seen_cons in x; inversion x; subst.
           right; do 2 apply PO_step; exact prefix_n_seen.
      - left; transitivity (locks Γ seen). rewrite seen_cons; reflexivity.
        apply locks_mono; apply PeanoNat.Nat.lt_le_incl; exact seen_lt_n.
    Qed.

    Theorem change_lock_inv_down : forall {Γ : Ctxt} {m : mod} {p : PName} {seen : nat},
        locks Γ seen = cons m p ->
        forall n, PrefixOf (cons m p) (locks Γ n) \/ PrefixOf (locks Γ n) m.
    Proof using.
      intros Γ m p seen locks_seen n.
      destruct (PeanoNat.Nat.leb_spec n seen) as [n_le_seen | seen_lt_n].
      - pose proof (locks_mono Γ n_le_seen) as prefix_n_seen; dependent destruction prefix_n_seen.
        -- left; rewrite <- locks_seen; rewrite <- x; reflexivity.
        -- rewrite locks_seen in x; inversion x; subst; clear x.
           right; auto.
      - left; transitivity (locks Γ seen). rewrite locks_seen; reflexivity.
        apply locks_mono; apply PeanoNat.Nat.lt_le_incl; exact seen_lt_n.
    Qed.    

  End Lockpointer.

End Contexts.
