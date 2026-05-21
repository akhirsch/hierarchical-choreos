Require Import EqBool.
Require Import Modalities.
Require Import Syntax.
Require Import Contexts.
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
  #[local] Abbreviation Ctxt := (@Ctxt PName).
  #[local] Definition ptm := @proc_to_mod PName.
  Coercion ptm : PName >-> mod.
  Context {CanSend CanUp CanDown : mod -> mod -> Prop}.
  
  Section TypeSystem.

    Inductive Typed : Ctxt -> expr -> type -> Prop :=
    | VarTyping {Γ : Ctxt} {n : nat} {τ : type} (m : mod) (i : InCtxt n m τ m Γ)
      : Typed Γ (var n) τ
    | UnitTyping (Γ : Ctxt) : Typed Γ uu UnitT
    | AtTyping {Γ : Ctxt} {e : expr} {τ : type} (p : PName) (pf : Typed (LockExt Γ p) e τ)
      : Typed Γ (atE p e) (AtT p τ)
    | LetTyping {Γ : Ctxt} {e1 e2 : expr} {τ1 τ2 : type} {p : PName}
        (pf1 : Typed Γ e1 (AtT p τ1)) (pf2 : Typed (VarExt Γ p τ1) e2 τ2)
      : Typed Γ (letAt p e1 e2) τ2
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
    | CaseTyping {Γ : Ctxt} {e1 e2 e3 : expr} {τ1 τ2 τ3 : type}
        (pf1 : Typed Γ e1 (PlusT τ1 τ2))
        (pf2 : Typed (VarExt Γ base τ1) e2 τ3)
        (pf3 : Typed (VarExt Γ base τ2) e3 τ3)
      : Typed Γ (caseE e1 e2 e3) τ3
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
    | SendTyping {Γ Δ : Ctxt} {m : mod} {p q : PName} {e : expr} {τ : type} {n : nat}
        (eq : change_lock_after Γ m p q = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanSend (cons m p) (cons m q))
        (clsd : closed_below e n)
        (eq' : lock_location Γ (cons m p) = Some n)
      : Typed Γ (send e m p q) τ
    | UpTyping {Γ Δ : Ctxt} {m : mod} {p : PName} {e : expr} {τ : type} {n : nat}
        (eq : remove_lock_after Γ m p = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanUp m (cons m p))
        (clsd : closed_below e n)
        (eq' : lock_location Γ (cons m p) = Some n)
      : Typed Γ (up e m p) τ
    | DownTyping {Γ Δ : Ctxt} {m : mod} {p : PName} {e : expr} {τ : type} {n : nat}
        (eq : add_lock_after Γ m p = Some Δ)
        (pf : Typed Δ e τ)
        (cs : CanDown (cons m p) m)
        (clsd : closed_below e n)
        (eq' : lock_location Γ m = Some n)
      : Typed Γ (down e m p) τ
    .

        
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
        destruct (@change_lock_after_defined _ _ Δ m p q pfx) as [E eqE].
        apply @SendTyping with (Δ := E) (n := n); auto. apply IHtyp; auto.
        apply (change_lock_equiv eqv eq eqE).
        rewrite <- (lock_location_proper (cons m p) eqv); assumption.
      - pose proof (remove_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (remove_lock_after_defined pfx) as [E eqE].
        apply @UpTyping with (Δ := E) (n := n); auto. apply IHtyp; auto.
        apply (remove_lock_equiv eqv eq eqE).
        rewrite <- (lock_location_proper (cons m p) eqv); assumption.
      - pose proof (add_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (@add_lock_after_defined _ _ Δ m p pfx) as [E eqE].
        apply @DownTyping with (Δ := E) (n := n); auto. apply IHtyp; auto.
        apply (add_lock_equiv eqv eq eqE).
        rewrite <- (lock_location_proper m eqv); assumption.
    Qed.

    Theorem Typed_proper : forall Γ Δ, ctxt_equiv Γ Δ -> forall e τ, Typed Γ e τ <-> Typed Δ e τ.
    Proof using.
      intros Γ Δ H0 e τ; split; intro H1; [| symmetry in H0]; eapply Typed_proper'; eassumption.
    Qed.

    Lemma Typed_closed_above : forall {Γ : Ctxt} {e : expr} {τ : type},
        Typed Γ e τ ->
        closed_above e (num_vars Γ).
    Proof using.
      intros Γ e τ typ; induction typ; cbn; try (econstructor; eauto; fail).
      - apply InCtxt_lt in i; constructor; assumption.
      - constructor; rewrite (change_lock_after_num_vars eq); assumption.
      - constructor; rewrite (remove_lock_after_num_vars eq); assumption.
      - constructor; rewrite (add_lock_after_num_vars eq); assumption.
    Qed.

    Theorem weakening : forall {Γ Δ : Ctxt} {ξ : renaming} (lq : ctxt_leq Γ ξ Δ)
                          (e : expr) (τ : type),
        Typed Γ e τ ->
        Typed Δ (ren e ξ) τ.
    Proof using.
      intros Γ Δ ξ lq e τ typ; revert Δ ξ lq; induction typ; intros E ξ lq; cbn;
        try (econstructor; eauto; fail).
      - econstructor; apply (Inctxt_leq lq); exact i.
      - constructor. specialize (IHtyp (LockExt E p) ξ (LockExtLeq p lq)).
        cbn in IHtyp. assumption.
      - econstructor. apply IHtyp1; auto.
        specialize (IHtyp2 (VarExt E p τ1) (renup ξ) (VarExtLeq p τ1 (fun n => eq_refl) lq)).
        cbn in IHtyp2. assumption.
      - econstructor. apply IHtyp1; assumption.
        specialize (IHtyp2 (VarExt E base τ1) (renup ξ) (VarExtLeq base τ1 (fun n => eq_refl) lq));
          cbn in IHtyp2; assumption.
        specialize (IHtyp3 (VarExt E base τ2) (renup ξ) (VarExtLeq base τ2 (fun n => eq_refl) lq));
          cbn in IHtyp3; assumption.
      - constructor;
          specialize (IHtyp (VarExt E base τ1) (renup ξ) (VarExtLeq base τ1 (fun n => eq_refl) lq));
          cbn in IHtyp; assumption.
      - pose proof (change_lock_after_prefix eq).
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (@change_lock_after_defined PName _ E m p q H0) as [Δ' eq''].
        pose proof (lock_location_prefix eq') as pfx.
        rewrite (ctxt_leq_all_locks lq) in pfx.
        destruct (lock_location_Some pfx) as [n' eqn'].
        apply @SendTyping with (n := n') (Δ := Δ'); auto.
        pose proof (ctxt_leq_change_lock_after lq eq eq'').
        apply IHtyp; auto.
        eapply closed_below_ren; eauto.
        intros n0 H1. eapply ctxt_leq_below_lock''; eauto.
      - pose proof (remove_lock_after_prefix eq).
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (lock_location_Some H0) as [n' eqn'].
        destruct (remove_lock_after_defined H0) as [Δ' eq''].
        apply @UpTyping with (Δ := Δ') (n := n'); auto.
        pose proof (ctxt_leq_remove_lock_after lq eq eq'').
        apply IHtyp; auto.
        eapply closed_below_ren; eauto.
        intros n0 H1; eapply ctxt_leq_below_lock''; eauto.
      - pose proof (add_lock_after_prefix eq).
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (lock_location_Some H0) as [n' eqn'].
        destruct (@add_lock_after_defined PName H E m p H0) as [Δ' eq''].
        apply @DownTyping with (Δ := Δ') (n := n'); auto.
        pose proof (ctxt_leq_add_lock_after lq eq eq'').
        apply IHtyp; auto.
        eapply closed_below_ren; eauto.
        intros n0 H1; eapply ctxt_leq_below_lock''; eauto.
    Qed.
        
  End TypeSystem.

  Section Substitution.

    Definition add_to_subst (σ : substitution) (e : expr) : substitution :=
      fun n => match n with
            | 0 => e
            | (S n) => σ n
            end.

    Inductive TypedSubst : Ctxt -> substitution -> Ctxt -> Prop :=
    | EmptySubst (σ : substitution) (Γ Δ : Ctxt) :
      ctxt_equiv Γ EmptyCtxt -> all_locks Δ = base -> TypedSubst Γ σ Δ
    | VarLSubst (Γ Δ : Ctxt) (m : mod) (τ : type) (e : expr) (σ1 σ2 : substitution):
      TypedSubst Γ σ1 Δ ->
      Typed (LockExt Δ m) e τ ->
      (forall n, σ2 n = add_to_subst σ1 e n) ->
      TypedSubst (VarExt Γ m τ) σ2 Δ
    | VarRSubst (Γ Δ : Ctxt) (m : mod) (τ : type) (σ1 σ2 : substitution) :
      TypedSubst Γ σ1 Δ ->
      (forall n, σ2 n = ren (σ1 n) S) -> 
      TypedSubst Γ σ2 (VarExt Δ m τ)
    | LockSubst (Γ Δ : Ctxt) (m : mod) (σ : substitution) :
      TypedSubst Γ σ Δ ->
      TypedSubst (LockExt Γ m) σ (LockExt Δ m).

    Theorem TypedSubstAt : forall {Γ Δ : Ctxt} {σ : substitution} {n : nat} {m1 m2 : mod} {τ : type},
        TypedSubst Γ σ Δ ->
        InCtxt n (mod_app m1 m2) τ m1 Γ ->
        Typed (LockExt Δ m2) (σ n) τ.
    Proof using.
      intros Γ Δ σ n m1 m2 τ styp; revert n m1 m2 τ; induction styp; intros n m1 m2 τ' i.
      - rewrite (InCtxt_proper H0) in i. dependent destruction i; cbn.
      - dependent destruction i; cbn.
        -- rewrite mod_base_app in H0; rewrite H1; cbn; assumption.
        -- rewrite H1; cbn; apply IHstyp with (m1 := m0); assumption.
      - rewrite H0. apply @weakening with (Γ := LockExt Δ m2).
        constructor; eapply VarAddLeq; [apply ctxt_leq_refl | unfold id_renaming; auto].
        apply IHstyp with (m1 := m1); assumption.
      - dependent destruction i; cbn.
        rewrite mod_app_assoc in i. apply IHstyp in i.
        apply Typed_proper with (Δ := LockExt (LockExt Δ m) m2) in i. assumption.
        apply LockSplitEquiv. reflexivity.
    Qed.

    Lemma TypedSubstUp : forall {Γ Δ : Ctxt} {σ : substitution} {m : mod} {τ : type},
        TypedSubst Γ σ Δ ->
        TypedSubst (VarExt Γ m τ) (substup σ) (VarExt Δ m τ).
    Proof using.
      intros Γ Δ σ m τ styp.
      eapply VarLSubst.
      - eapply VarRSubst; [exact styp | intro n; reflexivity].
      - eapply VarTyping; apply @thereLockInCtxt with (m1 := base); rewrite mod_base_app; apply hereInCtxt.
      - intro n; destruct n; cbn; reflexivity.
    Qed.

    Theorem TypeSubst_ext : forall {Γ Δ : Ctxt} {σ1 σ2 : substitution},
        (forall n, σ1 n = σ2 n) ->
        TypedSubst Γ σ1 Δ ->
        TypedSubst Γ σ2 Δ.
    Proof using.
      intros Γ Δ σ1 σ2 ext_eq styp; revert σ2 ext_eq; induction styp; intros σ3 ext_eq;
        try (econstructor; eauto; fail).
      - eapply VarLSubst; eauto. intro n; rewrite <- ext_eq; auto.
      - eapply VarRSubst; eauto. intro n; rewrite <- ext_eq; auto.
    Qed.

    Theorem TypeSubstRefl : forall {Γ : Ctxt},
        TypedSubst Γ id_substitution Γ.
    Proof using.
      intro Γ; induction Γ; try (econstructor; eauto; fail).
      econstructor; reflexivity. 
      apply @TypeSubst_ext with (σ1 := substup id_substitution); [exact id_substup|].
      apply TypedSubstUp. exact IHΓ.
    Qed.

    Theorem TypedSubstAllLocks : forall {Γ Δ : Ctxt} {σ : substitution},
        TypedSubst Γ σ Δ ->
        all_locks Γ = all_locks Δ.
    Proof using.
      intros Γ Δ σ typ; induction typ; cbn; auto.
      - transitivity (@all_locks PName EmptyCtxt).
        apply all_locks_proper; assumption.
        cbn; symmetry; assumption.
      - f_equal; assumption.
    Qed.
    
    Theorem TypedSubstLockLocation : forall {Γ Δ : Ctxt} {σ : substitution} {i j : nat} {m : mod},
        TypedSubst Γ σ Δ ->
        lock_location Γ m = Some i ->
        lock_location Δ m = Some j ->
        forall k, i <= k -> k < num_vars Γ -> closed_below (σ k) j.
    Proof using.
      intros Γ Δ σ i j m styp; revert i j m; induction styp; intros i j m' eqi eqj k i_le_k k_lt_Γ;
        cbn in *.
      - rewrite (num_vars_proper H0) in k_lt_Γ; cbn in k_lt_Γ; inversion k_lt_Γ.
      - destruct (lock_location Γ m') eqn: eqi'; inversion eqi; subst; clear eqi; rename eqi' into eqi.
        rewrite H1; destruct k; [inversion i_le_k|]; cbn.
        rewrite <- PeanoNat.Nat.succ_lt_mono in k_lt_Γ; apply le_S_n in i_le_k.
        exact (IHstyp n j m' eqi eqj k i_le_k k_lt_Γ).
      - destruct (lock_location Δ m') eqn:eqj'; inversion eqj; subst; clear eqj; rename eqj' into eqj.
        rewrite H0. apply @closed_below_ren with (k' := n); [apply le_n_S|].
        apply IHstyp with (i := i) (m := m'); assumption.
      - rewrite <- (TypedSubstAllLocks styp) in eqj; destruct (prefixb m' (all_locks Γ)) eqn:pfx.
        apply IHstyp with (i := i) (m := m'); assumption.
        destruct (prefixb m' (mod_app (all_locks Γ) m)) eqn: pfx'; inversion eqi; inversion eqj; subst.
        apply closed_below_zero.
    Qed.

    Definition unit_subst_before (σ : substitution) (n : nat) :=
      fun m => if PeanoNat.Nat.ltb m n then @uu PName else σ m.

    Lemma change_lock_after_subst : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {σ : substitution} {m : mod} {p q : PName} {n : nat},
        TypedSubst Γ1 σ Δ1 ->
        change_lock_after Γ1 m p q = Some Γ2 ->
        change_lock_after Δ1 m p q = Some Δ2 ->
        lock_location Γ1 (cons m p) = Some n ->
        TypedSubst Γ2 (unit_subst_before σ n) Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 σ m p q n styp; revert Γ2 Δ2 m p q n; dependent induction styp;
        intros Γ2 Δ2 n p q n' eqΓ eqΔ loc; cbn in *.
      - eapply change_lock_after_no_locks in H1; rewrite H1 in eqΔ; inversion eqΔ.
      - destruct (change_lock_after Γ n p q) eqn:eqΓ';
          inversion eqΓ; subst; clear eqΓ; rename eqΓ' into eqΓ.
        destruct (lock_location Γ (cons n p)) eqn:loc';
          inversion loc; subst; clear loc; rename loc' into loc.
        apply VarLSubst with (e := uu) (σ1 := unit_subst_before σ1 n0).
        apply IHstyp with (m := n) (p := p) (q := q); auto.
        apply UnitTyping.
        intro n1; destruct n1; cbn. reflexivity.
        unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n1 n0) eqn:eq.
        rewrite PeanoNat.Nat.ltb_lt in eq; rewrite PeanoNat.Nat.succ_lt_mono in eq; rewrite <- PeanoNat.Nat.ltb_lt in eq;
          rewrite eq; reflexivity.
        destruct (PeanoNat.Nat.ltb (S n1) (S n0)) eqn:eq'.
        rewrite PeanoNat.Nat.ltb_lt in eq'; apply <- PeanoNat.Nat.succ_lt_mono in eq'; rewrite <- PeanoNat.Nat.ltb_lt in eq';
          rewrite eq' in eq; inversion eq.
        rewrite H1; cbn; reflexivity.
      - destruct (change_lock_after Δ n p q) eqn:eqΔ'; inversion eqΔ; subst; clear eqΔ; rename eqΔ' into eqΔ; rename c into Δ2.
        apply VarRSubst with (σ1 := unit_subst_before σ1 n').
        eapply IHstyp; eauto.
        intro n0. unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n0 n'); cbn; auto.
      - rewrite <- (TypedSubstAllLocks styp) in eqΔ.
        destruct (prefixb (cons n p) (all_locks Γ)) eqn:pfx;
          [| destruct (remove_Prefix (all_locks Γ) n) as [m''|]; [|inversion eqΓ]].
        -- eapply IHstyp; eauto.
        -- destruct (prefixb (cons m'' p) m) eqn:pfx'; inversion eqΓ; inversion eqΔ; subst; clear eqΓ eqΔ.
           destruct (prefixb (cons n p) (mod_app (all_locks Γ) m)) eqn:pfx'';
             inversion loc; subst; clear loc.
           apply LockSubst. eapply TypeSubst_ext; [| exact styp].
           intro n0. unfold unit_subst_before.
           destruct (PeanoNat.Nat.ltb n0 0) eqn:eq; [| reflexivity].
           rewrite PeanoNat.Nat.ltb_lt in eq; inversion eq.
    Qed.

    Lemma remove_lock_after_subst : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {σ : substitution} {m : mod} {p : PName} {n : nat},
        TypedSubst Γ1 σ Δ1 ->
        remove_lock_after Γ1 m p = Some Γ2 ->
        remove_lock_after Δ1 m p = Some Δ2 ->
        lock_location Γ1 (cons m p) = Some n ->
        TypedSubst Γ2 (unit_subst_before σ n) Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 σ m p n styp; revert Γ2 Δ2 m p n; dependent induction styp;
        intros Γ2 Δ2 n p n' eqΓ eqΔ loc; cbn in *.
      - eapply remove_lock_after_no_locks in H1; rewrite H1 in eqΔ; inversion eqΔ.
      - destruct (remove_lock_after Γ n p) eqn:eqΓ';
          inversion eqΓ; subst; clear eqΓ; rename eqΓ' into eqΓ.
        destruct (lock_location Γ (cons n p)) eqn:loc';
          inversion loc; subst; clear loc; rename loc' into loc.
        apply VarLSubst with (e := uu) (σ1 := unit_subst_before σ1 n0).
        apply IHstyp with (m := n) (p := p); auto.
        apply UnitTyping.
        intro n1; destruct n1; cbn. reflexivity.
        unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n1 n0) eqn:eq.
        rewrite PeanoNat.Nat.ltb_lt in eq; rewrite PeanoNat.Nat.succ_lt_mono in eq; rewrite <- PeanoNat.Nat.ltb_lt in eq;
          rewrite eq; reflexivity.
        destruct (PeanoNat.Nat.ltb (S n1) (S n0)) eqn:eq'.
        rewrite PeanoNat.Nat.ltb_lt in eq'; apply <- PeanoNat.Nat.succ_lt_mono in eq'; rewrite <- PeanoNat.Nat.ltb_lt in eq';
          rewrite eq' in eq; inversion eq.
        rewrite H1; cbn; reflexivity.
      - destruct (remove_lock_after Δ n p) eqn:eqΔ'; inversion eqΔ; subst; clear eqΔ; rename eqΔ' into eqΔ; rename c into Δ2.
        apply VarRSubst with (σ1 := unit_subst_before σ1 n').
        eapply IHstyp; eauto.
        intro n0. unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n0 n'); cbn; auto.
      - rewrite <- (TypedSubstAllLocks styp) in eqΔ.
        destruct (prefixb (cons n p) (all_locks Γ)) eqn:pfx;
          [| destruct (remove_Prefix (all_locks Γ) n) as [m''|]; [|inversion eqΓ]].
        -- eapply IHstyp; eauto.
        -- destruct (prefixb (cons m'' p) m) eqn:pfx'; inversion eqΓ; inversion eqΔ; subst; clear eqΓ eqΔ.
           destruct (prefixb (cons n p) (mod_app (all_locks Γ) m)) eqn:pfx'';
             inversion loc; subst; clear loc.
           apply LockSubst. eapply TypeSubst_ext; [| exact styp].
           intro n0. unfold unit_subst_before.
           destruct (PeanoNat.Nat.ltb n0 0) eqn:eq; [| reflexivity].
           rewrite PeanoNat.Nat.ltb_lt in eq; inversion eq.
    Qed.

    Lemma add_lock_after_subst : forall {Γ1 Γ2 Δ1 Δ2 : Ctxt} {σ : substitution} {m : mod} {p : PName} {n : nat},
        TypedSubst Γ1 σ Δ1 ->
        add_lock_after Γ1 m p = Some Γ2 ->
        add_lock_after Δ1 m p = Some Δ2 ->
        lock_location Γ1 m = Some n ->
        TypedSubst Γ2 (unit_subst_before σ n) Δ2.
    Proof using.
      intros Γ1 Γ2 Δ1 Δ2 σ m p n styp; revert Γ2 Δ2 m p n; dependent induction styp;
        intros Γ2 Δ2 n p n' eqΓ eqΔ loc; cbn in *.
      - (* eapply add_lock_after_no_locks in H1; rewrite H1 in eqΔ; inversion eqΔ. *) admit.
      - destruct (add_lock_after Γ n p) eqn:eqΓ';
          inversion eqΓ; subst; clear eqΓ; rename eqΓ' into eqΓ.
        destruct (lock_location Γ n) eqn:loc';
          inversion loc; subst; clear loc; rename loc' into loc.
        apply VarLSubst with (e := uu) (σ1 := unit_subst_before σ1 n0).
        apply IHstyp with (m := n) (p := p); auto.
        apply UnitTyping.
        intro n1; destruct n1; cbn. reflexivity.
        unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n1 n0) eqn:eq.
        rewrite PeanoNat.Nat.ltb_lt in eq; rewrite PeanoNat.Nat.succ_lt_mono in eq; rewrite <- PeanoNat.Nat.ltb_lt in eq;
          rewrite eq; reflexivity.
        destruct (PeanoNat.Nat.ltb (S n1) (S n0)) eqn:eq'.
        rewrite PeanoNat.Nat.ltb_lt in eq'; apply <- PeanoNat.Nat.succ_lt_mono in eq'; rewrite <- PeanoNat.Nat.ltb_lt in eq';
          rewrite eq' in eq; inversion eq.
        rewrite H1; cbn; reflexivity.
      - destruct (add_lock_after Δ n p) eqn:eqΔ'; inversion eqΔ; subst; clear eqΔ; rename eqΔ' into eqΔ; rename c into Δ2.
        apply VarRSubst with (σ1 := unit_subst_before σ1 n').
        eapply IHstyp; eauto.
        intro n0. unfold unit_subst_before.
        destruct (PeanoNat.Nat.ltb n0 n'); cbn; auto.
      - rewrite <- (TypedSubstAllLocks styp) in eqΔ.
        destruct (prefixb n (all_locks Γ)) eqn:pfx;
          [| destruct (remove_Prefix (all_locks Γ) n) as [m''|]; [|inversion eqΓ]].
        -- eapply IHstyp; eauto.
        -- destruct (prefixb m'' m) eqn:pfx'; inversion eqΓ; inversion eqΔ; subst; clear eqΓ eqΔ.
           destruct (prefixb n (mod_app (all_locks Γ) m)) eqn:pfx'';
             inversion loc; subst; clear loc.
           apply LockSubst. eapply TypeSubst_ext; [| exact styp].
           intro n0. unfold unit_subst_before.
           destruct (PeanoNat.Nat.ltb n0 0) eqn:eq; [| reflexivity].
           rewrite PeanoNat.Nat.ltb_lt in eq; inversion eq.
    (* Qed. *)
    Admitted.

    Theorem TypedSubstitution : forall {Γ Δ : Ctxt} {σ : substitution} {e : expr} {τ : type},
        Typed Γ e τ ->
        TypedSubst Γ σ Δ ->
        Typed Δ (subst e σ) τ.
    Proof using.
      intros Γ Δ σ e τ typ; revert Δ σ; induction typ; try rename Δ into Δ'; intros Δ σ styp; cbn;
        try (econstructor; eauto; fail).
      - apply Typed_proper with (Γ := LockExt Δ base); [constructor; reflexivity |].
        eapply @TypedSubstAt; [exact styp| cbn; exact i].
      - constructor.
        apply IHtyp; constructor; auto; fail.
      - econstructor. apply IHtyp1; auto. apply IHtyp2.
        apply TypedSubstUp; auto.
      - econstructor; [apply IHtyp1 | apply IHtyp2 | apply IHtyp3]; try apply TypedSubstUp; auto.
      - constructor; apply IHtyp; apply TypedSubstUp; auto.
      - pose proof (change_lock_after_prefix eq).
        rewrite (TypedSubstAllLocks styp) in H0.
        rename Δ' into Γ';
          destruct (@change_lock_after_defined PName _ Δ m p q H0) as [Δ' eqΔ'].
        destruct (lock_location_Some H0) as [x eqx].
        apply @SendTyping with (n := x) (Δ := Δ'); auto.
        rewrite (@closed_below_subst_ext PName e σ (unit_subst_before σ n) n); auto.
        apply IHtyp. eapply change_lock_after_subst; eauto.
        intros k n_le_k; unfold unit_subst_before; destruct (PeanoNat.Nat.ltb k n) eqn:eq'';
          [rewrite PeanoNat.Nat.ltb_lt in eq''; lia| reflexivity].
        apply @closed_narrow_subst with (n := 0) (m := n) (j := num_vars Γ).
        -- intros k H1 H2;  inversion H2.
        -- intros k H1 H2;
             eapply @TypedSubstLockLocation with (m := (cons m p)); eauto.
        -- rewrite (change_lock_after_num_vars eq).
           eapply Typed_closed_above; eauto.
        -- fold (closed_below e n); assumption.
      - pose proof (remove_lock_after_prefix eq).
        rewrite (TypedSubstAllLocks styp) in H0.
        rename Δ' into Γ';
          destruct (@remove_lock_after_defined PName _ Δ m p H0) as [Δ' eqΔ'].
        destruct (lock_location_Some H0) as [x eqx].
        apply @UpTyping with (n := x) (Δ := Δ'); auto.
        rewrite (@closed_below_subst_ext PName e σ (unit_subst_before σ n) n); auto.
        apply IHtyp. eapply remove_lock_after_subst; eauto.
        intros k n_le_k; unfold unit_subst_before; destruct (PeanoNat.Nat.ltb k n) eqn:eq'';
          [rewrite PeanoNat.Nat.ltb_lt in eq''; lia| reflexivity].
        apply @closed_narrow_subst with (n := 0) (m := n) (j := num_vars Γ).
        -- intros k H1 H2;  inversion H2.
        -- intros k H1 H2;
             eapply @TypedSubstLockLocation with (m := (cons m p)); eauto.
        -- rewrite (remove_lock_after_num_vars eq).
           eapply Typed_closed_above; eauto.
        -- fold (closed_below e n); assumption.
      - pose proof (add_lock_after_prefix eq).
        rewrite (TypedSubstAllLocks styp) in H0.
        rename Δ' into Γ';
          destruct (@add_lock_after_defined PName _ Δ m p H0) as [Δ' eqΔ'].
        destruct (lock_location_Some H0) as [x eqx].
        apply @DownTyping with (n := x) (Δ := Δ'); auto.
        rewrite (@closed_below_subst_ext PName e σ (unit_subst_before σ n) n); auto.
        apply IHtyp. eapply add_lock_after_subst; eauto.
        intros k n_le_k; unfold unit_subst_before; destruct (PeanoNat.Nat.ltb k n) eqn:eq'';
          [rewrite PeanoNat.Nat.ltb_lt in eq''; lia| reflexivity].
        apply @closed_narrow_subst with (n := 0) (m := n) (j := num_vars Γ).
        -- intros k H1 H2;  inversion H2.
        -- intros k H1 H2;
             eapply @TypedSubstLockLocation with (m := m); eauto.
        -- rewrite (add_lock_after_num_vars eq).
           eapply Typed_closed_above; eauto.
        -- fold (closed_below e n); assumption.
    Qed.
        
  End Substitution.
End CorpsTypes.

