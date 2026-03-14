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
        apply @SendTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (change_lock_equiv eqv eq eqE).
      - pose proof (remove_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (remove_lock_after_defined pfx) as [E eqE].
        apply @UpTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (remove_lock_equiv eqv eq eqE).
      - pose proof (add_lock_after_prefix eq) as pfx.
        rewrite (all_locks_proper eqv) in pfx.
        destruct (@add_lock_after_defined _ _ Δ m p pfx) as [E eqE].
        apply @DownTyping with (Δ := E); auto. apply IHtyp; auto.
        apply (add_lock_equiv eqv eq eqE).
    Qed.

    Theorem Typed_proper : forall Γ Δ, ctxt_equiv Γ Δ -> forall e τ, Typed Γ e τ <-> Typed Δ e τ.
    Proof using.
      intros Γ Δ H0 e τ; split; intro H1; [| symmetry in H0]; eapply Typed_proper'; eassumption.
    Qed.


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


    Theorem weakening : forall {Γ Δ : Ctxt} {ξ : renaming} (lq : ctxt_leq Γ ξ Δ)
                          (e : expr) (τ : type),
        Typed Γ e τ ->
        Typed Δ (ren e ξ) τ.
    Proof using.
      intros Γ Δ ξ lq e τ typ; revert Δ ξ lq; induction typ; intros E ξ lq; cbn;
        try (econstructor; eauto; fail).
      - econstructor; apply (Inctxt_leq lq); exact i.
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
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (@change_lock_after_defined PName _ E m p q H0) as [Δ' eq'].
        apply @SendTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq_change_lock_after lq eq eq').
        apply IHtyp; auto.
      - pose proof (remove_lock_after_prefix eq).
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (remove_lock_after_defined H0) as [Δ' eq'].
        apply @UpTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq_remove_lock_after lq eq eq').
        apply IHtyp; auto.
      - pose proof (add_lock_after_prefix eq).
        rewrite (ctxt_leq_all_locks lq) in H0.
        destruct (@add_lock_after_defined _ _ E m p H0) as [Δ' eq'].
        apply @DownTyping with (Δ := Δ'); auto.
        pose proof (ctxt_leq_add_lock_after lq eq eq').
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

