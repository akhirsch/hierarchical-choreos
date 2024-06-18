Require Import EqBool.
Require Import Syntax.
Require Import RelationClasses.
Require Import Lia.
Require Import Coq.Program.Equality.

Section CorpsTypes.
  Context {PName : Type} `{EqBool PName}.

  #[local] Notation Ctxt := (@Ctxt PName).
  #[local] Notation type := (type PName).
  #[local] Notation expr := (expr PName).
  #[local] Notation mod := (mod PName).
  #[local] Definition ptm := @proc_to_mod PName.
  Coercion ptm : PName >-> mod.
  Context {CanSend CanUp CanDown : mod -> mod -> Prop}.
  
  Section TypeSystem.

    Inductive Typed : Ctxt -> expr -> type -> Prop :=
    | VarTyping {Γ : Ctxt} {n : nat} {τ : type} (m : mod) (pf1 : vars Γ n = (m, τ)) (pf2 : locks Γ n = m)
      : Typed Γ (var n) τ
    | UnitTyping (Γ : Ctxt) : Typed Γ uu UnitT
    | AtTyping {Γ : Ctxt} {e : expr} {τ : type} (p : PName) (pf : Typed (add_lock Γ p) e τ)
      : Typed Γ (atE p e) (AtT p τ)
    | LetTyping {Γ : Ctxt} {e1 e2 : expr} {τ σ : type} {p : PName}
        (pf1 : Typed Γ e1 (AtT p τ)) (pf2 : Typed (add_var Γ p τ) e2 σ)
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
        (pf2 : Typed (add_var Γ base τ1) e2 σ)
        (pf3 : Typed (add_var Γ base τ2) e3 σ)
      : Typed Γ (caseE e1 e2 e3) σ
    | EfqlTyping {Γ : Ctxt} {e : expr}
        (pf : Typed Γ e VoidT) (τ : type)
      : Typed Γ (efql e) τ
    | LamTyping {Γ : Ctxt} {e : expr} {τ1 τ2 : type}
        (pf : Typed (add_var Γ base τ1) e τ2)
      : Typed Γ (lam τ1 e) (ArrT τ1 τ2)
    | AppTyping {Γ : Ctxt} {e1 e2 : expr} {τ1 τ2 : type}
        (pf1 : Typed Γ e1 (ArrT τ1 τ2))
        (pf2 : Typed Γ e2 τ1)
      : Typed Γ (appE e1 e2) τ2
    | SendTyping {Γ Γ' : Ctxt} {p q : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt (add_lock Γ p) Δ) e τ)
        (cs : CanSend (cons (all_locks Γ) p) (cons (all_locks Γ) q))
        (eqv : ctxt_equiv Γ' (addFiniteCtxt (add_lock Γ q) Δ))
      : Typed Γ' (send e p Δ q) τ
    | UpTyping {Γ : Ctxt} {p : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt Γ Δ) e τ)
        (cu : CanUp (all_locks Γ) (cons (all_locks Γ) p))
      : Typed (addFiniteCtxt (add_lock Γ p) Δ) (up e p Δ) τ
    | DownTyping {Γ : Ctxt} {p : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt (add_lock Γ p) Δ) e τ)
        (cu : CanDown (cons (all_locks Γ) p) (all_locks Γ))
      : Typed (addFiniteCtxt Γ Δ) (down e p Δ) τ
    .

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

    Theorem add_finite_ctxt_ext : forall Γ Δ E,
        ctxt_equiv Γ Δ -> ctxt_equiv (addFiniteCtxt Γ E) (@addFiniteCtxt PName Δ E).
    Proof using.
      intros Γ Δ E; revert Γ Δ; induction E; intros Γ Δ eqv; cbn; auto;
        apply IHE; [apply add_var_ext; auto | apply add_lock_ext; auto].
    Qed.

    Theorem type_ext : forall (Γ Δ : Ctxt) (e : expr) (τ : type),
        Typed Γ e τ -> (ctxt_equiv Γ Δ) -> Typed Δ e τ.
    Proof using.
      intros Γ Δ e τ typd; revert Δ; induction typd; try (rename Δ into Γ'); intros Δ' eqv';
        pose proof (proj1 eqv') as vars_eq;
        pose proof (proj1 (proj2 eqv')) as locks_eq;
        pose proof (proj2 (proj2 eqv')) as all_locks_eq;
        repeat match goal with
          | [ H : vars ?Γ ?n = ?x, H' : forall x, vars ?Γ x = vars ?Δ x |- _ ] =>
              lazymatch goal with
              | [ _ : vars Δ n = x |- _ ] => fail
              | _ => assert (vars Δ n = x) by (rewrite <- H'; exact H)
              end
          | [ H : locks ?Γ ?n = ?x, H' : forall x, locks ?Γ x = locks ?Δ x |- _ ] =>
              lazymatch goal with
              | [ _ : locks Δ n = x |- _ ] => fail
              | _ => assert (locks Δ n = x) by (rewrite <- H'; exact H)
              end
          | [ IH : forall Δ, ctxt_equiv (add_lock ?Γ ?m) Δ -> Typed Δ ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] =>
              lazymatch goal with
              | [ _ : Typed (add_lock Δ m) e τ |- _ ] => fail
              | _ => pose proof (IH (add_lock Δ m) (add_lock_ext Γ Δ m H))
              end
          | [ IH : forall Δ, ctxt_equiv (add_var ?Γ ?m ?τ') Δ -> Typed Δ ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] =>
              lazymatch goal with
              | [ _ : Typed (add_var Δ m τ') e τ |- _ ] => fail
              | _ => pose proof (IH (add_var Δ m τ') (add_var_ext Γ Δ m τ' H))
              end
          | [ IH : forall Δ, ctxt_equiv (addFiniteCtxt ?Γ ?E) Δ -> Typed Δ ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] =>
              lazymatch goal with
              | [ _ : Typed (addFiniteCtxt Δ E) e τ |- _ ] => fail
              | _ => pose proof (IH (addFiniteCtxt Δ E) (add_finite_ctxt_ext Γ Δ E H))
              end
          end;
        try (econstructor; eauto; fail).
      - apply @SendTyping with (Γ := Γ); auto.
        transitivity Γ'; auto. symmetry; assumption.
      - admit.
      - admit.
    Admitted.

    Definition ctxt_ren (Γ : Ctxt) (ξ : renaming) (mono : forall n m, n <= m -> PrefixOf (locks Γ (ξ n)) (locks Γ (ξ m))): Ctxt :=
      {|
        vars n := vars Γ (ξ n);
        locks n := locks Γ (ξ n);
        all_locks := all_locks Γ;
        locks_mono n m lt := mono n m lt;
        locks_bound n := locks_bound Γ (ξ n);
      |}.

    Lemma weakening : forall (Γ Δ : Ctxt) (e : expr) (ξ : renaming) (τ : type) mono,
        ctxt_equiv (ctxt_ren Γ ξ mono) Δ ->
        Typed Δ e τ -> Typed Γ (ren e ξ) τ.
    Proof using.
      intros Γ Δ e ξ τ mono eqv typ; revert Γ ξ mono eqv; induction typ;
        intros Γ'' ξ mono [vars_eqv [locks_eqv al_eqv]]; cbn.
      all: try (econstructor; eauto; fail).
      - apply VarTyping with (m := m).  rewrite <- pf1; rewrite <- vars_eqv; cbn; reflexivity.
        rewrite <- pf2; rewrite <- locks_eqv; cbn; reflexivity.
      - apply AtTyping. eapply IHtyp. Unshelve.
        2: { intros n m H0; cbn; apply mod_app_mono_l; apply mono; auto. }
        split; [|split].
        -- intro x; cbn. rewrite <- vars_eqv. cbn. reflexivity.
        -- intro x; cbn. rewrite <- locks_eqv. cbn. reflexivity.
        --
      Admitted.


  End TypeSystem.

  Section Substitution.

    Definition TypedSubst (Γ : Ctxt) (σ : substitution) (Δ : Ctxt) :=
      forall x, match PrefixOfT_dec (locks Γ x) (fst (vars Γ x)) with
           | Some pfxt => Typed (add_lock Δ (remove_PrefixT pfxt)) (σ x) (snd (vars Γ x))
           | None => True
           end.
      
    Lemma substup_typed : forall Γ Δ σ τ,
        TypedSubst Γ σ Δ -> TypedSubst (add_var Γ base τ) (substup σ) (add_var Δ base τ).
    Proof using.
      intros Γ Δ σ τ typd; unfold TypedSubst in *; intros x; destruct x; cbn.
      - econstructor; eauto; reflexivity.
      - specialize (typd x); destruct (PrefixOfT_dec (locks Γ x) (fst (vars Γ x))); [|exact I].
        eapply weakening with (Δ := add_lock Δ (remove_PrefixT p)); auto.
        Unshelve.
        -- split; [|split].
           1,2: intro n.
           all: cbn; reflexivity.
        -- intros n m H0; apply locks_mono; lia.
    Qed.
    
    Theorem subst_typed : forall Γ Δ e σ τ, Typed Γ e τ -> TypedSubst Γ σ Δ -> Typed Δ (subst e σ) τ.
    Proof using.
      intros Γ Δ e σ τ typed; revert Δ σ; induction typed; try (rename σ into τ');
        intros Γ'' σ typeds; cbn.
      all: try (econstructor; eauto; fail).
      - unfold TypedSubst in typeds; specialize (typeds n).
        rewrite pf1 in typeds; rewrite pf2 in typeds; cbn in typeds.
        destruct (PrefixOfT_dec m m) eqn:eq.
        2: { exfalso; destruct (Prefix2PrefixT (PO_refl m)) as [pfxt eq'];
             rewrite eq' in eq; inversion eq. }
        assert (p = POT_refl m) by apply UIprefixT; subst. cbn in typeds.
        apply type_ext with (Γ := add_lock Γ'' base); auto.
        split; [| split]; cbn; auto; [intro x|]; apply mod_base_app.
      - apply AtTyping.
        apply IHtyped.
        unfold TypedSubst; unfold TypedSubst in typeds.
        intro x; specialize (typeds x); cbn.
        destruct (PrefixOfT_dec (mod_app p (locks Γ x)) (fst (vars Γ x))) as [pfxt |];
          [| exact I].
        

                                             

  (* Section Decidability. *)

  (*   Program Fixpoint typedb (Γ : Ctxt) (e : expr) (τ : type) : bool := *)
  (*     match e with *)
  (*     | var x => eqb (locks Γ x, τ) (vars Γ x) *)
  (*     | uu => eqb τ UnitT *)
  (*     | atE p e => *)
  (*         match τ with *)
  (*         | AtT q σ => *)
  (*             eqb p q && typedb (add_lock Γ p) e σ *)
  (*         | _ => false *)
  (*         end *)
  (*     | letAt p e1 e2 => _ *)
  (*     | pair e1 e2 => _ *)
  (*     | pi1 e => _ *)
  (*     | pi2 e => _ *)
  (*     | inl e => _ *)
  (*     | inr e => _ *)
  (*     | caseE e1 e2 e3 => _ *)
  (*     | efql e => _ *)
  (*     | lam t e => _ *)
  (*     | appE e1 e2 => _ *)
  (*     | send e p Δ q => _ *)
  (*     | up e p Δ => _ *)
  (*     | down e p Δ => _ *)
  (*     end. *)
  (*   Next Obligation. *)

  (* End Decidability. *)
  
End CorpsTypes.

