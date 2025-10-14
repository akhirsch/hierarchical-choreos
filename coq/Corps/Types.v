Require Import EqBool.
Require Import Modalities.
Require Import Syntax.
Require Import Contexts.
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
(* From Stdlib Require Lists.List. *)
(* Import List.ListNotations. *)

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
    | SendTyping {Γ Γ' : Ctxt} {seen : nat} {m : mod} {p q : PName} {e : expr} {τ : type}
        (* (locks_seen : PrefixOf (cons m p) (all_locks Γ)) *)
        (locks_seen : PrefixOf (cons m p) (locks Γ seen))
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_send q locks_seen)))
        (pf : Typed Γ' e τ)
        (cs : CanSend (cons m p) (cons m q))
      : Typed Γ (send e seen m p q) τ
    | UpTyping {Γ Γ' : Ctxt} {seen : nat} {m : mod} {p : PName} {e : expr} {τ : type}
        (locks_seen : PrefixOf m (locks Γ seen))
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_up p locks_seen)))
        (pf : Typed Γ' e τ)
        (cu : CanUp m (cons m p))
      : Typed Γ (up e seen m p) τ
    | DownTyping {Γ Γ' : Ctxt} {seen : nat} {m : mod} {p : PName} {e : expr} {τ : type}
        (locks_seen : PrefixOf (cons m p) (locks Γ seen))
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_down locks_seen)))
        (pf : Typed Γ' e τ)
        (cu : CanDown (cons m p) m)
      : Typed Γ (down e seen m p) τ
    .

    (* Theorem type_ext' : forall {Γ Δ : Ctxt} {e : expr} {τ : type}, *)
    (*     Typed Γ e τ -> ctxt_equiv' Γ Δ -> Typed Δ e τ. *)
    (* Proof using. *)
    (*   intros Γ Δ e τ typd; revert Δ; induction typd; try (rename Δ into Γ'); intros Δ eqv'; *)
    (*     pose proof (proj1 eqv') as vars_eq; *)
    (*     pose proof (proj1 (proj2 eqv')) as locks_eq; *)
    (*     pose proof (proj2 (proj2 eqv')) as all_locks_eq. *)
    (*   all: try (econstructor; eauto; fail). *)
    (*   - specialize (vars_eq n). destruct (vars Δ n) eqn:eq; rewrite pf1 in vars_eq; cbn in vars_eq; subst. *)
    (*     apply VarTyping with (m := m0); auto. *)
    (*     destruct (locks_eq n) as [m1 [m2 [eq1 [eq2 eq_owner]]]]. *)
    (*     rewrite pf1 in eq_owner. rewrite eq in eq_owner. cbn in eq_owner. *)
    (*     rewrite <- all_locks_eq in eq2. rewrite eq1 in eq2. *)
    (*     rewrite eq2 in eq_owner. apply mod_app_back with (m3 := m2); auto. *)
    (*   - apply AtTyping; apply IHtypd; apply add_lock_ext'; auto. *)
    (*   - apply @LetTyping with (τ := τ). apply IHtypd1; auto. apply IHtypd2; auto. apply add_var_ext'; auto. *)
    (*   - apply @CaseTyping with (τ1 := τ1) (τ2 := τ2). apply IHtypd1; auto. apply IHtypd2. 2: apply IHtypd3. *)
    (*     all: apply add_var_ext'; auto. *)
    (*   - apply @LamTyping. apply IHtypd. apply add_var_ext'; auto. *)
    (*   - pose proof (locks_seen) as locks_seen'; rewrite all_locks_eq in locks_seen'. *)
    (*     eapply SendTyping with (locks_seen := locks_seen'); auto. reflexivity. apply IHtypd. etransitivity; [exact eqv|]. apply change_lock_ctxt_ext'; auto. *)

    Theorem type_ext : forall {Γ Δ : Ctxt} {e : expr} {τ : type},
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
          (* | [ IH : forall Δ, ctxt_equiv (addFiniteCtxt ?Γ ?E) Δ -> TypedAtLevel Δ ?l ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] => *)
          (*     lazymatch goal with *)
          (*     | [ _ : Typed (addFiniteCtxt Δ E) l e τ |- _ ] => fail *)
          (*     | _ => pose proof (IH (addFiniteCtxt Δ E) (add_finite_ctxt_ext Γ Δ E H)) *)
          (*     end *)
          end;
        try (econstructor; eauto; fail).
      - eapply @SendTyping with (Γ' := Γ'); eauto. 
        etransitivity; [exact eqv | apply change_lock_ext; auto].
        Unshelve. rewrite <- locks_eq; auto.
      - eapply @UpTyping with (Γ' := Γ'); eauto.
        etransitivity; [exact eqv | apply change_lock_ext; auto].
        Unshelve. rewrite <- locks_eq; auto.
      - eapply @DownTyping with (Γ' := Γ'); eauto.
        etransitivity; [exact eqv | apply change_lock_ext; auto].
        Unshelve. rewrite <- locks_eq; auto.
    Qed.

    Theorem exchange : forall {Γ Δ : Ctxt} {e : expr} {ξ : renaming} {τ : type}
                        (nolocks_change : forall n, locks Γ n = locks Γ (ξ n)),
        ctxt_equiv (ctxt_ren Γ ξ (nolocks_change_mono nolocks_change)) Δ ->
        Typed Δ e τ -> Typed Γ (ren e ξ) τ.
    Proof using.
      intros Γ Δ e ξ τ nochange eqv typ; revert Γ ξ nochange eqv; induction typ; try rename Γ'' into Γ2;
        intros Γ'' ξ nochange ctxt_eqv; cbn in *.
      all: pose proof ctxt_eqv as [vars_eqv [locks_eqv al_eqv]]; cbn in *.
      all: try (econstructor; eauto; fail).
      - apply VarTyping with (m := m).
        specialize (vars_eqv n); cbn in vars_eqv; rewrite vars_eqv; auto.
        specialize (locks_eqv n); cbn in locks_eqv; rewrite locks_eqv; auto.
      - econstructor; eauto. unshelve eapply IHtyp; cbn. intro n; f_equal; apply nochange.
        split; [| split]; try intro; cbn; auto; f_equal; auto.
      - econstructor; eauto. unshelve eapply IHtyp2; cbn.
        intro n; destruct n; cbn; auto.
        split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto.
      - econstructor; eauto; [unshelve eapply IHtyp2 | unshelve eapply IHtyp3]; cbn.
        1,3: intro n; destruct n; cbn; auto.
        all: split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto.
      - econstructor; eauto. unshelve eapply IHtyp; cbn.
        intro n; destruct n; cbn; auto.
        split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto.
      - destruct eqv as [vars_eqv' [locks_eqv' al_eqv']].
        eapply @SendTyping; eauto. reflexivity. unshelve eapply IHtyp; auto.
        intro n; cbn; rewrite <- nochange; reflexivity.
        split; [| split]; try intro x; auto.
        cbn. rewrite vars_eqv; auto.
        cbn; rewrite locks_eqv; rewrite locks_eqv'; auto.
        cbn; rewrite al_eqv; rewrite al_eqv'; auto.
        Unshelve.  rewrite nochange; rewrite locks_eqv; apply locks_seen.
      - destruct eqv as [vars_eqv' [locks_eqv' al_eqv']].
        eapply @UpTyping; eauto. reflexivity. unshelve eapply IHtyp; auto.
        intro n; cbn; rewrite <- nochange; reflexivity.
        split; [| split]; try intro x; auto.
        cbn. rewrite vars_eqv; auto.
        cbn; rewrite locks_eqv; rewrite locks_eqv'; auto.
        cbn; rewrite al_eqv; rewrite al_eqv'; auto.
        Unshelve.  rewrite nochange; rewrite locks_eqv; apply locks_seen.
      - destruct eqv as [vars_eqv' [locks_eqv' al_eqv']].
        eapply @DownTyping; eauto. reflexivity. unshelve eapply IHtyp; auto.
        intro n; cbn; rewrite <- nochange; reflexivity.
        split; [| split]; try intro x; auto.
        cbn. rewrite vars_eqv; auto.
        cbn; rewrite locks_eqv; rewrite locks_eqv'; auto.
        cbn; rewrite al_eqv; rewrite al_eqv'; auto.
        Unshelve.  rewrite nochange; rewrite locks_eqv; apply locks_seen.
    Qed.

    Theorem weakening : forall  {Γ Δ : Ctxt} {e : expr} {ξ : renaming} {τ : type}
                           (mono : forall n m, n <= m -> ξ n <= ξ m),
        ctxt_equiv (ctxt_ren Γ ξ (mono_mono_locks Γ ξ  mono)) Δ ->
        Typed Δ e τ -> Typed Γ (renseen (ren e ξ) ξ) τ.
    Proof using.
      intros Γ Δ e ξ τ mono eqv typd; revert Γ ξ mono eqv; induction typd;
        intros Γ'' ξ mono ctxt_eqv; cbn.
      all: pose proof ctxt_eqv as [vars_eqv [locks_eqv al_eqv]]; cbn in *.
      all: try (econstructor; eauto; fail).
      - econstructor; [rewrite vars_eqv | rewrite locks_eqv]; eauto.
      - econstructor. apply IHtypd with (mono := mono).
        split; [| split]; try intro x; cbn; auto; [rewrite locks_eqv | rewrite al_eqv]; auto.
      - econstructor. apply IHtypd1 with (mono := mono).
        split; [| split]; try intro x; cbn; auto.
        apply IHtypd2 with (mono := mono_renup ξ mono). 
        split; [| split]; try intro x; cbn.
        3: apply al_eqv.
        all: destruct x; cbn; auto.
      - econstructor. apply IHtypd1 with (mono := mono); auto.
        apply IHtypd2 with (mono := mono_renup ξ mono).
        2: apply IHtypd3 with (mono := mono_renup ξ mono).
        all: split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto.
      - econstructor. apply IHtypd with (mono := mono_renup ξ mono).
        split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto.
      - eapply @SendTyping; [reflexivity | | auto].
        Unshelve. 2: rewrite locks_eqv; auto.
        eapply IHtypd.
        pose proof eqv as [vars_eqv' [locks_eqv' al_eqv']]; cbn in vars_eqv'.
        split; [| split]; try intro x; cbn.
        rewrite vars_eqv; symmetry; apply vars_eqv'.
        rewrite locks_eqv; symmetry; apply locks_eqv'.
        rewrite al_eqv; symmetry; apply al_eqv'.
      - eapply @UpTyping; [reflexivity | | auto].
        Unshelve. 2: auto. 2: rewrite locks_eqv; auto.
        unshelve eapply IHtypd; auto.
        pose proof eqv as [vars_eqv' [locks_eqv' al_eqv']]; cbn in vars_eqv'.
        split; [| split]; try intro x; cbn.
        rewrite vars_eqv; symmetry; apply vars_eqv'.
        rewrite locks_eqv; symmetry; apply locks_eqv'.
        rewrite al_eqv; symmetry; apply al_eqv'.          
      - eapply @DownTyping; [reflexivity | | auto].
        Unshelve. 2: auto. 2: rewrite locks_eqv; auto.
        unshelve eapply IHtypd; auto.
        pose proof eqv as [vars_eqv' [locks_eqv' al_eqv']]; cbn in vars_eqv'.
        split; [| split]; try intro x; cbn.
        rewrite vars_eqv; symmetry; apply vars_eqv'.
        rewrite locks_eqv; symmetry; apply locks_eqv'.
        rewrite al_eqv; symmetry; apply al_eqv'.          
    Qed.        
        
  End TypeSystem.

  Section Substitution.

    Fixpoint add_vars (Γ : Ctxt) (xs : list (mod * type)) :=
      match xs with
      | nil => Γ
      | List.cons (m, τ) xs =>add_var (add_vars Γ xs) m τ
      end.

    Fixpoint finite_substitution (es : list expr) : substitution :=
      match es with
      | nil => fun x => var x
      | List.cons e es => fun x =>
                   match x with
                   | 0 => e
                   | S y => finite_substitution es y
                   end
      end.


    (* Fixpoint typed_finite_substitution (Γ : Ctxt) (Δ : FiniteCtxt) (es : list expr) : Prop := *)
    (*   match Δ, es with *)
    (*   | emptyFC, nil => True *)
    (*   | varFC m τ Δ, List.cons e es => Typed (add_lock Γ m) e τ /\ typed_finite_substitution Γ Δ es *)
    (*   | lockFC m Δ, es => typed_finite_substitution Γ Δ es *)
    (*   | _, _ => False *)
    (*   end. *)

    Fixpoint snoc {A : Type} (xs : list A) (x : A) : list A :=
      match xs with
      | List.cons x' xs' => List.cons x' (snoc xs' x)
      | List.nil => List.cons x nil
      end.

    Lemma snoc_app: forall {A : Type} (xs : list A) (x : A), snoc xs x = (xs ++ (x :: nil))%list.
    Proof using.
      intros A xs; induction xs as [| x' xs IHxs]; intro x; cbn; [| rewrite IHxs]; reflexivity.
    Qed.

    Lemma snoc_length : forall {A : Type} (xs : list A) (x : A), length (snoc xs x) = S (length xs).
    Proof using.
      intros A xs; induction xs as [| y xs IHxs]; intro x; cbn; [| rewrite IHxs]; reflexivity.
    Qed.

    Inductive typed_finite_substitution : Ctxt -> FiniteCtxt -> list expr -> Prop :=
    | TypedEmptySubst : forall (Γ : Ctxt), typed_finite_substitution Γ emptyFC nil
    |  TypedVarCtxt : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m : mod) (τ : type) (e : expr) (es : list expr),
        Typed (add_lock (add_lock Γ (FiniteCtxtLocks Δ)) m) e τ ->
        typed_finite_substitution  Γ Δ es ->
        typed_finite_substitution Γ (varFC m τ Δ) (snoc es e)
    | TypedLockCtxt : forall (Γ : Ctxt) (Δ : FiniteCtxt) (m : mod) (es : list expr),
        typed_finite_substitution (add_lock Γ m) Δ es ->
        typed_finite_substitution Γ (lockFC m Δ) es.

    Lemma typed_finite_substitution_length : forall Γ Δ es,
        typed_finite_substitution Γ Δ es ->
        FiniteCtxtSize Δ = length es.
    Proof using.
      intros Γ Δ es typd; induction typd; cbn; try rewrite snoc_length; auto.
    Qed.

    Lemma finite_substitution_past_length : forall es n,
        length es <= n ->
        finite_substitution es n = var (n - length es).
    Proof using.
      intro es; induction es; destruct n; cbn; intro length_le_n; auto.
      inversion length_le_n.
      rewrite IHes; [reflexivity|].
      apply le_S_n; exact length_le_n.
    Qed.

    Lemma finite_substitution_snoc_end : forall es e,
        finite_substitution (snoc es e) (length es) = e.
    Proof using.
      intro es; induction es as [| e' es IHes]; intro e; cbn; [| rewrite IHes]; auto.
    Qed.

    Lemma finite_substitution_snoc_lt : forall es e n,
        n < length es ->
        finite_substitution (snoc es e) n = finite_substitution es n.
    Proof using.
      intro es; induction es as [| e' es IHes]; intros e n n_lt_len; cbn in *.
      - inversion n_lt_len.
      - destruct n; [reflexivity|].
        apply IHes.
        apply PeanoNat.lt_S_n; exact n_lt_len.
    Qed.

    Lemma typed_finite_subst_typed : forall Γ Δ es n m m' τ,
        typed_finite_substitution Γ Δ es ->
        nth_var Δ n = Some (m, τ) ->
        locks_at Δ n = Some m' ->
        Typed (add_lock (add_lock Γ m') m) (finite_substitution es n) τ.
    Proof using.
      intros Γ Δ es n m m' τ typd; revert n m m' τ; induction typd; intros n m' m'' τ' eq1 eq2; cbn in *.
      - unfold nth_var in eq1; destruct n; cbn in eq1; inversion eq1.
      - unfold nth_var in eq1; cbn in eq1; unfold locks_at in eq2; cbn in eq2.
        destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) n) as [size_le_n | n_lt_size].
        -- destruct (Compare_dec.le_lt_eq_dec _ _ size_le_n) as [size_lt_n | size_eq_n].
           --- rewrite List.nth_error_app2 in eq1; [| rewrite <- vars_of_finite_ctxt_size; auto].
               rewrite List.nth_error_app2 in eq2; [| rewrite locks_at_finite_ctxt_vars_size; auto].
               rewrite <- vars_of_finite_ctxt_size in eq1; rewrite locks_at_finite_ctxt_vars_size in eq2.
               destruct (n - FiniteCtxtSize Δ) as [| n'] eqn:eq; cbn in eq1; cbn in eq2.
               exfalso; lia.
               rewrite List.nth_error_nil in eq1; inversion eq1.
           --- rewrite List.nth_error_app2 in eq1; [| rewrite <- vars_of_finite_ctxt_size; auto].
               rewrite List.nth_error_app2 in eq2; [| rewrite locks_at_finite_ctxt_vars_size; auto].
               rewrite <- vars_of_finite_ctxt_size in eq1; rewrite locks_at_finite_ctxt_vars_size in eq2.
               rewrite size_eq_n in eq1; rewrite PeanoNat.Nat.sub_diag in eq1;
                 rewrite size_eq_n in eq2; rewrite PeanoNat.Nat.sub_diag in eq2; cbn in eq1; cbn in eq2.
               inversion eq1; subst; clear eq1; inversion eq2; subst.
               pose proof (typed_finite_substitution_length _ _ _ typd).
               rewrite H1 at 1. rewrite finite_substitution_snoc_end; auto.
        -- rewrite List.nth_error_app1 in eq1; [| rewrite <- vars_of_finite_ctxt_size; auto].
           rewrite List.nth_error_app1 in eq2; [| rewrite locks_at_finite_ctxt_vars_size; auto].
           rewrite finite_substitution_snoc_lt. 2: rewrite <- (typed_finite_substitution_length _ _ _ typd); auto.
           apply IHtypd; auto.
      - unfold locks_at in eq2; cbn in eq2.
        unfold nth_var in eq1; cbn in eq1.
        admit.
    Abort.
           

    Theorem finite_subst_typed : forall Γ e Δ E es τ,
        Typed (addFiniteCtxt (addFiniteCtxt Γ Δ) E) e τ ->
        typed_finite_substitution Γ Δ es ->
        Typed (addFiniteCtxt (add_lock Γ (FiniteCtxtLocks Δ)) E) (subst e (substup_many (FiniteCtxtSize E) (finite_substitution es))) τ.
    Proof using.
      intros Γ e; revert Γ; induction e; intros Γ Δ E es τ typd typd_subst; cbn; inversion typd; subst; 
        try (econstructor; eauto; fail).
      - destruct (Compare_dec.le_lt_dec (FiniteCtxtSize E) n).
        -- rewrite vars_past_finite_ctxt in pf1; auto.
           rewrite AddFiniteCtxt_locks1 in pf1; auto.
           unfold substup_many. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _) l).
           destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) (n - FiniteCtxtSize E)) as [l' | l'].
           ---
             eapply weakening. apply extend_rename.
             rewrite finite_substitution_past_length; [|rewrite <- (typed_finite_substitution_length _ _ _ typd_subst); exact l'].
               cbn. 
               rewrite vars_past_finite_ctxt in pf1; auto.
               rewrite AddFiniteCtxt_locks1 in pf1; auto.
               rewrite <- (typed_finite_substitution_length _ _ _ typd_subst).
               eapply VarTyping; cbn. exact pf1. reflexivity.
           --- eapply weakening with (mono := add_mono (FiniteCtxtSize E)).
               apply extend_rename.
      (*          apply typed_finite_subst_typed with (Δ := Δ); auto. *)
      (*          rewrite vars_in_finite_ctxt with (Γ:= Γ); auto. *)
      (*          rewrite pf1; f_equal. *)
      (*          pose proof (AddFiniteCtxt_locks2 Γ Δ (n - FiniteCtxtSize E) l') *)
      (*      admit. *)
      (*   -- unfold substup_many; rewrite (proj2 (PeanoNat.Nat.ltb_lt n (FiniteCtxtSize E))); [| exact l]. *)
      (*        apply @VarTyping with (m := locks (addFiniteCtxt Γ E) n). *)
      (*        2: { pose proof (AddFiniteCtxt_locks2 (add_lock Γ (FiniteCtxtLocks Δ)) E n l). *)
      (*             pose proof (AddFiniteCtxt_locks2 Γ E n l). *)
      (*             rewrite <- H1 in H0; inversion H0; reflexivity. } *)
      (*        destruct (nth_var_size1 E n l) as [m [τ' eq]]. *)
      (*        assert (vars (addFiniteCtxt (addFiniteCtxt Γ Δ) E) n = (m, τ')) as eq' *)
      (*            by (apply nth_var_add_ctxt; auto). *)
      (*        rewrite nth_var_add_ctxt with (pr := (m, τ')); auto. *)
      (*        rewrite eq' in pf1; inversion pf1; subst; clear pf1. *)
      (*        f_equal. *)
      (*        pose proof (AddFiniteCtxt_locks2 Γ E n l). *)
      (*        pose proof (AddFiniteCtxt_locks2 (addFiniteCtxt Γ Δ) E n l). *)
      (*        rewrite <- H1 in H0; inversion H0; subst; reflexivity. *)
      (* - *)
        
             
      (*   unfold substup_many. *)
      (*   assert (PeanoNat.Nat.ltb n (FiniteCtxtSize E) = false) as eq by (rewrite PeanoNat.Nat.ltb_ge; auto); rewrite eq. *)
        

      (*   destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) n). *)
      (*   rewrite finite_substitution_past_length. *)
      (*   apply @VarTyping with (m := locks (addFiniteCtxt Γ Δ) n). *)
      (*   rewrite <- typed_finite_substitution_length with (Γ := Γ) (Δ := Δ); auto. *)
      (*   rewrite <- vars_past_finite_ctxt; auto. *)
      (*   admit. *)
      (*   erewrite <- typed_finite_substitution_length; eauto. *)
      (*   admit. *)
      (* -  eapply AtTyping. apply IHe with (xs := xs). *)
      (*    admit. *)
      (*    admit. *)
      (* - apply @LetTyping with (τ := τ0). *)
      (*   apply IHe1 with (xs := xs); auto. *)
      (*   pose proof (IHe2 Γ (List.cons (proc_to_mod p, τ0) xs) (List.cons (var 0) es) τ). *)
        
               (*   apply IHe2 with (xs := (List.cons (proc_to_mod p, τ0) xs)). *)
    Abort.
      

(*     Definition TypedSubst (Γ : Ctxt) (σ : substitution) (ξ : renaming) (Δ : Ctxt) := *)
(*       all_locks Γ = all_locks Δ /\ *)
(*         (forall n, PrefixOf (locks Γ n) (locks Δ (ξ n))) /\  *)
(*         (* forall x m, *) *)
(*         (*   mod_app m (locks Γ x) = fst (vars Γ x) ->  *) *)
(*         (*   Typed (add_lock Δ m) (renseen (σ x) ξ) (snd (vars Γ x)). *) *)
(*         (forall x, Typed (add_lock (remove_locks Δ) (owner_unqualified Γ x)) (renseen (σ x) ξ) (snd (vars Γ x))). *)

(*     Lemma TypedSubst_ext  : forall (Γ1 Γ2 : Ctxt) (σ1 σ2 : substitution) (ξ1 ξ2 : renaming) (Δ1 Δ2 : Ctxt), *)
(*         ctxt_equiv Γ1 Γ2 -> *)
(*         (forall n, σ1 n = σ2 n) -> *)
(*         (forall n, ξ1 n = ξ2 n) -> *)
(*         ctxt_equiv Δ1 Δ2 -> *)
(*         TypedSubst Γ1 σ1 ξ1 Δ1 -> *)
(*         TypedSubst Γ2 σ2 ξ2 Δ2. *)
(*     Proof using. *)
(*       intros Γ1 Γ2 σ1 σ2 ξ1 ξ2 Δ1 Δ2 Γ_eqv σ_eqv ξ_eqv Δ_eqv [al_eqv3 [pfx typd]]; split; [|split]; *)
(*         pose proof Γ_eqv as [vars_eqv1 [locks_eqv1 al_eqv1]]; *)
(*         pose proof Δ_eqv as [vars_eqv2 [locks_eqv2 al_eqv2]]. *)
(*       - rewrite <- al_eqv1; rewrite <- al_eqv2; exact al_eqv3. *)
(*       - intro n; rewrite <- locks_eqv1; rewrite <- locks_eqv2; rewrite <- ξ_eqv; apply pfx. *)
(*       - intros x. apply @type_ext with (Γ := add_lock (remove_locks Δ1) (owner_unqualified Γ1 x)); auto. *)
(*         rewrite <- σ_eqv. rewrite <- renseen_ext with (ξ1 := ξ1); auto. *)
(*         rewrite <- vars_eqv1. apply typd. *)
(*         admit. *)
(* Admitted. *)

(*     Lemma id_subst_typed: forall Γ, TypedSubst Γ (fun x => var x) (fun x => x) Γ. *)
(*     Proof using. *)
(*       intros Γ; split; [reflexivity |  split; [reflexivity| intro x; cbn]]. *)
(*       apply VarTyping with (m := owner_unqualified Γ x); cbn; auto. *)
(*     Qed.       *)

(*     Lemma substup_typed : forall Γ Δ σ ξ g τ, *)
(*         TypedSubst Γ σ ξ Δ -> TypedSubst (add_var Γ g τ) (substup σ) (renup ξ) (add_var Δ g τ). *)
(*     Proof using. *)
(*       intros Γ Δ σ ξ g τ [al_eqv [pfx typd]]; split; [exact al_eqv|split]; [|intros x]. *)
(*       - intro n; destruct n; cbn; [reflexivity | auto]. *)
(*       - destruct x; cbn in *; subst. *)
(*         -- admit. *)
(*         -- rewrite renseen_fusion. *)
(*            rewrite ren_renseen. cbn. rewrite <- renseen_fusion. rewrite <- ren_renseen. *)
(*            eapply weakening; [| apply typd; apply eq]. *)
(*            split; [|split]; try (intro y); cbn; auto. *)
(*            Unshelve. 4: apply le_n_S. *)
(*     Admitted. *)

(*     Lemma addlock_typedsubst : forall Γ Δ σ ξ m, *)
(*         TypedSubst Γ σ ξ Δ -> TypedSubst (add_lock Γ m) σ ξ (add_lock Δ m). *)
(*     Proof using. *)
(*       intros Γ Δ σ ξ m [al [pfx typd]]; split; [| split]; cbn; auto. *)
(*       - rewrite al; reflexivity. *)
(*       - intro n; apply mod_app_mono_l; apply pfx. *)
(*       - intros x. *)
(*         admit. *)
(*     Admitted. *)

(*     (* Lemma changelock_typedsubst : forall Γ Δ σ ξ {m1 m2} (inv1 : forall n, PrefixOf m1 (locks Γ n) \/ PrefixOf (locks Γ n) m2) *) *)
(*     (*                                 (inv2 : forall n, PrefixOf m1 (locks Δ n) \/ PrefixOf (locks Δ n) m2), *) *)
(*     (*     TypedSubst Γ σ ξ Δ -> *) *)
(*     (*     TypedSubst (change_lock Γ inv1) σ ξ (change_lock Δ inv2). *) *)
(*     (* Proof using. *) *)
(*     (*   intros Γ Δ σ ξ m1 m2 inv1 inv2 [al_eqv [pfx typd]]; split; [| split]. *) *)
(*     (*   - cbn; rewrite al_eqv; reflexivity. *) *)
(*     (*   - intro n; cbn. admit. *) *)
(*     (*   - intros x m eq. *) *)
(*     (*     cbn. apply typd. *) *)

      

        

(*     Theorem subst_typed : forall Γ Δ e σ ξ τ, Typed Γ e τ -> TypedSubst Γ σ ξ Δ -> Typed Δ (renseen (subst e σ) ξ) τ. *)
(*     Proof using. *)
(*       intros Γ Δ e σ ξ τ typed; revert Δ σ ξ; induction typed; try (rename σ into τ'); *)
(*         intros Γ'' σ ξ typeds; cbn; pose proof typeds as [al_eqv [pfx typd]]. *)
(*       all: try (econstructor; eauto; fail). *)
(*       - *)
        
(*       (* assert (snd (vars Γ n) = τ) as x_tau by (rewrite pf1; reflexivity); rewrite <- x_tau. *) *)
(*         (* apply @type_ext with (Γ := add_lock Γ'' base); [|symmetry; apply add_base_lock]. *) *)
(*         (* apply typd. rewrite pf2. rewrite mod_base_app; auto. rewrite pf1; reflexivity. *) *)
(*       - apply AtTyping. apply IHtyped. *)
(*         apply addlock_typedsubst; auto. *)
(*       - eapply LetTyping. apply IHtyped1; auto. *)
(*         apply IHtyped2; apply substup_typed;auto. *)
(*       - eapply CaseTyping. apply IHtyped1; auto. apply IHtyped2. 2: apply IHtyped3. all: apply substup_typed; auto. *)
(*       - apply LamTyping. apply IHtyped. apply substup_typed. auto. *)
(*       - eapply @SendTyping. reflexivity. *)
(*         apply IHtyped. *)
    (*     Qed.                                              *)


    Definition single_subst (e : expr) : substitution :=
      fun n =>
        match n with
        | 0 => e
        | S n => var n
        end.

    
    Theorem finite_subst_typed : forall (Γ : Ctxt) (Δ: FiniteCtxt) (e e' : expr) (m : mod) (τ τ' : type),
        Typed (addFiniteCtxt (add_var Γ m τ') Δ) e τ ->
        Typed (add_lock Γ m) e' τ' ->
        Typed (addFiniteCtxt Γ Δ) (subst e (substup_many (FiniteCtxtSize Δ) (single_subst e'))) τ.
    Proof using.
      intros Γ Δ e; revert Γ Δ; induction e; intros Γ Δ e'' m' τ τ' typd1 typd2;
        inversion typd1; subst; cbn; try (econstructor; eauto; fail).
      - destruct (Compare_dec.le_lt_dec (FiniteCtxtSize Δ) n) as [ size_Δ_le_n | n_lt_size_Δ].
        -- unfold substup_many. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
           rewrite vars_past_finite_ctxt in pf1; [| lia].
           rewrite AddFiniteCtxt_locks1 in pf1; [| lia].
           destruct (n - FiniteCtxtSize Δ) eqn:eq; cbn.
           --- eapply weakening. apply extend_rename.
               cbn in pf1. inversion pf1; subst; auto.
           --- assert (n0 + FiniteCtxtSize Δ - FiniteCtxtSize Δ = n0) as eq' by lia.
               eapply VarTyping.
               rewrite vars_past_finite_ctxt; [| lia]. rewrite eq'; exact pf1.
               rewrite AddFiniteCtxt_locks1; [| lia]. rewrite eq'. reflexivity.
        -- unfold substup_many. rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [| exact n_lt_size_Δ].
           pose proof (vars_in_finite_ctxt Γ Δ n n_lt_size_Δ) as eq1.
           pose proof (vars_in_finite_ctxt (add_var Γ m' τ') Δ n n_lt_size_Δ) as eq2.
           eapply VarTyping.
           rewrite eq1 in eq2; inversion eq2; subst. rewrite H1. rewrite pf1; reflexivity.
           pose proof (AddFiniteCtxt_locks2 Γ Δ n n_lt_size_Δ) as eq3.
           pose proof (AddFiniteCtxt_locks2 (add_var Γ m' τ') Δ n n_lt_size_Δ) as eq4.
           rewrite <- eq3 in eq4; inversion eq4; subst.
           reflexivity.
      - apply AtTyping.
        apply @type_ext with (Γ := addFiniteCtxt Γ (add_end_lock Δ p)); [| apply add_end_lock_eqv].
        rewrite <- add_end_lock_size with (m := p).
        apply IHe with (m := m') (τ' := τ'); auto.
        eapply type_ext; eauto. symmetry; apply add_end_lock_eqv.
      - apply @LetTyping with (τ := τ0).
        -- apply IHe1 with (m := m') (τ' := τ'); auto.
        -- eapply type_ext; [| apply add_end_var_eqv].
           rewrite subst_ext with (σ2 := substup_many (FiniteCtxtSize (add_end_var Δ p τ0)) (single_subst e'')).
           2: intro n; rewrite add_end_var_size; symmetry; apply substup_many_S.
           apply IHe2 with (m := m') (τ' := τ'); auto.
           eapply type_ext; [| symmetry; apply add_end_var_eqv]; auto.
      - apply @CaseTyping with (τ1 := τ1) (τ2 := τ2).
        -- apply IHe1 with (m := m') (τ' := τ'); auto.
        -- eapply type_ext; [| apply add_end_var_eqv].
           rewrite subst_ext with (σ2 := substup_many (FiniteCtxtSize (add_end_var Δ base τ1)) (single_subst e'')).
           2: intro n; rewrite add_end_var_size; symmetry; apply substup_many_S.
           apply IHe2 with (m := m') (τ' := τ'); auto.
           eapply type_ext; [| symmetry; apply add_end_var_eqv]; auto.
        -- eapply type_ext; [| apply add_end_var_eqv].
           rewrite subst_ext with (σ2 := substup_many (FiniteCtxtSize (add_end_var Δ base τ2)) (single_subst e'')).
           2: intro n; rewrite add_end_var_size; symmetry; apply substup_many_S.
           apply IHe3 with (m := m') (τ' := τ'); auto.
           eapply type_ext; [| symmetry; apply add_end_var_eqv]; auto.
      - apply @LamTyping with (τ1 := t).  
        eapply type_ext; [| apply add_end_var_eqv].
        rewrite subst_ext with (σ2 := substup_many (FiniteCtxtSize (add_end_var Δ base t)) (single_subst e'')).
        2: intro n; rewrite add_end_var_size; symmetry; apply substup_many_S.
        apply IHe with (m := m') (τ' := τ'); auto.
        eapply type_ext; [| symmetry; apply add_end_var_eqv]; auto.
      - unshelve (eapply @SendTyping; [reflexivity | | auto]).
        -- destruct (Compare_dec.le_gt_dec (FiniteCtxtSize Δ) seen).
           --- assert (locks (addFiniteCtxt Γ Δ) seen = locks (addFiniteCtxt (add_var Γ m' τ') Δ) (1 + seen)).
               repeat rewrite AddFiniteCtxt_locks1; try lia; apply f_equal.
               assert (1 + seen - FiniteCtxtSize Δ = S (seen - FiniteCtxtSize Δ)) by lia.
               rewrite H0; cbn; reflexivity.
               rewrite H0; transitivity (locks (addFiniteCtxt (add_var Γ m' τ') Δ) seen); auto.
               apply locks_mono; lia.
           --- assert (Some (locks (addFiniteCtxt Γ Δ) seen) = Some (locks (addFiniteCtxt (add_var Γ m' τ') Δ) seen))
                 by (repeat rewrite AddFiniteCtxt_locks2; auto).
               inversion H0; rewrite H2; exact locks_seen.
        -- 
      - unshelve (eapply @UpTyping; eauto).

        
  End Substitution.
  
End CorpsTypes.

