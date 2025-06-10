Require Import EqBool.
Require Import Modalities.
Require Import Syntax.
Require Import Contexts.
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.


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

    Inductive TypedAtLevel : Ctxt -> nat -> expr -> type -> Prop :=
    | VarTyping {Γ : Ctxt} {l n : nat} {τ : type} (m : mod) (pf1 : vars Γ n = (m, τ)) (pf2 : locks Γ n = m)
      : TypedAtLevel Γ l (var n) τ
    | UnitTyping (Γ : Ctxt) (l : nat) : TypedAtLevel Γ l uu UnitT
    | AtTyping {Γ : Ctxt} {l : nat} {e : expr} {τ : type} (p : PName) (pf : TypedAtLevel (add_lock Γ p) l e τ)
      : TypedAtLevel Γ l (atE p e) (AtT p τ)
    | LetTyping {Γ : Ctxt} {l : nat} {e1 e2 : expr} {τ σ : type} {p : PName}
        (pf1 : TypedAtLevel Γ l e1 (AtT p τ)) (pf2 : TypedAtLevel (add_var Γ p τ) (S l) e2 σ)
      : TypedAtLevel Γ l (letAt p e1 e2) σ
    | PairTyping {Γ : Ctxt} {l : nat} {e1 e2 : expr} {τ1 τ2 : type}
        (pf1 : TypedAtLevel Γ l e1 τ1) (pf2 : TypedAtLevel Γ l e2 τ2)
      : TypedAtLevel Γ l (pair e1 e2) (TimesT τ1 τ2)
    | ProjLTyping {Γ : Ctxt} {l : nat} {e : expr} {τ1 τ2 : type}
        (pf : TypedAtLevel Γ l e (TimesT τ1 τ2))
      : TypedAtLevel Γ l (pi1 e) τ1
    | ProjRTyping {Γ : Ctxt} {l : nat} {e : expr} {τ1 τ2 : type}
        (pf : TypedAtLevel Γ l e (TimesT τ1 τ2))
      : TypedAtLevel Γ l (pi2 e) τ2
    | InlTyping {Γ : Ctxt} {l : nat} {e : expr} {τ1 τ2 : type}
        (pf : TypedAtLevel Γ l e τ1)
      : TypedAtLevel Γ l (inl e) (PlusT τ1 τ2)
    | InrTyping {Γ : Ctxt} {l : nat} {e : expr} {τ1 τ2 : type}
        (pf : TypedAtLevel Γ l e τ2)
      : TypedAtLevel Γ l (inr e) (PlusT τ1 τ2)
    | CaseTyping {Γ : Ctxt} {l : nat} {e1 e2 e3 : expr} {τ1 τ2 σ : type}
        (pf1 : TypedAtLevel Γ l e1 (PlusT τ1 τ2))
        (pf2 : TypedAtLevel (add_var Γ base τ1) (S l) e2 σ)
        (pf3 : TypedAtLevel (add_var Γ base τ2) (S l) e3 σ)
      : TypedAtLevel Γ l (caseE e1 e2 e3) σ
    | EfqlTyping {Γ : Ctxt} {l : nat} {e : expr}
        (pf : TypedAtLevel Γ l e VoidT) (τ : type)
      : TypedAtLevel Γ l (efql e) τ
    | LamTyping {Γ : Ctxt} {l : nat} {e : expr} {τ1 τ2 : type}
        (pf : TypedAtLevel (add_var Γ base τ1) (S l) e τ2)
      : TypedAtLevel Γ l (lam τ1 e) (ArrT τ1 τ2)
    | AppTyping {Γ : Ctxt} {l : nat} {e1 e2 : expr} {τ1 τ2 : type}
        (pf1 : TypedAtLevel Γ l e1 (ArrT τ1 τ2))
        (pf2 : TypedAtLevel Γ l e2 τ1)
      : TypedAtLevel Γ l (appE e1 e2) τ2
    | SendTyping {Γ Γ' : Ctxt} {l seen : nat} {m : mod} {p q : PName}  {e : expr} {τ : type}
        (locks_seen : locks Γ seen = cons m p)
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_send q locks_seen)))
        (pf : TypedAtLevel Γ' l e τ)
        (cs : CanSend (cons m p) (cons m q))
        (seen_at_level : seen <= l)
      : TypedAtLevel Γ l (send e seen m p q) τ
    | UpTyping {Γ Γ' : Ctxt} {l seen : nat} {m : mod} {p : PName} {e : expr} {τ : type}
        (locks_seen : locks Γ seen = m)
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_up p locks_seen)))
        (pf : TypedAtLevel Γ' l e τ)
        (cu : CanUp m (cons m p))
        (seen_at_level : seen <= l)
      : TypedAtLevel Γ l (up e seen m p) τ
    | DownTyping {Γ Γ' : Ctxt} {l seen : nat} {m : mod} {p : PName} {e : expr} {τ : type}
        (locks_seen : locks Γ seen = cons m p)
        (eqv : ctxt_equiv Γ' (change_lock Γ (change_lock_inv_down locks_seen)))
        (pf : TypedAtLevel Γ' l e τ)
        (cu : CanDown (cons m p) m)
        (seen_at_level : seen <= l)
      : TypedAtLevel Γ l (down e seen m p) τ
    .

    Definition Typed Γ e τ := TypedAtLevel Γ 0 e τ.

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

    Theorem type_level_ext : forall (Γ Δ : Ctxt) (l : nat) (e : expr) (τ : type),
        TypedAtLevel Γ l e τ -> (ctxt_equiv Γ Δ) -> TypedAtLevel Δ l e τ.
    Proof using.
      intros Γ Δ l e τ typd; revert Δ; induction typd; try (rename Δ into Γ'); intros Δ' eqv';
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
          | [ IH : forall Δ, ctxt_equiv (add_lock ?Γ ?m) Δ -> TypedAtLevel Δ ?l ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] =>
              lazymatch goal with
              | [ _ : TypedAtLevel (add_lock Δ m) l e τ |- _ ] => fail
              | _ => pose proof (IH (add_lock Δ m) (add_lock_ext Γ Δ m H))
              end
          | [ IH : forall Δ, ctxt_equiv (add_var ?Γ ?m ?τ') Δ -> TypedAtLevel Δ ?level ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] =>
              lazymatch goal with
              | [ _ : TypedAtLevel (add_var Δ m τ') level e τ |- _ ] => fail
              | _ => pose proof (IH (add_var Δ m τ') (add_var_ext Γ Δ m τ' H))
              end
          (* | [ IH : forall Δ, ctxt_equiv (addFiniteCtxt ?Γ ?E) Δ -> TypedAtLevel Δ ?l ?e ?τ, H : ctxt_equiv ?Γ ?Δ |- _ ] => *)
          (*     lazymatch goal with *)
          (*     | [ _ : Typed (addFiniteCtxt Δ E) l e τ |- _ ] => fail *)
          (*     | _ => pose proof (IH (addFiniteCtxt Δ E) (add_finite_ctxt_ext Γ Δ E H)) *)
          (*     end *)
          end;
        try (econstructor; eauto; fail).
      - apply @SendTyping with (Γ' := Γ') (locks_seen := H0); auto.
        etransitivity; [exact eqv | apply change_lock_ext; auto].
      - apply @UpTyping with (Γ' := Γ') (locks_seen := H0); auto.
        etransitivity; [exact eqv | apply change_lock_ext; auto].
      - apply @DownTyping with (Γ' := Γ') (locks_seen := H0); auto.
        etransitivity; [exact eqv | apply change_lock_ext; auto].
    Qed.

    Theorem type_ext : forall (Γ Δ : Ctxt) (e : expr) (τ : type),
        Typed Γ e τ -> (ctxt_equiv Γ Δ) -> Typed Δ e τ.
    Proof using.
      intros Γ Δ e τ H0 H1; eapply type_level_ext; eauto.
    Qed.
    
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

    Lemma renup_nochange : forall ξ l, (forall n, n < l -> ξ n = n) -> forall n, n < S l -> renup ξ n = n.
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


    Lemma weakening_at_level : forall (Γ Δ : Ctxt) (l : nat) (e : expr) (ξ : renaming) (τ : type)
                                 (locks_no_change : forall n, locks Γ n = locks Γ (ξ n)),
        ctxt_equiv (ctxt_ren Γ ξ (nolocks_change_mono locks_no_change)) Δ ->
        (forall n, n < l -> ξ n = n) ->
        TypedAtLevel Δ l e τ -> TypedAtLevel Γ l (ren e ξ) τ.
    Proof using.
      intros Γ Δ l e ξ τ mono eqv ξ_eq typ; revert Γ ξ mono eqv ξ_eq; induction typ; try rename Γ'' into Γ2;
        intros Γ'' ξ mono ctxt_eqv ξ_eq; cbn.
      all: pose proof ctxt_eqv as [vars_eqv [locks_eqv al_eqv]].
      all: try (econstructor; eauto; fail).
      - econstructor; eauto.
        rewrite <- mono.
        specialize (vars_eqv n); cbn in vars_eqv; rewrite vars_eqv.
        specialize (locks_eqv n); cbn in locks_eqv; rewrite locks_eqv.
        rewrite pf1. rewrite pf2. reflexivity.
      - econstructor; eauto.
        eapply IHtyp; eauto.
        split; [| split]; cbn; eauto.
        2: cbn in al_eqv; rewrite al_eqv; reflexivity.
        intro x; specialize (locks_eqv x); cbn in locks_eqv; rewrite locks_eqv; reflexivity.
        Unshelve. cbn; intro n; rewrite <- mono; reflexivity.
      - econstructor; eauto.
        eapply IHtyp2. 2: apply renup_nochange; auto. split; [| split]; try intro x; cbn; auto.
        all: destruct x; cbn; auto. apply vars_eqv. apply locks_eqv.
        Unshelve. intro n; cbn; destruct n; cbn; [reflexivity | apply mono].
      - econstructor; eauto.
        eapply IHtyp2. 3: eapply IHtyp3. all: try eapply renup_nochange; eauto.
        all: split; [| split]; try intro x; cbn; try reflexivity; try destruct x; cbn; auto.
        1,3: apply vars_eqv. all: apply locks_eqv.
        Unshelve. all: intro n; destruct n; cbn; auto.
      - econstructor; eauto.
        eapply IHtyp; [|apply renup_nochange; auto].
        split; [| split]; try intro x; cbn; auto; destruct x; cbn; auto.
        apply vars_eqv. apply locks_eqv.
        Unshelve. intro n; destruct n; cbn; auto.
      - assert (locks Γ'' (ξ seen) = cons m p) as locks_seen'
            by (specialize (locks_eqv seen); cbn in locks_eqv;
                rewrite locks_eqv; apply locks_seen).
        assert (locks Γ'' seen = cons m p) as locks_seen''
            by (rewrite mono; apply locks_seen').
        eapply @SendTyping with (Γ' := change_lock Γ'' (change_lock_inv_send q locks_seen'')); eauto;
          [reflexivity|].
        eapply IHtyp; auto.
        destruct eqv as [vars_eqv' [locks_eqv' al_eqv']].
        split; [| split]; cbn; try intro x.
        -- specialize (vars_eqv x); cbn in vars_eqv; rewrite vars_eqv.
           specialize (vars_eqv' x); cbn in vars_eqv'; symmetry; apply vars_eqv'.
        -- specialize (locks_eqv x); cbn in locks_eqv; rewrite locks_eqv.
           specialize (locks_eqv' x); cbn in locks_eqv'.
           symmetry; apply locks_eqv'.
        -- cbn in al_eqv; rewrite al_eqv; cbn in al_eqv'; symmetry; apply al_eqv'.
           Unshelve. intro n; cbn; rewrite <- mono; reflexivity.
      - 
          
        
        
        

  End TypeSystem.

  Section Substitution.

    Definition TypedSubst (Γ : Ctxt) (σ : substitution) (Δ : Ctxt) :=
      all_locks Γ = all_locks Δ /\
      forall x m,
        mod_app m (locks Γ x) = fst (vars Γ x) -> 
        Typed (add_lock Δ m) (σ x) (snd (vars Γ x)).

    Lemma id_subst_typed: forall Γ, TypedSubst Γ (fun x => var x) Γ.
    Proof using.
      intros Γ; split; [reflexivity | intros x m eq].
      apply VarTyping with (m := fst (vars Γ x)); cbn; auto.
      apply surjective_pairing.
    Qed.      

    Lemma substup_typed : forall Γ Δ σ g τ,
        TypedSubst Γ σ Δ -> TypedSubst (add_var Γ g τ) (substup σ) (add_var Δ g τ).
    Proof using.
      intros Γ Δ σ g τ [al_eqv typd]; split; [exact al_eqv|]; intros x m eq.
      destruct x; cbn in *; subst.
      - apply VarTyping with (m := g); cbn; reflexivity.
      - eapply weakening with (Δ := add_lock Δ m).
        split; [|split]; try (intro y); cbn; auto.
        apply typd; auto.
        Unshelve.
        intros n m0 H0; cbn; apply mod_app_mono_l; apply locks_mono; auto.
    Qed.

    Theorem subst_typed : forall Γ Δ e σ τ, Typed Γ e τ -> TypedSubst Γ σ Δ -> Typed Δ (subst e σ) τ.
    Proof using.
      intros Γ Δ e σ τ typed; revert Δ σ; induction typed; try (rename σ into τ');
        intros Γ'' σ typeds; cbn;
        try (econstructor; eauto;
             repeat lazymatch goal with
               | [ H : ?P |- ?P ] => exact H
               | [ IH : forall Δ σ, TypedSubst ?Γ σ Δ -> Typed Δ (subst ?e σ) ?τ, H : TypedSubst ?Γ ?σ ?Δ |- Typed ?Δ (subst ?e ?σ) ?τ ] =>
                   exact (IH Δ σ H)
               | [H : TypedSubst ?Γ ?σ ?Δ |- context[add_var ?Δ ?p ?τ] ] =>
                   lazymatch goal with
                   | [ _ : TypedSubst (add_var Γ p τ) (substup σ) (add_var Δ p τ) |- _ ] => fail
                   | _ => 
                       assert (TypedSubst (add_var Γ p τ) (substup σ) (add_var Δ p τ)) by (exact (substup_typed Γ Δ σ p τ H))
                   end
               | [ H : TypedSubst ?Γ ?σ ?Δ |- context[all_locks ?Δ]] =>
                   lazymatch goal with
                   | [_ : all_locks Γ = all_locks Δ |- _ ] => fail
                   | _ => let eq := fresh "eq" in assert (all_locks Γ = all_locks Δ) as eq by (destruct H as [al_eqv _]; exact al_eqv);
                                                rewrite <- eq
                   end
          end; fail).
      - destruct typeds as [al_eqv typeds].
        specialize (typeds n base); cbn in typeds.
        rewrite pf1 in typeds; cbn in typeds.
        rewrite mod_base_app in typeds; specialize (typeds pf2).
        apply type_ext with (Γ := add_lock Γ'' base); [exact typeds | symmetry; apply add_base_lock].
      - apply AtTyping; apply IHtyped.
        destruct typeds as [al_eqv typeds]; split; [cbn; rewrite al_eqv; reflexivity|].
        intros x m; cbn; intro eq.
        apply type_ext with (Γ := add_lock Γ'' (mod_app m p)); [|apply add_two_locks].
        rewrite <- mod_app_assoc in eq.
        apply typeds; exact eq.
    Qed.                                             

  End Substitution.
  
End CorpsTypes.

