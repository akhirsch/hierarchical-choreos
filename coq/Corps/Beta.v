Require Import Syntax.
Require Import EqBool.
Require Import Types.

Section BetaReduction.

  Context {PName : Type} `{EqBool PName}.
  #[local] Notation type := (type PName).
  #[local] Notation expr := (expr PName).
  #[local] Notation mod := (mod PName).
  Context {CanSend CanUp CanDown : mod -> mod -> Prop}.
  #[local] Notation Typed := (@Typed PName CanSend CanUp CanDown).
  #[local] Notation TypedSubst := (@TypedSubst PName CanSend CanUp CanDown).

  Definition single_subst (v : expr) : substitution :=
    fun n => match n with
          | 0 => v
          | S n' => var n'
          end.

  Lemma singlesubst_typed : forall (Γ : Ctxt) (v : expr) (τ : type),
      Typed Γ v τ -> TypedSubst (add_var Γ base τ) (single_subst v) Γ.
  Proof using.
    intros Γ v τ typ; split; cbn; [reflexivity| intros x m eq].
    destruct x; cbn in *; subst.
    - apply type_ext with (Γ := Γ); [exact typ | apply add_base_lock].
    - apply @VarTyping with (m := mod_app m (locks Γ x)); cbn; [|reflexivity].
      rewrite eq; apply surjective_pairing.
  Qed.

  (* substitute v for the variable 0 in e *)
  Definition subst1 (e v : expr) :=
    subst e (single_subst v).

  Lemma subst1_typed : forall Γ e v τ1 τ2,
      Typed (add_var Γ base τ1) e τ2 ->
      Typed Γ v τ1 ->
      Typed Γ (subst1 e v) τ2.
  Proof using.
    intros Γ e v τ1 τ2 typed_e typed_v; 
      unfold subst1; apply subst_typed with (Γ := add_var Γ base τ1);
      [ exact typed_e
      | apply singlesubst_typed; exact typed_v
      ].
  Qed.

  Inductive stepβ : expr -> expr -> Prop :=
    stepAt (p : PName) {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (atE p e1) (atE p e2)
  | stepLet1 (p : PName) {e11 e12 : expr} (step : stepβ e11 e12) (e2 : expr)
    : stepβ (letAt p e11 e2) (letAt p e12 e2)
  | stepLet2 (p : PName) (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22)
    : stepβ (letAt p e1 e21) (letAt p e1 e22)
  | stepLetβ (p : PName) (e1 e2 : expr) :
    stepβ (letAt p (atE p e1) e2) (subst1 e2 e1)
  | stepPair1 {e11 e12 : expr} (step : stepβ e11 e12) (e2 : expr) : stepβ (pair e11 e2) (pair e12 e2)
  | stepPair2 (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22) : stepβ (pair e1 e21) (pair e1 e22)
  | stepPi1 {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (pi1 e1) (pi1 e2)
  | stepPi2 {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (pi2 e1) (pi2 e2)
  | stepPairβ1 (e1 e2 : expr) : stepβ (pi1 (pair e1 e2)) e1
  | stepPairβ2 (e1 e2 : expr) : stepβ (pi2 (pair e1 e2)) e2
  | stepInl {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (inl e1) (inl e2)
  | stepInr {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (inr e1) (inr e2)
  | stepCaseE1 {e11 e12 : expr} (step : stepβ e11 e12) (e2 e3 : expr)
    : stepβ (caseE e11 e2 e3) (caseE e12 e2 e3)
  | stepCaseE2 (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22) (e3 : expr)
    : stepβ (caseE e1 e21 e3) (caseE e1 e22 e3)
  | stepCaseE3 (e1 e2 : expr) {e31 e32 : expr} (step : stepβ e31 e32)
    : stepβ (caseE e1 e2 e31) (caseE e1 e2 e32)
  | stepCaseInl (e1 e2 e3 : expr) : stepβ (caseE (inl e1) e2 e3) (subst1 e2 e1)
  | stepCaseInr (e1 e2 e3 : expr) : stepβ (caseE (inr e1) e2 e3) (subst1 e3 e1)
  | stepEfqlInner {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (efql e1) (efql e2)
  | stepLam (t : type) {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (lam t e1) (lam t e2)
  | stepApp1 {e11 e12 : expr} (step : stepβ e11 e12) (e2 : expr)
    : stepβ (appE e11 e2) (appE e12 e2)
  | stepApp2 (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22)
    : stepβ (appE e1 e21) (appE e1 e22)
  | stepAppLam (t : type) (e1 e2 : expr) : stepβ (appE (lam t e1) e2) (subst1 e1 e2).

  
  Theorem preservation : forall e1 e2 Γ τ, Typed Γ e1 τ -> stepβ e1 e2 -> Typed Γ e2 τ.
  Proof using.
    intros e1 e2 Γ τ typ; revert e2; induction typ; intros e2' stp; inversion stp; subst;
      repeat match goal with
           | [ IH : forall e2, stepβ ?e e2 -> Typed ?G e2 ?τ, H : stepβ ?e ?e' |- _ ] =>
               lazymatch goal with
               | [_ : Typed G e' τ |- _ ] => fail
               | _ => pose proof (IH e' H)
               end
           end;
      try (econstructor; eauto; fail); try (inversion typ; subst; assumption).
    - inversion typ1; subst.
      unfold subst1.
      apply subst_typed with (Γ := add_var Γ (Types.ptm p) τ); auto.
      split; cbn; [reflexivity|].
      intros x m; destruct x; cbn; intro eq; subst; auto.
      apply @VarTyping with (m := mod_app m (locks Γ x)); cbn.
      rewrite eq; apply surjective_pairing.
      reflexivity.
    - inversion typ1; subst; eapply subst1_typed; eauto.
    - inversion typ1; subst; eapply subst1_typed; eauto.
    - inversion typ1; subst; eapply subst1_typed; eauto.
  Qed.

End BetaReduction.
