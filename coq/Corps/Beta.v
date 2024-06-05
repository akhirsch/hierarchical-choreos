Require Import Syntax.
Require Import EqBool.

Section BetaReduction.

  Context {PName : Type} `{EqBool PName}.
  #[local] Notation type := (type PName).
  #[local] Notation expr := (expr PName).

  (* substitute v for the variable 0 in e *)
  Definition singlesubst (e v : expr) :=
    subst e (fun n => match n with | 0 => v |S n' => var n' end).

  Inductive stepβ : expr -> expr -> Prop :=
    stepAt (p : PName) {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (atE p e1) (atE p e2)
  | stepLet1 (p : PName) {e11 e12 : expr} (step : stepβ e11 e12) (e2 : expr)
    : stepβ (letAt p e11 e2) (letAt p e12 e2)
  | stepLet2 (p : PName) (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22)
    : stepβ (letAt p e1 e21) (letAt p e1 e22)
  (* | stepLetβ (p : PName) (e1 e2 : expr) : *)
  (*   stepβ (letAt p (atE p e1) e2) (* Unclear what to do here! *) *)
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
  | stepCaseInl (e1 e2 e3 : expr) : stepβ (caseE (inl e1) e2 e3) (singlesubst e3 e1)
  (* Do I really want stepEfqlInner? *)
  | stepEfqlInner {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (efql e1) (efql e2)
  | stepEfql (e1 e2 : expr) : stepβ (efql e1) e2 (* Should e2 have to be in normal form? *)
  | stepLam (t : type) {e1 e2 : expr} (step : stepβ e1 e2) : stepβ (lam t e1) (lam t e2)
  | stepApp1 {e11 e12 : expr} (step : stepβ e11 e12) (e2 : expr)
    : stepβ (appE e11 e2) (appE e12 e2)
  | stepApp2 (e1 : expr) {e21 e22 : expr} (step : stepβ e21 e22)
    : stepβ (appE e1 e21) (appE e1 e22)
  | stepAppLam (t : type) (e1 e2 : expr) : stepβ (appE (lam t e1) e2) (singlesubst e1 e2).


End BetaReduction.
