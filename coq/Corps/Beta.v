Require Import Syntax.
Require Import EqBool.

Section BetaReduction.

  Context (PName : Type) `{EqBool PName}.
  #[local] Notation Typ := (Typ PName).
  #[local] Notation Expr := (Expr PName).

  (* substitute v for the variable 0 in e *)
  Definition singlesubst (e v : Expr) :=
    subst e (fun n => match n with | 0 => v |S n' => var _ n' end).
               

  Inductive stepβ : Expr -> Expr -> Prop :=
    stepAt (p : PName) {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (atE p e1) (atE p e2)
  | stepLet1 (p : PName) {e11 e12 : Expr} (step : stepβ e11 e12) (e2 : Expr)
    : stepβ (letAt p e11 e2) (letAt p e12 e2)
  | stepLet2 (p : PName) (e1 : Expr) {e21 e22 : Expr} (step : stepβ e21 e22)
    : stepβ (letAt p e1 e21) (letAt p e1 e22)
  (* | stepLetβ (p : PName) (e1 e2 : Expr) : *)
  (*   stepβ (letAt p (atE p e1) e2) (* Unclear what to do here! *) *)
  | stepPair1 {e11 e12 : Expr} (step : stepβ e11 e12) (e2 : Expr) : stepβ (pair e11 e2) (pair e12 e2)
  | stepPair2 (e1 : Expr) {e21 e22 : Expr} (step : stepβ e21 e22) : stepβ (pair e1 e21) (pair e1 e22)
  | stepPi1 {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (pi1 e1) (pi1 e2)
  | stepPi2 {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (pi2 e1) (pi2 e2)
  | stepPairβ1 (e1 e2 : Expr) : stepβ (pi1 (pair e1 e2)) e1
  | stepPairβ2 (e1 e2 : Expr) : stepβ (pi2 (pair e1 e2)) e2
  | stepInl {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (inl e1) (inl e2)
  | stepInr {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (inr e1) (inr e2)
  | stepCaseE1 {e11 e12 : Expr} (step : stepβ e11 e12) (e2 e3 : Expr)
    : stepβ (caseE e11 e2 e3) (caseE e12 e2 e3)
  | stepCaseE2 (e1 : Expr) {e21 e22 : Expr} (step : stepβ e21 e22) (e3 : Expr)
    : stepβ (caseE e1 e21 e3) (caseE e1 e22 e3)
  | stepCaseE3 (e1 e2 : Expr) {e31 e32 : Expr} (step : stepβ e31 e32)
    : stepβ (caseE e1 e2 e31) (caseE e1 e2 e32)
  | stepCaseInl (e1 e2 e3 : Expr) : stepβ (caseE (inl e1) e2 e3) (singlesubst e3 e1)
  (* Do I really want stepEfqlInner? *)
  | stepEfqlInner {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (efql e1) (efql e2)
  | stepEfql (e1 e2 : Expr) : stepβ (efql e1) e2 (* Should e2 have to be in normal form? *)
  | stepLam (t : Typ) {e1 e2 : Expr} (step : stepβ e1 e2) : stepβ (lam t e1) (lam t e2)
  | stepApp1 {e11 e12 : Expr} (step : stepβ e11 e12) (e2 : Expr) : stepβ (app e11 e2) (app e12 e2)
  | stepApp2 (e1 : Expr) {e21 e22 : Expr} (step : stepβ e21 e22) : stepβ (app e1 e21) (app e1 e22)
  | stepAppLam (t : Typ) (e1 e2 : Expr) : stepβ (app (lam t e1) e2) (singlesubst e1 e2).


End BetaReduction.
