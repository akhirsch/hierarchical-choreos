Require Import EqBool.
Require Import Syntax.
Require Import RelationClasses.
Require Import Lia.

Section CorpsTypes.
  Context {PName : Type} `{EqBool PName}.

  #[local] Notation type := (type PName).
  #[local] Notation expr := (expr PName).
  #[local] Notation mod := (mod PName).
  #[local] Definition ptm := @proc_to_mod PName.
  Coercion ptm : PName >-> mod.
  
  Section TypeSystem.

    Context {CanSend CanUp CanDown : mod -> mod -> Prop}.

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
    | SendTyping {Γ : Ctxt} {p q : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt (add_lock Γ p) Δ) e τ)
        (cs : CanSend (cons (all_locks Γ) p) (cons (all_locks Γ) q))
      : Typed (addFiniteCtxt (add_lock Γ q) Δ) (send e p Δ q) τ
    | UpTyping {Γ : Ctxt} {p : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt Γ Δ) e τ)
        (cu : CanUp (all_locks Γ) (cons (all_locks Γ) p))
      : Typed (addFiniteCtxt (add_lock Γ p) Δ) (up e p Δ) τ
    | DownTyping {Γ : Ctxt} {p : PName} {Δ : FiniteCtxt} {e : expr} {τ : type}
        (pf : Typed (addFiniteCtxt (add_lock Γ p) Δ) e τ)
        (cu : CanDown (cons (all_locks Γ) p) (all_locks Γ))
      : Typed (addFiniteCtxt Γ Δ) (down e p Δ) τ
    .

    
    

  End TypeSystem.  
  
End CorpsTypes.

