Require Import Base.EqBool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.


Set Implicit Arguments.
Section CorpsSyntax.

  Context {PName : Type} `{EqBool PName}.
  
  Section CorpsTypes.

    Inductive type : Type :=
      UnitT
    | VoidT
    | AtT : PName -> type -> type
    | TimesT : type -> type -> type
    | PlusT : type -> type -> type
    | ArrT : type -> type -> type.

    Fixpoint typ_eqb (t1 t2 : type) : bool :=
      match t1, t2 with
      | UnitT, UnitT => true
      | VoidT, VoidT => true
      | AtT p t1, AtT q t2 => eqb p q && typ_eqb t1 t2
      | TimesT t11 t12, TimesT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | PlusT t11 t12, PlusT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | ArrT t11 t12, ArrT t21 t22 => typ_eqb t11 t21 && typ_eqb t12 t22
      | _, _ => false
      end.

    #[global] Program Instance TypEqB : EqBool type :=
      {
        eqb := typ_eqb
      }.
    Next Obligation.
      revert y H0; solve_eqb_liebniz x.
    Defined.
    Next Obligation.
      solve_eqb_refl.
    Defined.

  End CorpsTypes.

  Section Modality.

    Inductive mod : Type :=
    | base : mod
    | cons (m : mod) (p : PName) : mod.

    Fixpoint mod_eqb (m1 m2 : mod) : bool :=
      match m1, m2 with
      | base, base => true
      | cons m1 p, cons m2 q => eqb p q && mod_eqb m1 m2
      | _, _ => false
      end.
    #[global] Program Instance ModEqB : EqBool mod :=
      {
        eqb := mod_eqb
      }.
    Next Obligation.
      revert y H0; solve_eqb_liebniz x.
    Defined.
    Next Obligation.
      solve_eqb_refl.
    Defined.

    Fixpoint mod_size (m : mod) : nat :=
      match m with
      | base => 0
      | cons m _ => S (mod_size m)
      end.

    Lemma mod_size_zero_to_base : forall m, mod_size m = 0 -> m = base.
    Proof using.
      intro m; destruct m; cbn; intro eq; [reflexivity | inversion eq].
    Qed.

    Fixpoint mod_app (m1 m2 : mod) : mod :=
      match m2 with
      | base => m1
      | cons m2 p => cons (mod_app m1 m2) p
      end.

    Lemma mod_app_comm : forall m1 m2 m3, mod_app (mod_app m1 m2) m3 = mod_app m1 (mod_app m2 m3).
    Proof using.
      intros m1 m2 m3; revert m1 m2; induction m3 as [| m3' IHm3' p]; intros m1 m2; cbn.
      - reflexivity.
      - f_equal; apply IHm3'.
    Qed.

    Lemma mod_app_base : forall m, mod_app m base = m. Proof using. intros m; reflexivity. Qed.

    Lemma mod_base_app : forall m, mod_app base m = m.
    Proof using.
      intro m; induction m; cbn; [|rewrite IHm]; reflexivity.
    Qed.

    Lemma mod_app_size : forall m1 m2, mod_size (mod_app m1 m2) = mod_size m1 + mod_size m2.
    Proof using.
      intros m1 m2; revert m1; induction m2 as [| m2' IHm2' p]; intro m1; cbn;
        [|rewrite IHm2']; lia.
    Qed.

    Lemma mod_app_id_inv : forall m1 m2, m1 = mod_app m1 m2 -> m2 = base.
    Proof using.
      intros m1 m2 eq.
      apply mod_size_zero_to_base.
      apply (f_equal mod_size) in eq; rewrite mod_app_size in eq.
      lia.
    Qed.

    Lemma mod_app_base_inv : forall m1 m2, mod_app m1 m2 = base -> m1 = base /\ m2 = base.
    Proof using.
      intros m1 m2 eq; destruct m1; destruct m2; try (inversion eq; fail); split; reflexivity.
    Qed.

    Definition proc_to_mod (p : PName) : mod := cons base p.

    Lemma proc_to_mod_inj : forall p q, proc_to_mod p = proc_to_mod q -> p = q.
    Proof using.
      intros p q H0; unfold proc_to_mod in H0; inversion H0; reflexivity.
    Qed.

    #[global] Coercion proc_to_mod : PName >-> mod.

    Inductive PrefixOf : mod -> mod -> Prop :=
    | PO_refl (m : mod) : PrefixOf m m
    | PO_step {m1 m2 : mod} (pf : PrefixOf m1 m2) (p : PName)
      : PrefixOf m1 (cons m2 p).

    #[global] Instance PrefixOfRefl : Reflexive PrefixOf := PO_refl.

    Lemma PrefixOf_peel : forall m1 m2, PrefixOf m1 m2 -> exists m2', m2 = mod_app m1 m2'.
    Proof using.
      intros m1 m2 pfx; induction pfx.
      - exists base; reflexivity.
      - destruct IHpfx as [m2' eq]; subst.
        exists (cons m2' p); reflexivity.
    Qed.

    Lemma PrefixOf_antisym : forall m1 m2, PrefixOf m1 m2 -> PrefixOf m2 m1 -> m1 = m2.
    Proof using.
      intros m1 m2 pfx1 pfx2.
      apply PrefixOf_peel in pfx1; destruct pfx1 as [m1' eq1].
      apply PrefixOf_peel in pfx2; destruct pfx2 as [m2' eq2].
      subst.
      rewrite mod_app_comm in eq2. apply mod_app_id_inv in eq2. apply mod_app_base_inv in eq2; destruct eq2; subst. cbn. reflexivity.
    Qed.

    #[global] Instance PrefixOfAntisym : Antisymmetric mod eq PrefixOf := PrefixOf_antisym.

    Lemma PrefixOf_trans : forall m1 m2 m3, PrefixOf m1 m2 -> PrefixOf m2 m3 -> PrefixOf m1 m3.
    Proof using.
      intros m1 m2 m3 pfx1 pfx2; revert m1 pfx1; induction pfx2 as [m2 | m2 m3 pf IHpf p];
        intros m1 pfx1.
      - exact pfx1.
      - apply PO_step; apply IHpf; exact pfx1.
    Qed.

    #[global] Instance PrefixOfTrans : Transitive PrefixOf := PrefixOf_trans.

    Lemma PrefixOf_size : forall m1 m2, PrefixOf m1 m2 -> mod_size m1 <= mod_size m2.
    Proof using.
      intros m1 m2 pfx; induction pfx; cbn; lia.
    Qed.

    Lemma mod_app_mono_l : forall m1 m2 m3, PrefixOf m1 m2 -> PrefixOf (mod_app m3 m1) (mod_app m3 m2).
    Proof using.
      intros m1 m2 m3 pfx; revert m3; induction pfx; intro m3; [reflexivity|].
      cbn; apply PO_step; apply IHpfx.
    Qed.

    Fixpoint prefixb (m1 m2 : mod) : bool :=
      if eqb m1 m2
      then true
      else match m2 with
           | base => false
           | cons m2' _ => prefixb m1 m2'
           end.

    Lemma prefixb_refl : forall m, prefixb m m = true.
    Proof using.
      intro m; destruct m; cbn; eq_bool; reflexivity.
    Qed.

    Lemma PrefixOf_prefixb : forall m1 m2, PrefixOf m1 m2 -> prefixb m1 m2 = true.
    Proof using.
      intros m1 m2 pfx; induction pfx; [apply prefixb_refl|].
      cbn; eq_bool; subst; [reflexivity| assumption].
    Qed.

    Lemma prefixb_PrefixOf : forall m1 m2, prefixb m1 m2 = true -> PrefixOf m1 m2.
    Proof using.
      intros m1 m2; revert m1; induction m2 as [| m2' IHm2' p]; intros m1 eq; cbn in eq;
        eq_bool; subst; try (constructor; auto; fail).
      inversion eq.
    Qed.

    Theorem PrefixOf_dec : forall m1 m2, {PrefixOf m1 m2} + {~ PrefixOf m1 m2}.
    Proof using H.
      intros m1 m2; destruct (prefixb m1 m2) eqn:eq.
      left; apply prefixb_PrefixOf; exact eq.
      right; intro H'; apply PrefixOf_prefixb in H'; rewrite H' in eq; inversion eq.
    Defined.

    Theorem PrefixOf_app : forall m1 {m2 m3}, PrefixOf m2 m3 -> PrefixOf (mod_app m1 m2) (mod_app m1 m3).
    Proof using.
      intros m1 m2 m3 pfx; revert m1; induction pfx as [m2 | m2 m3 pf IHpf p]; intro m1.
      - reflexivity.
      - cbn; constructor; apply IHpf.
    Qed.

    Fixpoint base_Prefix (m : mod) : PrefixOf base m :=
      match m with
      | base => PO_refl base
      | cons m p => PO_step (base_Prefix m) p
      end.

    Fixpoint remove_Prefix (m1 m2 : mod) : option mod :=
      if eqb m1 m2
      then Some base
      else match m2 with
           | base => None
           | cons m2' p =>
               match remove_Prefix m1 m2' with
               | None => None
               | Some m => Some (cons m p)
               end
           end.

    Lemma readd_remove_prefix : forall m1 m2 m3, remove_Prefix m1 m2 = Some m3 -> mod_app m1 m3 = m2.
    Proof using.
      intros m1 m2; revert m1; induction m2; intros m1 m3 eq; cbn in *;
        eq_bool; subst; try (inversion eq; subst); cbn; try reflexivity.
      destruct (remove_Prefix m1 m2) eqn:eq'; [|inversion eq].
      inversion H1; subst; clear H1; cbn.
      specialize (IHm2 m1 m eq'). rewrite IHm2. reflexivity.
    Qed.

    Lemma remove_all_mod : forall m, remove_Prefix m m = Some base.
    Proof using.
      intro m; destruct m; cbn; eq_bool; reflexivity.
    Qed.

    Lemma prefix_remove_Some : forall m1 m2, PrefixOf m1 m2 -> exists m, remove_Prefix m1 m2 = Some m.
    Proof using.
      intros m1 m2 pfx; induction pfx; cbn.
      - exists base; apply remove_all_mod.
      - eq_bool; subst; [exists base; reflexivity|].
        destruct IHpfx as [m IHpfx].
        exists (cons m p); rewrite IHpfx; reflexivity.
    Qed.

    Lemma remove_Some_prefix : forall m1 m2 m3, remove_Prefix m1 m2 = Some m3 -> PrefixOf m1 m2.
    Proof using.
      intros m1 m2; revert m1; induction m2; intros m1 m3 eq; cbn in eq;
        eq_bool; subst; try (econstructor; eauto; fail).
      inversion eq.
      destruct (remove_Prefix m1 m2) eqn:eq'; inversion eq; subst.
      specialize (IHm2 m1 m eq').
      constructor; auto.
    Qed.

    Definition mod_eq_dec  : forall (m1 m2 : mod), {m1 = m2} + {m1 <> m2}.
      refine (fix mod_eq_dec (m1 m2 : mod) :=
      match m1, m2 with
      | base, base => left eq_refl
      | base, cons m2' p => right (fun eq => _)
      | cons m1' p, base => right (fun eq => _)
      | cons m1' p, cons m2' q =>
          match EqBool.eq_dec p q with
          | left eq_p_q =>
              match mod_eq_dec m1' m2' with
              | left eq_12 => left _
              | right neq_12 => right (fun eq => _)
              end
          | right neq_p_q => right (fun eq => _)
      end
      end).
      all: try (inversion eq; fail).
      - rewrite eq_p_q; rewrite eq_12; reflexivity.
      - inversion eq; subst; apply neq_12; reflexivity.
      - inversion eq; subst; apply neq_p_q; reflexivity.
    Defined.

    Inductive PrefixOfT : mod -> mod -> Type :=
    | POT_refl (m : mod) : PrefixOfT m m
    | POT_step (m1 m2 : mod) (p : PName) (pfx : PrefixOfT m1 m2) : PrefixOfT m1 (cons m2 p).

    Fixpoint PrefixOfT2Prefix {m1 m2 : mod} (pfx : PrefixOfT m1 m2) : PrefixOf m1 m2 :=
      match pfx with
      | POT_refl m => PO_refl m
      | POT_step p pfx => PO_step (PrefixOfT2Prefix pfx) p
      end.

    Fixpoint base_PrefixT (m : mod) : PrefixOfT base m :=
      match m with
      | base => POT_refl base
      | cons m p => POT_step p (base_PrefixT m)
      end.

    Fixpoint PrefixOfT_dec (m1 m2 : mod) : option (PrefixOfT m1 m2) :=
      match mod_eq_dec m1 m2 with
      | left e => ltac:(rewrite e; exact (Some (POT_refl m2)))
      | right neq =>
          match m2 with
            | base =>
                match m1 with
                | base => Some (POT_refl base)
                | _ => None
                end
            | cons m2' q =>
                match PrefixOfT_dec m1 m2' with
                | Some pfxt => Some (POT_step q pfxt)
                | None => None
                end
          end
      end.

    Lemma Prefix2PrefixT : forall m1 m2, PrefixOf m1 m2 -> exists pfxt, PrefixOfT_dec m1 m2 = Some pfxt.
    Proof using.
      intros m1 m2 pfx; induction pfx; cbn.
      - destruct m; cbn.
        -- exists (POT_refl base); reflexivity.
        -- destruct (EqBool.eq_dec p p) as [e|n]; [|destruct (n eq_refl)].
           destruct (mod_eq_dec m m) as [e'|n]; [|destruct (n eq_refl)].
           exists (POT_refl (cons m p)).
           assert (e = eq_refl) by (apply (UIP_dec EqBool.eq_dec)).
           assert (e' = eq_refl) by (apply (UIP_dec EqBool.eq_dec)).
           rewrite H1; cbn. rewrite H0; cbn. reflexivity.
      - destruct (mod_eq_dec m1 (cons m2 p)); subst; cbn.
        -- exists (POT_refl (cons m2 p)); reflexivity.
        -- destruct IHpfx as [pfxt IHpfx]. rewrite IHpfx.
           eexists; reflexivity.
    Qed.

    Theorem PrefixT_equiv : forall m1 m2, PrefixOf m1 m2 <-> exists pfxt, PrefixOfT_dec m1 m2 = Some pfxt.
    Proof using.
      intros m1 m2; split; intro H0. exact (Prefix2PrefixT H0).
      destruct H0 as [pfxt H0]. apply PrefixOfT2Prefix; exact pfxt.
    Qed.

    Fixpoint remove_PrefixT (m1 m2 : mod) (pfx : PrefixOfT m1 m2) :=
      match pfx with
      | POT_refl m => base
      | POT_step p pfx' => cons (remove_PrefixT pfx') p
      end.

    
    Definition remove_Prefix' : forall (m1 m2 : mod) (pfx : PrefixOf m1 m2), mod.
      refine (fix remove_Prefix' m1 m2 pfx :=
      match mod_eq_dec m1 m2 with
      | left _ => base
      | right neq =>
          (match m2 as a return a = m2 -> mod with
          | base => fun eq => False_rect mod _
          | cons m2' p =>
              fun eq => cons (@remove_Prefix' m1 m2' _) p
          end) eq_refl
      end).
      - rewrite <- eq in pfx. inversion pfx; subst. destruct (neq eq_refl).
      - subst; inversion pfx; subst; [exfalso; apply neq; reflexivity | exact pf].
    Defined.
    
    (* Lemma remove_prefix_prime : forall (m1 m2 : mod) (pfx : PrefixOf m1 m2), *)
    (*     remove_Prefix m1 m2 = Some (remove_Prefix' pfx). *)
    (* Proof using. *)
    (*   intros m1 m2; revert m1; induction m2; intros m1; intro pfx; cbn; eq_bool; subst; *)
    (*     try (reflexivity). *)
    (*   - inversion pfx; subst. exfalso; apply neq; reflexivity. *)
    (*   - destruct (mod_eq_dec (cons m2 p) (cons m2 p)) as [e' | n]; [|destruct (n eq_refl)]. *)
    (*     reflexivity. *)
    (*   - destruct (mod_eq_dec m1 (cons m2 p)) as [e' | n]; [destruct (neq e')|]. *)
    (*     inversion pfx; subst. destruct (n eq_refl). *)

    (* Equations remove_Prefix' (m1 m2 : mod) (pfx : PrefixOf m1 m2) : mod := *)
    (*   { *)
    (*     remove_Prefix' m1 m2 pfx with dec_eq m1 m2 => { *)
    (*       remove_Prefix' m1 m2 pfx (left _) := base; *)
    (*       remove_Prefix' base base (PO_refl _) (right neq) with (neq eq_refl) => { }; *)
    (*       remove_Prefix' m1 (cons m2 p) (PO_step pf' p) (right neq) := cons (remove_Prefix' m1 m2 pf')     *)
    (*     } *)
    (*   }. *)
      
  End Modality.


  Section Contexts.

    Record Ctxt :=
      {
        vars : nat -> mod * type;
        locks : nat -> mod;
        all_locks : mod;
        locks_mono : forall n m, n <= m -> PrefixOf (locks n) (locks m);
        locks_bound : forall n, PrefixOf (locks n) all_locks
      }.
    
    Definition add_lock (Γ : Ctxt) (m : mod) : Ctxt :=
      {|
        vars n := vars Γ n;
        locks n := mod_app m (locks Γ n);
        all_locks := mod_app m (all_locks Γ);
        locks_mono := fun j k leq => PrefixOf_app m (locks_mono Γ leq);
        locks_bound := fun n => PrefixOf_app m (locks_bound Γ n); 
      |}.

    Program Definition prefixT_prefix_trans {m1 m2 m3 : mod} (pfx : PrefixOfT m1 m2) (pfx' : PrefixOf m2 m3) : PrefixOfT m1 m3 :=
      match PrefixOfT_dec m1 m3 with
      | Some pfxt => pfxt
      | None => False_rect _ _
      end.
    Next Obligation.
      apply PrefixOfT2Prefix in pfx.
      pose proof (PrefixOf_trans pfx pfx') as pfx''.
      apply Prefix2PrefixT in pfx''; destruct pfx'' as [pfx'' Hpfx''].
      rewrite Hpfx'' in Heq_anonymous. inversion Heq_anonymous.
    Qed.

    Inductive ConsTowerOn : mod -> mod -> Type :=
    | OneCons (p : PName) (m : mod) : ConsTowerOn (cons m p) m
    | MoreCons (p : PName) (m1 m2 : mod) (cto : ConsTowerOn m1 m2) : ConsTowerOn (cons m1 p) m2.

    Definition ConsTower_reduce : forall m1 m2 p, ConsTowerOn m1 (cons m2 p) -> ConsTowerOn m1 m2.
      intros m1 m2 p cto; dependent induction cto.
      apply MoreCons; apply OneCons.
      apply MoreCons. apply IHcto; auto.
    Defined.
    
    Definition ConsTowerOn_antirefl : forall m, ConsTowerOn m m -> False.
      intro m; induction m; intro cto.
      inversion cto.
      inversion cto; subst.
      - clear cto IHm; induction m; inversion H0; subst; apply IHm; auto.
      - apply ConsTower_reduce in cto0. apply IHm; auto.
    Defined.
    
    Definition ConsTowerOnPrefixT : forall m1 m2, ConsTowerOn m1 m2 -> PrefixOfT m1 m2 -> False.
      intros m1 m2 cot pfxt; induction pfxt.
      - apply ConsTowerOn_antirefl with (m := m); exact cot.
      - apply IHpfxt. apply ConsTower_reduce with (p := p). exact cot.
    Defined.

    
    Lemma UIprefixT : forall m1 m2 (pfx1 pfx2 : PrefixOfT m1 m2), pfx1 = pfx2.
    Proof using H PName.
      intros m1 m2 pfx1 pfx2; revert pfx1; induction pfx2; intro pfx1.
      - destruct m.
        -- dependent destruction pfx1; reflexivity.
        -- dependent destruction pfx1. reflexivity.
           exfalso; apply ConsTowerOnPrefixT with (m1 := cons m p) (m2 := m);
             [constructor | assumption].
      - dependent destruction pfx1.
        -- exfalso; clear IHpfx2; apply ConsTowerOnPrefixT in pfx2; auto; constructor.
        -- rewrite (IHpfx2 pfx1); reflexivity.
    Qed.
    
    Lemma remove_prefix_mono : forall (m1 m2 m3 : mod) (pfx1 : PrefixOfT m3 m1) (pfx2 : PrefixOfT m3 m2),
        PrefixOf m1 m2 -> PrefixOf (remove_PrefixT pfx1) (remove_PrefixT pfx2).
    Proof using.
      intros m1 m2 m3 pfx1 pfx2  pfx; revert m3 pfx1 pfx2; induction pfx; intros m3 pfx1 pfx2.
      - inversion pfx1; subst; rewrite (UIprefixT pfx1 pfx2); reflexivity.
      - admit.
    Admitted.
      

    Definition remove_lock (Γ : Ctxt) (m : mod) : option Ctxt.
      refine (match PrefixOfT_dec m (locks Γ 0) with
      | None => None
      | Some pfx =>
          Some ({|
                vars n :=  vars Γ n;
                locks n := @remove_PrefixT m (locks Γ n) (prefixT_prefix_trans pfx (@locks_mono Γ 0 n ltac:(lia)));
                all_locks := @remove_PrefixT m (all_locks Γ) (prefixT_prefix_trans pfx (@locks_bound Γ 0));
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

    Inductive FiniteCtxt : Type :=
    | emptyFC : FiniteCtxt
    | varFC (m : mod) (τ : type) (Δ : FiniteCtxt) : FiniteCtxt
    | lockFC (m : mod) (Δ : FiniteCtxt) : FiniteCtxt.

    Fixpoint FiniteCtxt_eqb (Γ Δ : FiniteCtxt) : bool :=
      match Γ, Δ with
      | emptyFC, emptyFC => true
      | varFC m1 τ1 Γ', varFC m2 τ2 Δ' => eqb m1 m2 && eqb τ1 τ2 && FiniteCtxt_eqb Γ' Δ'
      | lockFC m1 Γ', lockFC m2 Δ' => eqb m1 m2 && FiniteCtxt_eqb Γ' Δ'
      | _, _ => false 
      end.

    #[global] Program Instance FiniteCtxtEqBool : EqBool FiniteCtxt :=
      {
        eqb := FiniteCtxt_eqb;
      }.
    Next Obligation.
      revert y H0; solve_eqb_liebniz x.
    Defined.
    Next Obligation.
      solve_eqb_refl.
    Defined.

    Fixpoint addFiniteCtxt (Γ : Ctxt) (Δ : FiniteCtxt) : Ctxt :=
      match Δ with
      | emptyFC => Γ
      | varFC m τ Δ => addFiniteCtxt (add_var Γ m τ) Δ
      | lockFC m Δ => addFiniteCtxt (add_lock Γ m) Δ
      end.
    
  End Contexts.

  Section CorpsTerms.

    Inductive expr : Type :=
      var : nat -> expr
    | uu : expr
    | atE (p : PName) (e : expr) : expr
    | letAt (p : PName) (e1 e2 : expr) : expr
    | pair (e1 e2 : expr) : expr
    | pi1 (e : expr)
    | pi2 (e : expr)
    | inl (e : expr)
    | inr (e : expr)
    | caseE (e1 e2 e3 : expr)
    | efql (e : expr) (* ex falso quod libet; exfalso is taken by coq *)
    | lam (t : type) (e : expr)
    | appE (e1 e2 : expr)
    | send (e : expr) (p : PName) (Δ : FiniteCtxt) (q : PName)
    | up (e : expr) (p : PName) (Δ : FiniteCtxt)
    | down (e : expr) (p : PName) (Δ : FiniteCtxt).

    Fixpoint expr_eqb (e1 e2 : expr) : bool :=
      match e1, e2 with
      | var n, var m => eqb n m
      | uu, uu => true
      | atE p e1, atE q e2 => eqb p q && expr_eqb e1 e2
      | letAt p e11 e12, letAt q e21 e22 => eqb p q && expr_eqb e11 e21 && expr_eqb e12 e22
      | pair e11 e12, pair e21 e22 => expr_eqb e11 e21 && expr_eqb e12 e22
      | pi1 e1, pi1 e2 => expr_eqb e1 e2
      | pi2 e1, pi2 e2 => expr_eqb e1 e2
      | inl e1, inl e2 => expr_eqb e1 e2
      | inr e1, inr e2 => expr_eqb e1 e2
      | caseE e11 e12 e13, caseE e21 e22 e23 =>
          expr_eqb e11 e21 && expr_eqb e12 e22 && expr_eqb e13 e23
      | efql e1, efql e2 => expr_eqb e1 e2
      | lam t1 e1, lam t2 e2 => eqb t1 t2 && expr_eqb e1 e2
      | appE e11 e12, appE e21 e22 => expr_eqb e11 e21 && expr_eqb e12 e22
      | send e1 p1 Δ1 q1, send e2 p2 Δ2 q2 => expr_eqb e1 e2 && eqb Δ1 Δ2 && eqb p1 p2 && eqb q1 q2
      | up e1 p Δ1, up e2 q Δ2 => expr_eqb e1 e2 && eqb Δ1 Δ2 && eqb p q
      | down e1 p Δ1, down e2 q Δ2 => expr_eqb e1 e2 && eqb Δ1 Δ2 && eqb p q
      | _, _ => false 
      end.

    Theorem expr_eqb_liebniz : forall x y, expr_eqb x y = true -> x = y.
    Proof using.
      intro x; solve_eqb_liebniz x.
    Qed.

    Theorem expr_eqb_refl : forall x, expr_eqb x x = true.
    Proof using.
      intro x; solve_eqb_refl.
    Qed.
    
    #[global] Instance exprEqBool : EqBool expr :=
      {
        eqb := expr_eqb;
        eqb_liebniz := expr_eqb_liebniz;
        eqb_refl := expr_eqb_refl;
      }.

  End CorpsTerms.

  Section Renaming.

    Definition renaming : Type := nat -> nat.

    Definition id_renaming : renaming := fun n => n.

    Definition renup (ξ : renaming) : renaming :=
      fun n =>
        match n with
        | 0 => 0
        | S n => S (ξ n)
        end.

    Lemma renup_ext : forall (ξ1 ξ2 : renaming),
        (forall n, ξ1 n = ξ2 n) ->
        forall n, (renup ξ1) n = (renup ξ2) n.
    Proof using.
      intros ξ1 ξ2 ext_eq n; destruct n; cbn; [| rewrite ext_eq]; reflexivity.
    Qed.

    Lemma renup_id : forall n, (renup id_renaming) n = id_renaming n.
    Proof using.
      intro n; destruct n; unfold id_renaming; cbn; reflexivity.
    Qed.

    Lemma renup_fusion : forall ξ1 ξ2 : renaming,
      forall n, (fun n => renup ξ2 (renup ξ1 n)) n = renup (fun n => ξ2 (ξ1 n)) n.
    Proof using.
      intros ξ1 ξ2 n; destruct n; cbn; reflexivity.
    Qed.

    Lemma renup_id_below : forall ξ n,
        (forall m, m < n -> ξ m = m) ->
        forall m, m < S n -> renup ξ m = m.
    Proof using.
      intros ξ n id_bel m m_le_n; destruct m; cbn; [reflexivity|].
      rewrite id_bel; [reflexivity | lia].
    Qed.

    Fixpoint ren (e : expr) (ξ : renaming) : expr :=
      match e with
      | var x => var (ξ x)
      | uu => uu
      | atE p e => atE p (ren e ξ)
      | letAt p e1 e2 => letAt p (ren e1 ξ) (ren e2 (renup ξ))
      | pair e1 e2 => pair (ren e1 ξ) (ren e2 ξ)
      | pi1 e => pi1 (ren e ξ)
      | pi2 e => pi2 (ren e ξ)
      | inl e => inl (ren e ξ)
      | inr e => inr (ren e ξ)
      | caseE e1 e2 e3 => caseE (ren e1 ξ) (ren e2 (renup ξ)) (ren e3 (renup ξ))
      | efql e => efql (ren e ξ)
      | lam t e => lam t (ren e (renup ξ))
      | appE e1 e2 => appE (ren e1 ξ) (ren e2 ξ)
      | send e p Δ q => send (ren e ξ) p Δ q
      | up e p Δ => up (ren e ξ) p Δ
      | down e p Δ => down (ren e ξ) p Δ
      end.
    
    Lemma ren_ext : forall (ξ1 ξ2 : renaming),
        (forall n, ξ1 n = ξ2 n) ->
        forall e, ren e ξ1 = ren e ξ2.
    Proof using.
      intros ξ1 ξ2 ext_eq e; revert ξ1 ξ2 ext_eq; induction e; intros ξ1 ξ2 ext_eq; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall n, ?f n = ?g n |- context [?f ?n]] => rewrite (H n)
          | [ IH : forall ξ1 ξ2, (forall n, ξ1 n = ξ2 n) -> ren ?e ξ1 = ren ?e ξ2,
                H : forall n, ?f n = ?g n |- context[ren ?e ?f]] =>
              rewrite (IH f g H)
          | [H : forall n, ?f n = ?g n |- context[renup ?f]] =>
              pose proof (renup_ext f g H)
          end.
    Qed.


    Lemma ren_id : forall e, ren e id_renaming = e.
    Proof using.
      intro e; induction e; cbn;
        repeat match goal with
          | [|- ?a = ?a ] => reflexivity
          | [|- context[id_renaming _]] => unfold id_renaming; cbn
          | [ H : ren ?e id_renaming = ?e |- context[ren ?e id_renaming]] => rewrite H
          | [|- context[ren ?e (renup id_renaming)]] =>
              rewrite (ren_ext (renup id_renaming) id_renaming renup_id e)
          end.
    Qed.

    Lemma ren_fusion : forall e ξ1 ξ2, ren (ren e ξ1) ξ2 = ren e (fun n => ξ2 (ξ1 n)).
      intro e; induction e; intros ξ1 ξ2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ1 ξ2, ren (ren ?e ξ1) ξ2 = ren ?e (fun n => ξ2 (ξ1 n))
                            |-  context[ren (ren ?e ?f) ?g]] =>
              rewrite (IH f g)
          | [ |- context[ren ?e (fun n => renup ?g (renup ?f n))]] =>
              rewrite (ren_ext (fun n => renup g (renup f n)) (renup (fun n => g (f n)))
                         (renup_fusion f g) e)
          end.
    Qed.
  End Renaming.

  Section Substitution.

    Definition substitution : Type := nat -> expr.
    Definition id_substitution : substitution := var.

    Definition substup (σ : substitution) : substitution :=
      fun n =>
        match n with
        | 0 => var 0
        | S n => ren (σ n) S
        end.

    Lemma substup_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall n, substup σ1 n = substup σ2 n.
    Proof using.
      intros σ1 σ2 ext_eq n; destruct n; cbn; [|rewrite ext_eq]; reflexivity.
    Qed.

    Lemma id_substup :
      forall n, substup id_substitution n = id_substitution n.
    Proof using.
      intros n; destruct n; unfold id_substitution; cbn; reflexivity.
    Qed.

    Lemma renup_substup : forall ξ n,
        (fun n => var (renup ξ n)) n = substup (fun n => var (ξ n)) n.
    Proof using.
      intros ξ n; destruct n; cbn; reflexivity.
    Qed.

    Lemma substup_renup_fusion : forall ξ σ n,
        (fun n => substup σ (renup ξ n)) n = (substup (fun n => σ (ξ n))) n.
    Proof using.
      intros ξ σ n; destruct n; cbn; reflexivity.
    Qed.

    Lemma renup_substup_fusion : forall σ ξ n,
        (fun n => ren (substup σ n) (renup ξ)) n = (substup (fun n => ren (σ n) ξ)) n.
    Proof using.
      intros σ ξ n; destruct n; cbn; [reflexivity|].
      repeat rewrite ren_fusion; unfold renup; reflexivity.
    Qed.

    Lemma substup_id_below : forall σ n,
        (forall m, m < n -> σ m = var m) ->
        forall m, m < S n -> substup σ m = var m.
    Proof using.
      intros σ n id_below m m_lt_Sn; destruct m; cbn; [reflexivity|].
      rewrite id_below; [reflexivity|].
      lia.
    Qed.
    
    Fixpoint subst (e : expr) (σ : substitution) : expr :=
      match e with
      | var x => σ x
      | uu => uu
      | atE p e => atE p (subst e σ)
      | letAt p e1 e2 => letAt p (subst e1 σ) (subst e2 (substup σ))
      | pair e1 e2 => pair (subst e1 σ) (subst e2 σ)
      | pi1 e => pi1 (subst e σ)
      | pi2 e => pi2 (subst e σ)
      | inl e => inl (subst e σ)
      | inr e => inr (subst e σ)
      | caseE e1 e2 e3 =>
          caseE (subst e1 σ) (subst e2 (substup σ)) (subst e3 (substup σ))
      | efql e => efql (subst e σ)
      | lam t e => lam t (subst e (substup σ))
      | appE e1 e2 => appE (subst e1 σ) (subst e2 σ)
      | send e p Δ q => send (subst e σ) p Δ q
      | up e p Δ => up (subst e σ) p Δ
      | down e p Δ => down (subst e σ) p Δ
      end.

    Lemma subst_ext : forall σ1 σ2,
        (forall n, σ1 n = σ2 n) ->
        forall e, subst e σ1 = subst e σ2.
    Proof using.
      intros σ1 σ2 ext_eq e; revert σ1 σ2 ext_eq; induction e; intros σ1 σ2 ext_eq; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall n, ?f n = ?g n |- context[?f ?n]] => rewrite (H n)
          | [ IH : forall σ1 σ2, (forall n, σ1 n = σ2 n) -> subst ?e σ1 = subst ?e σ2,
                H : forall n, ?f n = ?g n |- context[subst ?e ?f]] =>
              rewrite (IH f g H)
          | [ H : forall n, ?f n = ?g n |- context[substup ?f] ] =>
              pose proof (substup_ext f g H)
          end.
    Qed.

    Lemma subst_id : forall e,
        subst e id_substitution = e.
    Proof using.
      intro e; induction e; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ |- context[id_substitution _]] => unfold id_substitution; cbn
          | [ IH : subst ?e ?f = ?e |- context[subst ?e ?f]] =>
              rewrite IH
          | [ |- context[subst ?e (substup id_substitution)]] =>
              rewrite (subst_ext (substup id_substitution) id_substitution
                         id_substup e)
          end.
    Qed.

    Lemma ren_subst : forall e ξ,
        ren e ξ = subst e (fun n => var (ξ n)).
    Proof using.
      intro e; induction e; intro ξ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ, ren ?e ξ = subst ?e (fun n => var (ξ n)) |- context[ren ?e ?f]] =>
              rewrite (IH f)
          | [ |- context[subst ?e (fun n => var (renup ?ξ n))]] =>
              rewrite (subst_ext (fun n => var (renup ξ n)) (substup (fun n => var (ξ n)))
                         (renup_substup ξ) e)
          end.
    Qed.
    
    Lemma ren_subst_fusion : forall e ξ σ,
        subst (ren e ξ) σ = subst e (fun n => σ (ξ n)).
    Proof using.
      intro e; induction e; intros ξ σ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ σ, subst (ren ?e ξ) σ = subst ?e (fun n => σ (ξ n))
                          |- context[subst (ren ?e ?ξ) ?σ]] =>
              rewrite (IH ξ σ)
          | [ |- context[subst ?e (fun n => substup σ (renup ξ n))]] =>
              rewrite (subst_ext (fun n => substup σ (renup ξ n)) (substup (fun n => σ (ξ n)))
                         (substup_renup_fusion ξ σ) e)
          end.
    Qed.
    
    Lemma subst_ren_fusion : forall e σ ξ,
        ren (subst e σ) ξ = subst e (fun n => ren (σ n) ξ).
    Proof using.
      intro e; induction e; intros σ ξ; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall σ ξ, ren (subst ?e σ) ξ = subst ?e (fun n => ren (σ n) ξ)
                          |- context[ren (subst ?e ?σ) ?ξ]] =>
              rewrite (IH σ ξ)
          | [|- context[subst ?e (fun n => ren (substup ?σ n) (renup ?ξ))]] =>
              rewrite (subst_ext (fun n => ren (substup σ n) (renup ξ))
                         (substup (fun n => ren (σ n) ξ))
                         (renup_substup_fusion σ ξ) e)
          end.
    Qed.

    Lemma substup_fusion : forall σ1 σ2 n,
        (fun n => subst (substup σ1 n) (substup σ2)) n = (substup (fun n => subst (σ1 n) σ2)) n.
    Proof using.
      intros σ1 σ2 n; destruct n; cbn; [reflexivity|].
      rewrite ren_subst_fusion; rewrite subst_ren_fusion.
      unfold substup; reflexivity.
    Qed.

    Theorem subst_fusion : forall e σ1 σ2,
        subst (subst e σ1) σ2 = subst e (fun n => subst (σ1 n) σ2).
    Proof using.
      intro e; induction e; intros σ1 σ2; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall σ1 σ2, subst (subst ?e σ1) σ2 = subst ?e (fun n => subst (σ1 n) σ2)
                            |- context[subst (subst ?e ?f) ?g]] =>
              rewrite (IH f g)
          | [ |- context[subst ?e (fun n => subst (substup ?f n) (substup ?g))]] =>
              rewrite (subst_ext (fun n => subst (substup f n) (substup g))
                         (substup (fun n => subst (f n) g))
                         (substup_fusion f g))
          end.
    Qed.

  End Substitution.

  Section Closure.

    Inductive closed_above : expr -> nat -> Prop :=
    | var_ca {n m : nat} (n_lt_m : n < m) : closed_above (var n) m
    | uu_ca (n : nat) : closed_above uu n
    | atE_ca (p : PName) {e : expr} {n : nat} (pf : closed_above e n) : closed_above (atE p e) n
    | letAt_ca (p : PName) {e1 e2 : expr} {n : nat}
        (pf1 : closed_above e1 n) (pf2 : closed_above e2 (S n)) : closed_above (letAt p e1 e2) n
    | pair_ca {e1 e2 : expr} {n : nat} (pf1 : closed_above e1 n) (pf2 : closed_above e2 n)
      : closed_above (pair e1 e2) n
    | pi1_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (pi1 e) n
    | pi2_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (pi2 e) n
    | inl_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (inl e) n
    | inr_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (inr e) n
    | caseE_ca {e1 e2 e3 : expr} {n : nat}
        (pf1 : closed_above e1 n)
        (pf2 : closed_above e2 (S n))
        (pf3 : closed_above e3 (S n))
      : closed_above (caseE e1 e2 e3) n
    | efql_ca {e : expr} {n : nat} (pf : closed_above e n) : closed_above (efql e) n
    | lam_ca (t : type) {e : expr} {n : nat} (pf : closed_above e (S n)) : closed_above (lam t e) n
    | app_ca {e1 e2 : expr} {n : nat} (pf1 : closed_above e1 n) (pf2 : closed_above e2 n)
      : closed_above (appE e1 e2) n
    | send_ca {e : expr} (Δ : FiniteCtxt) (p q : PName) {n : nat} (pf : closed_above e n)
      : closed_above (send e p Δ q) n
    | up_ca {e : expr} (p : PName) (Δ : FiniteCtxt) {n : nat} (pf : closed_above e n)
      : closed_above (up e p Δ) n
    | down_ca {e : expr} (p : PName) (Δ : FiniteCtxt) {n : nat} (pf : closed_above e n)
      : closed_above (down e p Δ) n.

    Fixpoint closed_aboveb (e : expr) (n : nat) : bool :=
      match e with
      | var x => PeanoNat.Nat.ltb x n
      | uu => true
      | atE p e => closed_aboveb e n
      | letAt p e1 e2 => closed_aboveb e1 n && closed_aboveb e2 (S n)
      | pair e1 e2 => closed_aboveb e1 n && closed_aboveb e2 n
      | pi1 e => closed_aboveb e n
      | pi2 e => closed_aboveb e n
      | inl e => closed_aboveb e n
      | inr e => closed_aboveb e n
      | caseE e1 e2 e3 => closed_aboveb e1 n && closed_aboveb e2 (S n) && closed_aboveb e3 (S n)
      | efql e => closed_aboveb e n
      | lam t e => closed_aboveb e (S n)
      | appE e1 e2 => closed_aboveb e1 n && closed_aboveb e2 n
      | send e p Δ q => closed_aboveb e n
      | up e p Δ => closed_aboveb e n
      | down e p Δ => closed_aboveb e n
      end.

    Lemma closed_aboveb_spec1 : forall e n, closed_aboveb e n = true -> closed_above e n.
    Proof using.
      intro e; induction e; cbn; intros m clsdb;
        repeat match goal with
          | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
          end;
        try (econstructor; eauto; fail).
      constructor; rewrite <- PeanoNat.Nat.ltb_lt; cbn; assumption.
    Qed.

    Lemma closed_aboveb_spec2 : forall e n, closed_above e n -> closed_aboveb e n = true.
    Proof using.
      intros e n clsd; induction clsd; cbn;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : ?P |- ?P ] => exact H
          | [ |- _ && _ = true ] => apply andb_true_intro; split
          | [ H : ?n < ?m |- match ?m with | 0 => false | S m' => PeanoNat.Nat.leb ?n m' end = true] =>
              let H' := fresh in
              pose proof ((proj2 (PeanoNat.Nat.ltb_lt n m)) H) as H';
              cbn in H';
              rewrite H';
              reflexivity
          end.
    Qed.

    Theorem closed_aboveb_spec : forall e n, closed_above e n <-> closed_aboveb e n = true.
    Proof using.
      intros e n; split; [apply closed_aboveb_spec2 | apply closed_aboveb_spec1].
    Qed.

    Theorem closed_above_mono : forall e n, closed_above e n -> forall m, n < m -> closed_above e m.
    Proof using.
      intros e n clsd; induction clsd; intros k n_lt_k;
        repeat match goal with
          | [ IH : forall m, S ?n < m -> closed_above ?e m, H : ?n < ?k |- _ ] =>
              lazymatch goal with
              | [_ : S n < S k |- _ ] => fail
              | _ => assert (S n < S k) by lia
              end
          end;
        try (econstructor; eauto; fail).
      * constructor; transitivity m; assumption.
    Qed.

    Corollary closed_above_mono' : forall e n, closed_above e n -> forall m, n <= m -> closed_above e m.
    Proof using.
      intros e n clsd m n_le_m.
      destruct (Compare_dec.le_lt_eq_dec n m n_le_m); [|subst; assumption].
      apply closed_above_mono with (n := n); assumption.
    Qed.

    Definition closed (e : expr) : Prop := closed_above e 0.

    Theorem closed_closed_above : forall e, closed e -> forall n, closed_above e n.
    Proof using.
      intros e clsd n; apply (closed_above_mono' clsd). apply le_0_n.
    Qed.
      
    Lemma closed_above_ren_id : forall e ξ n,
        (forall m, m < n -> ξ m = m) ->
        closed_above e n ->
        ren e ξ = e.
    Proof using.
      intro e; induction e; cbn; intros ξ k id_bel clsd; inversion clsd; subst;
        repeat match goal with
          | [ H : ?m < ?n, H' : forall m, m < ?n -> ?f m = m |- context[?f ?m]] => rewrite (H' m H)
          | [ |- ?a = ?a ] => reflexivity
          | [ IH : forall ξ n, (forall m, m < n -> ξ m = m) -> closed_above ?e n -> ren ?e ξ = ?e,
                H : forall m, m < ?n -> ?f m = m,
                H' : closed_above ?e ?n |-
                  context[ren ?e ?f]] =>
              rewrite (IH f n H H')
          | [ H : forall m, m < ?n -> ?f m = m |- context[renup ?f]] =>
              lazymatch goal with
              | [ _ : forall m, m < S ?n -> renup ?f m = m |- _ ] => fail
              | _ => pose proof (renup_id_below f H)
              end
          end.
    Qed.

    Corollary closed_ren_id : forall e, closed e -> forall ξ, ren e ξ = e.
    Proof using.
      intros e clsd ξ; apply (@closed_above_ren_id e ξ 0); [| exact clsd].
      intros m m_lt_z; inversion m_lt_z.
    Qed.

    Lemma closed_above_subst_id : forall e σ n,
        (forall m, m < n -> σ m = var m) ->
        closed_above e n ->
        subst e σ = e.
    Proof using.
      intro e; induction e; cbn; intros σ k id_bel clsd; inversion clsd; subst;
        repeat match goal with
          | [ |- ?a = ?a ] => reflexivity
          | [ H : forall m, m < ?n -> ?f m = var m, H' : ?m < ?n |- context[?f ?m]] => rewrite (H m H')
          | [ IH : forall σ n, (forall m, m < n -> σ m = var m) -> closed_above ?e n -> subst ?e σ = ?e,
                H' : forall m, m < ?n -> ?f m = var m,
                H'' : closed_above ?e ?n |- context[subst ?e ?f]] =>
              rewrite (IH f n H' H'')
          | [H : forall m, m < ?n -> ?f m = var m |- context[substup ?f]] =>
              lazymatch goal with
              | [_ : forall m, m < S n -> substup f m = var m |- _] => fail
              | _ => pose proof (substup_id_below f H)
              end
          end.
    Qed.

    Corollary closed_subst_id : forall e, closed e -> forall σ, subst e σ = e.
    Proof using.
      intros e clsd σ; apply closed_above_subst_id with (n := 0); [|exact clsd].
      intros m m_lt_0; inversion m_lt_0.
    Qed.

    Lemma renup_closed_above : forall ξ n k,
        (forall m, m < n -> ξ m < k) ->
        forall m, m < S n -> renup ξ m < S k.
    Proof using.
      intros ξ n k clsd_abv m m_lt_Sn; destruct m; cbn.
      apply PeanoNat.Nat.lt_0_succ.
      assert (ξ m < k) by (apply clsd_abv; lia); lia.
    Qed.

    Lemma ren_closed_above : forall e ξ n k,
        closed_above e n ->
        (forall m, m < n -> ξ m < k) ->
        closed_above (ren e ξ) k.
    Proof using.
      intros e; induction e; intros ξ k1 k2 clsd_e clsd_ξ; inversion clsd_e; subst; cbn;
        repeat match goal with
          | [ H : forall m, m < ?k1 -> ?f m < ?k2 |- context[renup ?f]] =>
              lazymatch goal with
              | [_ : forall m, m < S k1 -> renup f m < S k2 |- _ ] => fail
              | _ => pose proof (renup_closed_above f H)
              end
          end;
        try (econstructor; eauto; fail).
    Qed.

    Lemma substup_closed_above : forall σ n k,
        (forall m, m < n -> closed_above (σ m) k) ->
        forall m, m < S n -> closed_above (substup σ m) (S k).
    Proof using.
      intros σ n k clsd_abv m m_lt_Sn; destruct m; cbn.
      * constructor; apply PeanoNat.Nat.lt_0_succ.
      * apply ren_closed_above with (n := k). apply clsd_abv.
        all: intros; lia.
    Qed.

    Lemma subst_closed_above : forall e σ n k,
        closed_above e n ->
        (forall m, m < n -> closed_above (σ m) k) ->
        closed_above (subst e σ) k.
    Proof using.
      intro e; induction e; intros σ k1 k2 clsd_e clsd_σ; inversion clsd_e; subst; cbn;
        repeat match goal with
          | [ H : forall m, m < ?n -> closed_above (?σ m) ?k |- context[substup ?σ]] =>
              lazymatch goal with
              | [ _ : forall m, m < S n -> closed_above (substup σ m) (S k) |- _ ] => fail
              | _ => pose proof (substup_closed_above σ H)
              end
          end;
        try (econstructor; eauto; fail).
      apply clsd_σ; assumption.
    Qed.

    (* This is essentially a nameless version of the traditional free-variables function. *)
    Fixpoint min_closure (e : expr) : nat :=
      match e with
      | var x => S x
      | uu => 0
      | atE p e => min_closure e
      | letAt p e1 e2 => max (min_closure e1) (pred (min_closure e2))
      | pair e1 e2 => max (min_closure e1) (min_closure e2)
      | pi1 e => min_closure e
      | pi2 e => min_closure e
      | inl e => min_closure e
      | inr e => min_closure e
      | caseE e1 e2 e3 => max (min_closure e1) (max (pred (min_closure e2)) (pred (min_closure e3)))
      | efql e => min_closure e
      | lam t e => pred (min_closure e)
      | appE e1 e2 => max (min_closure e1) (min_closure e2)
      | send e p Δ q => min_closure e
      | up e p Δ => min_closure e
      | down e p Δ => min_closure e
      end.

    Theorem closed_above_min : forall e, closed_above e (min_closure e).
    Proof using.
      intro e; induction e; cbn; try (econstructor; eauto; fail).
      all: constructor; eapply closed_above_mono'; eauto; lia.
    Qed.

    Theorem open_below_min : forall e n, closed_above e n -> min_closure e <= n.
    Proof using.
      intros e n clsd; induction clsd; cbn; lia.
    Qed.
 
  End Closure.
End CorpsSyntax.

Arguments type : clear implicits.
Arguments expr : clear implicits.
Arguments mod : clear implicits.

    
