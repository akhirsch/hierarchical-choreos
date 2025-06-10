Require Import Base.EqBool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.
Import ListNotations.
From Stdlib Require Import Logic.JMeq.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Program.Wf.


Section Modality.
  Context {PName : Type} `{EqBool PName}.

  Inductive mod : Type :=
  | base : mod
  | cons (m : mod) (p : PName) : mod.

  Fixpoint mod2list (m : mod) : list PName :=
    match m with
    | base => []
    | cons m p => (mod2list m) ++ [p]
    end.

  Lemma mod2list_inj : forall (m1 m2 : mod) , mod2list m1 = mod2list m2 -> m1 = m2.
  Proof using.
    intro m1; induction m1; intros m2 eq; destruct m2; cbn in eq; subst; auto.
    - destruct (app_eq_nil _ _ ltac:(symmetry; exact eq)) as [H0 H1]; inversion H1.
    - destruct (app_eq_nil _ _ eq) as [H0 H1]; inversion H1.
    - apply app_inj_tail in eq; destruct eq; subst.
      apply IHm1 in H0; subst; reflexivity.
  Qed.        

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

  Lemma mod_size_list_length : forall m : mod, mod_size m = length (mod2list m).
  Proof using.
    intros m; induction m; cbn; auto.
    rewrite length_app; cbn.
    rewrite PeanoNat.Nat.add_1_r.
    f_equal; exact IHm.
  Qed.

  Lemma mod_size_zero_to_base : forall m, mod_size m = 0 -> m = base.
  Proof using.
    intro m; destruct m; cbn; intro eq; [reflexivity | inversion eq].
  Qed.

  Fixpoint mod_app (m1 m2 : mod) : mod :=
    match m2 with
    | base => m1
    | cons m2 p => cons (mod_app m1 m2) p
    end.

  Lemma mod_app2list : forall (m1 m2 : mod), mod2list (mod_app m1 m2) = (mod2list m1) ++ (mod2list m2).
  Proof using.
    intros m1 m2; revert m1; induction m2; intro m1; cbn.
    - symmetry; apply app_nil_r.
    - rewrite app_assoc; f_equal. apply IHm2.
  Qed.


  Lemma mod_app_assoc : forall m1 m2 m3, mod_app (mod_app m1 m2) m3 = mod_app m1 (mod_app m2 m3).
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

  Lemma mod_app_first_inj : forall (p q : PName) (m1 m2 : mod),
      mod_app p m1 = mod_app q m2 ->
      p = q /\ m1 = m2.
  Proof using.
    intros p q m1; revert p q; induction m1; cbn; intros q r m2 eq.
    destruct m2; inversion eq; subst; auto.
    symmetry in H1; apply mod_app_base_inv in H1; destruct H1; subst; auto.
    inversion H0.
    destruct m2; inversion eq; subst; auto.
    apply mod_app_base_inv in H1; destruct H1; subst; auto.
    inversion H0.
    apply IHm1 in H1; destruct H1; subst; auto.
  Qed.

  Fixpoint list2mod (l : list PName) : mod :=
    match l with
    | [] => base
    | p :: l' => mod_app p (list2mod l')
    end.

  Lemma list2mod_inj : forall (l1 l2 : list PName), list2mod l1 = list2mod l2 -> l1 = l2.
  Proof using.
    intro l1; induction l1; intros l2 eq; cbn in *.
    - destruct l2; cbn in eq; auto;
        symmetry in eq; apply mod_app_base_inv in eq; destruct eq as [eq0 eq1]; inversion eq0.
    - destruct l2; cbn in eq; auto.
      -- apply mod_app_base_inv in eq; destruct eq as [eq0 eq1]; inversion eq0.
      -- apply mod_app_first_inj in eq; destruct eq; subst; auto.
         apply IHl1 in H1; subst; reflexivity.
  Qed.

  Lemma list2mod2list : forall (l : list PName),
      mod2list (list2mod l) = l.
  Proof using.
    intro l; induction l; cbn; auto.
    rewrite mod_app2list; cbn. f_equal; exact IHl.
  Qed.

  Lemma app2mod_app : forall (l1 l2 : list PName),
      list2mod (l1 ++ l2) = mod_app (list2mod l1) (list2mod l2).
  Proof using.
    intro l1; induction l1; cbn; intro l2.
    rewrite mod_base_app; reflexivity.
    rewrite IHl1. symmetry; apply mod_app_assoc.
  Qed.
  
  Lemma mod2list2mod : forall (m : mod),
      list2mod (mod2list m) = m.
  Proof using.
    intro m; induction m; cbn; auto.
    rewrite app2mod_app; cbn. f_equal; exact IHm.
  Qed.

  Inductive SuffixOf : mod -> mod -> Prop :=
  | SO_base (m : mod) : SuffixOf base m
  | SO_step {m1 m2 : mod} (sfx : SuffixOf m1 m2) (p : PName)
    : SuffixOf (cons m1 p) (cons m2 p).

  Fixpoint SO_refl (m : mod) : SuffixOf m m :=
    match m with
    | base => SO_base base
    | cons m' p => SO_step (SO_refl m') p
    end.

  #[global] Instance SuffixOfRefl : Reflexive SuffixOf := SO_refl.

  Lemma suffix_has_prefix : forall m1 m2, SuffixOf m1 m2 -> exists m3, mod_app m3 m1 = m2.
  Proof using.
    intros m1 m2 sfx; induction sfx; cbn.
    - exists m; reflexivity.
    - destruct IHsfx as [m3 eq]; exists m3; rewrite eq; reflexivity.
  Qed.

  Lemma suffix_of_prefixed : forall m1 m2, SuffixOf m2 (mod_app m1 m2).
  Proof using.
    intros m1 m2; revert m1; induction m2; intro m1; cbn.
    - apply SO_base.
    - apply SO_step. apply IHm2.
  Qed.

  Lemma has_prefix_is_suffix : forall m1 m2 m3, mod_app m3 m1 = m2 -> SuffixOf m1 m2.
  Proof using.
    intros m1; induction m1; cbn; intros m2 m3 eq; subst.
    apply SO_base.
    apply SO_step; apply suffix_of_prefixed.
  Qed.

  Theorem SuffixOf_iff : forall m1 m2, SuffixOf m1 m2 <-> exists m3, mod_app m3 m1 = m2.
  Proof using.
    intros m1 m2; split; [apply suffix_has_prefix | intros [m3 eq]].
    apply has_prefix_is_suffix with (m3 := m3); auto.
  Qed.

  Lemma SuffixOf_modapp : forall m1 m2 m3, SuffixOf m1 m2 -> SuffixOf (mod_app m1 m3) (mod_app m2 m3).
  Proof using.
    intros m1 m2 m3; induction m3; cbn; intro sfx; auto.
    apply SO_step; auto.
  Qed.

  Fixpoint extract_suffix (m1 m2 : mod) : option mod :=
    if eqb m1 m2
    then Some base
    else if PeanoNat.Nat.ltb (mod_size m1) (mod_size m2)
         then match m2 with
              | base => None
              | cons m2' p =>
                  match extract_suffix m1 m2' with
                  | Some m3 => Some (cons m3 p)
                  | None => None
                  end
              end
         else None.

  Lemma extract_suffix_spec1 : forall m1 m2 m3, extract_suffix m1 m2 = Some m3 -> m2 = mod_app m1 m3.
  Proof using.
    intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 eq.
    - eq_bool; inversion eq; subst;  reflexivity.
    - eq_bool; [inversion eq; clear eq|]; subst; cbn; [reflexivity|].
      destruct (PeanoNat.Nat.leb_spec (mod_size m1) (mod_size m2)); [|inversion eq].
      destruct (extract_suffix m1 m2) eqn:eq'; inversion eq; subst; clear eq.
      apply IHm2 in eq'; subst; cbn; reflexivity.
  Qed.

  Lemma extract_suffix_self : forall m, extract_suffix m m = Some base.
  Proof using.
    intro m; induction m; cbn; eq_bool; reflexivity.
  Qed.
  
  Lemma extract_suffix_spec2 : forall m1 m2, extract_suffix m1 (mod_app m1 m2) = Some m2.
  Proof using.
    intros m1 m2; revert m1; induction m2; cbn; intros m1; cbn; [apply extract_suffix_self|].
    eq_bool; subst.
    - exfalso. assert (mod_size m1 = mod_size (cons (mod_app m1 m2) p)) as eq_size by (f_equal; exact eq).
      cbn in eq_size; rewrite mod_app_size in eq_size; lia.
    - destruct (PeanoNat.Nat.leb_spec (mod_size m1) (mod_size (mod_app m1 m2))).
      2: { rewrite mod_app_size in H0; exfalso; lia. }
      rewrite IHm2; reflexivity.
  Qed.

  Theorem extract_suffix_spec : forall m1 m2 m3, extract_suffix m1 m2 = Some m3 <-> m2 = mod_app m1 m3.
  Proof using.
    intros m1 m2 m3; split; intro H0; [apply extract_suffix_spec1; auto | rewrite H0; apply extract_suffix_spec2].
  Qed.

  
  Inductive PrefixOf : mod -> mod -> Prop :=
  | PO_refl (m : mod) : PrefixOf m m
  | PO_step {m1 m2 : mod} (pf : PrefixOf m1 m2) (p : PName)
    : PrefixOf m1 (cons m2 p).

  #[global] Instance PrefixOfRefl : Reflexive PrefixOf := PO_refl.

  Lemma PrefixOf_base : forall m, PrefixOf base m.
  Proof using.
    intro m; induction m; constructor; auto.
  Qed.

  Lemma PrefixOf_app : forall m1 m2, PrefixOf m1 (mod_app m1 m2).
  Proof using.
    intros m1 m2; revert m1; induction m2; intro m1; cbn; constructor; auto.
  Qed.

  Lemma PrefixOf_peel : forall {m1 m2}, PrefixOf m1 m2 -> exists m2', m2 = mod_app m1 m2'.
  Proof using.
    intros m1 m2 pfx; induction pfx.
    - exists base; reflexivity.
    - destruct IHpfx as [m2' eq]; subst.
      exists (cons m2' p); reflexivity.
  Qed.

  Lemma PrefixOf_antisym : forall {m1 m2}, PrefixOf m1 m2 -> PrefixOf m2 m1 -> m1 = m2.
  Proof using.
    intros m1 m2 pfx1 pfx2.
    apply PrefixOf_peel in pfx1; destruct pfx1 as [m1' eq1].
    apply PrefixOf_peel in pfx2; destruct pfx2 as [m2' eq2].
    subst.
    rewrite mod_app_assoc in eq2. apply mod_app_id_inv in eq2. apply mod_app_base_inv in eq2; destruct eq2; subst. cbn. reflexivity.
  Qed.

  #[global] Instance PrefixOfAntisym : Antisymmetric mod eq PrefixOf := @PrefixOf_antisym.

  Lemma PrefixOf_trans : forall {m1 m2 m3 : mod}, PrefixOf m1 m2 -> PrefixOf m2 m3 -> PrefixOf m1 m3.
  Proof using.
    intros m1 m2 m3 pfx1 pfx2; revert m1 pfx1; induction pfx2 as [m2 | m2 m3 pf IHpf p];
      intros m1 pfx1.
    - exact pfx1.
    - apply PO_step; apply IHpf; exact pfx1.
  Qed.

  #[global] Instance PrefixOfTrans : Transitive PrefixOf := @PrefixOf_trans.

  Lemma PrefixOf_size : forall m1 m2, PrefixOf m1 m2 -> mod_size m1 <= mod_size m2.
  Proof using.
    intros m1 m2 pfx; induction pfx; cbn; lia.
  Qed.

  Lemma mod_app_mono_l : forall m1 m2 m3, PrefixOf m1 m2 -> PrefixOf (mod_app m3 m1) (mod_app m3 m2).
  Proof using.
    intros m1 m2 m3 pfx; revert m3; induction pfx; intro m3; [reflexivity|].
    cbn; apply PO_step; apply IHpfx.
  Qed.

  Lemma extract_suffix_prefix : forall m1 m2 m3, extract_suffix m1 m2 = Some m3 -> PrefixOf m1 m2.
  Proof using.
    intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 eq; eq_bool; try (inversion eq; subst; reflexivity; fail); subst.
    destruct (PeanoNat.Nat.leb_spec (mod_size m1) (mod_size m2)); [| inversion eq].
    destruct (extract_suffix m1 m2) eqn:eq'; inversion eq; subst; clear eq.
    apply IHm2 in eq'. apply PO_step. exact eq'.
  Qed.

  Lemma prefix_extract_suffix : forall m1 m2, PrefixOf m1 m2 -> exists m3, extract_suffix m1 m2 = Some m3.
  Proof using.
    intros m1 m2 pfx.
    destruct (PrefixOf_peel pfx) as [m3 eq]; subst.
    exists m3; apply extract_suffix_spec2.
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

  Theorem PrefixOf_app_mono : forall m1 {m2 m3}, PrefixOf m2 m3 -> PrefixOf (mod_app m1 m2) (mod_app m1 m3).
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
  | POT_step {m1 m2 : mod} (p : PName) (pfx : PrefixOfT m1 m2) : PrefixOfT m1 (cons m2 p).

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

  Lemma Prefix2PrefixT : forall {m1 m2}, PrefixOf m1 m2 -> exists pfxt, PrefixOfT_dec m1 m2 = Some pfxt.
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

  Fixpoint remove_PrefixT {m1 m2 : mod} (pfx : PrefixOfT m1 m2) :=
    match pfx with
    | POT_refl m => base
    | POT_step p pfx' => cons (remove_PrefixT pfx') p
    end.

  Lemma Snm_false :forall n m, ~ (S ( n + m) = n).
  Proof using.
    intro n; induction n; cbn; intros m eq; inversion eq; subst.
    apply IHn in H1; auto.
  Qed.

  Lemma Prefix_modapp_inv : forall m1 m2, PrefixOf (mod_app m1 m2) m1 -> m2 = base.
  Proof using.
    intro m1; induction m1; intros m2 pfx.
    - rewrite mod_base_app in pfx; inversion pfx; subst; reflexivity.
    - inversion pfx; subst.
      -- clear IHm1 pfx; induction m2; [reflexivity| cbn in *].
         inversion H2; subst.
         assert (mod_size (mod_app (cons m1 p) m2) = mod_size m1) as eq by (f_equal; exact H1).
         rewrite mod_app_size in eq; cbn in eq.
         apply Snm_false in eq; exfalso; auto.
      -- assert (cons m1 p = mod_app m1 (cons base p)) as eq by reflexivity; rewrite eq in pf.
         rewrite mod_app_assoc in pf. apply IHm1 in pf.
         clear eq pfx IHm1 m1.
         exfalso; induction m2; cbn in pf; inversion pf.
  Qed.           
  
  Lemma PrefixT_modapp_inv : forall m1 m2, PrefixOfT (mod_app m1 m2) m1 -> m2 = base.
  Proof using.
    intro m1; induction m1; intros m2 pfx.
    - rewrite mod_base_app in pfx; inversion pfx; subst; reflexivity.
    - inversion pfx; subst.
      -- clear IHm1 pfx; induction m2; [reflexivity| cbn in *].
         inversion H2; subst.
         assert (mod_size (mod_app (cons m1 p) m2) = mod_size m1) as eq by (f_equal; exact H1).
         rewrite mod_app_size in eq; cbn in eq.
         apply Snm_false in eq; exfalso; auto.
      -- assert (cons m1 p = mod_app m1 (cons base p)) as eq by reflexivity; rewrite eq in pfx0.
         rewrite mod_app_assoc in pfx0. apply IHm1 in pfx0.
         clear eq pfx IHm1 m1.
         exfalso; induction m2; cbn in pfx0; inversion pfx0.
  Qed.           
  
  Lemma PrefixT_cons_inv : forall m p, PrefixOfT (cons m p) m -> False.
  Proof using.
    intros m p.
    assert (cons m p = mod_app m (cons base p)) as eq by reflexivity; rewrite eq; intro pfx.
    apply PrefixT_modapp_inv in pfx.
    inversion pfx.
  Qed.

  Lemma remove_PrefixT_ext : forall (m1 m2 : mod) (pfx1 pfx2 : PrefixOfT m1 m2),
      remove_PrefixT pfx1 = remove_PrefixT pfx2.
  Proof using.
    intros m1 m2; revert m1; induction m2; intros m1 pfx1 pfx2.
    - inversion pfx1; subst.
      dependent destruction pfx1; dependent destruction pfx2; reflexivity.
    - dependent destruction pfx1; dependent destruction pfx2; cbn; auto.
      -- exfalso; apply PrefixT_cons_inv in pfx2; auto.
      -- exfalso; apply PrefixT_cons_inv in pfx1; auto.
      -- rewrite IHm2 with (pfx2 := pfx2); reflexivity.
  Qed.

  Program Fixpoint PrefixT_peel (m1 m2 : mod) : PrefixOfT m1 (mod_app m1 m2) :=
    match m2 with
    | base => POT_refl m1
    | cons m2 p => POT_step p (PrefixT_peel m1 m2)
    end.
  
  Lemma remove_PrefixT_app : forall (m1 m2 : mod) (pfx : PrefixOfT m1 (mod_app m1 m2)),
      remove_PrefixT pfx = m2.
  Proof using.
    intros m1 m2 pfx.
    rewrite remove_PrefixT_ext with (pfx2 := PrefixT_peel m1 m2); clear pfx.
    revert m1; induction m2; intro m1; cbn; auto.
    rewrite IHm2; reflexivity.
  Qed.
  
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

  Fixpoint remove_list_prefix  {A : Type} `{eqdec : EqBool A} (l1 l2 : list A) : option (list A) :=
    match l1, l2 with
    | [], _ => Some l2
    | (_ :: _), [] => None
    | (x :: xs), (y :: ys) => if eqb x y then remove_list_prefix xs ys else None
    end.

  Lemma remove_list_prefix_nil : forall {A : Type} `{eqdec :EqBool A} (l : list A), remove_list_prefix l l = Some [].
  Proof using.
    intros A eqdec l; induction l; cbn. reflexivity.
    eq_bool; auto.
  Qed.

  Lemma remove_list_prefix_front : forall {A : Type} `{eqbool : EqBool A} (l1 l2 l3 l4 : list A),
      remove_list_prefix l1 l2 = Some l3 ->
      remove_list_prefix l1 (l2 ++ l4) = Some (l3 ++ l4).
  Proof using.
    intros A eqbool l1; induction l1; intros l2 l3 l4 eq; cbn in *.
    - inversion eq; subst; reflexivity.
    - destruct l2; cbn in *. inversion eq.
      eq_bool; subst.
      -- apply IHl1; auto.
      -- inversion eq.
  Qed.

  Lemma remove_list_PrefixOf : forall (m1 m2 : mod), PrefixOf m1 m2 -> exists l, remove_list_prefix (mod2list m1) (mod2list m2) = Some l.
  Proof using.
    intros m1 m2 pfx; induction pfx; cbn.
    - exists []; apply remove_list_prefix_nil.
    - destruct IHpfx as [l' eq].
      exists (l' ++ [p]). apply remove_list_prefix_front. exact eq.
  Qed.
  
  
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

    Lemma cons_self_no : forall m p, m <> cons m p.
    Proof using.
      intro m; induction m; cbn; intros q eq; inversion eq; subst.
      apply IHm in H1; auto.
    Qed.

    Lemma cons_app_self_no1 : forall m1 m2 p, m1 <> cons (mod_app m1 m2) p.
    Proof using.
      intros m1 m2 p eq. assert (m1 = mod_app m1 (cons m2 p)) as H0 by exact eq; apply mod_app_id_inv in H0.
      inversion H0.
    Qed.

    Lemma mod_app_front : forall m1 m2 m3, mod_app m1 m2 = mod_app m1 m3 -> m2 = m3.
    Proof using.
      intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 eq.
      - apply mod_app_id_inv in eq; symmetry; exact eq.
      - destruct m3; cbn in eq. symmetry in eq; apply cons_app_self_no1 in eq; destruct eq.
        inversion eq; subst. apply IHm2 in H1; subst. reflexivity.
    Qed.

    Lemma mod_app_prefix : forall m1 m2 m3, PrefixOf (mod_app m1 m2) (mod_app m1 m3) -> PrefixOf m2 m3.
    Proof using.
      intros m1 m2 m3; revert m1 m2; induction m3; intros m1 m2 pfx.
      - apply Prefix_modapp_inv in pfx; subst; reflexivity.
      - inversion pfx; subst.
        2: { specialize (IHm3 _ _ pf); apply PO_step; exact IHm3. }
        assert (mod_app m1 m2 = mod_app m1 (cons m3 p)) as H0 by (exact H2); apply mod_app_front in H0; subst.
        reflexivity.
    Qed.

    Lemma common_suffix : forall m1 m2 m3, PrefixOf m1 m3 -> PrefixOf m2 m3 -> PrefixOf m1 m2 \/ PrefixOf m2 m1.
    Proof using.
      intros m1 m2 m3; revert m1 m2; induction m3; intros m1 m2 pfx1 pfx2.
      - inversion pfx1; inversion pfx2; subst; left; reflexivity.
      - inversion pfx1; subst; [right; exact pfx2|].
        inversion pfx2; subst; [left; exact pfx1|].
        apply IHm3; auto.
    Qed.

        Fixpoint change_prefix_t {m1 m2 : mod} (pfx1 : PrefixOfT m1 m2) (m3 : mod) : mod :=
      match pfx1 with
      | POT_refl _ => m3
      | POT_step p pfx => cons (change_prefix_t pfx m3) p
      end.

    Lemma change_prefix_t_prefix : forall {m1 m2 : mod} (pfx : PrefixOfT m1 m2) (m3 : mod),
        PrefixOf m3 (change_prefix_t pfx m3).
    Proof using.
      intros m1 m2 pfx; dependent induction pfx; intro m3; cbn.
      reflexivity.
      apply PO_step; apply IHpfx.
    Qed.

    Fixpoint PrefixT_app (m1 m2 : mod) : PrefixOfT m1 (mod_app m1 m2) :=
      match m2 with
      | base => POT_refl m1
      | cons m2' p => POT_step p (PrefixT_app m1 m2')
      end.

    Lemma change_prefix_t_spec : forall m1 m2 m3, change_prefix_t (PrefixT_app m1 m2) m3 = mod_app m3 m2.
    Proof using.
      intros m1 m2; revert m1; induction m2; intros m1 m3; cbn.
      reflexivity.
      f_equal; apply IHm2.
    Qed.

    Fixpoint change_prefix (m1 m2 m3 : mod) : option mod :=
      if eqb m1 m2
      then Some m3
      else match m2 with
           | base => None
           | cons m2' p =>
               match change_prefix m1 m2' m3 with
               | None => None
               | Some m => Some (cons m p)
               end
           end.

    Theorem change_prefix_of_prefix : forall (m1 m2 m3 : mod),
        PrefixOf m1 m2 ->
        change_prefix m1 m2 m3 <> None.
    Proof using.
      intros m1 m2; revert m1; induction m2; intros m1 m3 pfx; cbn; eq_bool; subst; try discriminate.
      - inversion pfx; subst; exfalso; apply neq; reflexivity.
      - inversion pfx; subst; [exfalso; apply neq; reflexivity|].
        destruct (change_prefix m1 m2 m3) eqn:eq; [discriminate|].
        exfalso; apply IHm2 with (m1 := m1) (m3 := m3); auto.
    Qed.

    Lemma cons_prefix : forall m1 m2 p, PrefixOf (cons m1 p) m2 -> PrefixOf m1 m2.
    Proof using H PName.
      intros m1 m2 p pfx; dependent induction pfx.
      - apply PO_step; reflexivity.
      - specialize (IHpfx H m1 p eq_refl); apply PO_step; apply IHpfx.
    Qed.
    
    Lemma extended_suffix_not_prefix : forall m1 m2 p, PrefixOf m1 m2 -> ~ (PrefixOf (cons m2 p) m1).
    Proof using H PName.
      intros m1; induction m1; intros m2 q pfx1 pfx2.
      - inversion pfx2.
      - inversion pfx2; subst.
        apply IHm1 with (m2 := m1) (p := p); [reflexivity | exact pfx1].
        apply (IHm1 m2 q); [apply cons_prefix with (p := p); exact pfx1 | exact pf].
    Qed.

    Theorem change_prefix_of_suffix : forall {m1 m2 : mod} (m3 : mod),
        PrefixOf m2 m1 ->
        change_prefix m1 m2 m3 = None \/ m1 = m2.
    Proof using.
      intros m1 m2; revert m1; induction m2; intros m1 m3 pfx; cbn; eq_bool; subst; auto.
      left.
      assert (PrefixOf m2 m1). clear IHm2 m3 e neq; dependent induction pfx. apply PO_step; apply PO_refl.
      specialize (IHpfx H m2 p eq_refl). apply PO_step; exact IHpfx.
      destruct (IHm2 m1 m3 H0); [rewrite H1; reflexivity| subst].
      apply extended_suffix_not_prefix  with (p := p) in pfx.
      exfalso; apply pfx; reflexivity.
    Qed.      

    Lemma change_prefix_of_prefix' : forall (m1 m2 m2' m3 m4 m4' : mod),
        change_prefix m1 m2 m3 = Some m4 ->
        change_prefix m1 m2' m3 = Some m4' ->
        PrefixOf m2 m2' ->
        PrefixOf m4 m4'.
    Proof using.
      intros m1 m2 m2' m3 m4 m4' H0 H1 pfx2; revert m1 m3 m4 m4' H0 H1; dependent induction pfx2;
        [| rename m1 into m5; rename m2 into m5']; intros m1 m3 m4 m4' eq0 eq1.
      - rewrite eq0 in eq1; inversion eq1; reflexivity.
      - cbn in eq1; cbn in eq0; eq_bool; subst.
        -- inversion eq1; subst; clear eq1.
           destruct (change_prefix_of_suffix m4'  (PO_step pfx2 p)); subst.
           rewrite H0 in eq0; inversion eq0.
           cbn in eq0; eq_bool; inversion eq0; subst; reflexivity.
        -- destruct (change_prefix m1 m5' m3) eqn:eq2; inversion eq1; subst; clear eq1.
           apply PO_step. apply IHpfx2 with (m1 := m1)(m3 := m3); auto.
    Qed.

    Lemma prefix_of_change_prefix : forall (m1 m2 m3 m4 m5 : mod),
        change_prefix m1 m2 m3 = Some m4 ->
        PrefixOf m5 m3 ->
        PrefixOf m5 m4.
    Proof using.
      intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 m4 m5 eq pfx; eq_bool; subst;
        try (inversion eq; subst; auto; fail).
      destruct (change_prefix m1 m2 m3) eqn:eq'; inversion eq; subst; clear eq.
      apply PO_step; eapply IHm2; eauto.
    Qed.

    Lemma only_prefixes_changable : forall m1 m2 m3 m4,
        change_prefix m1 m2 m3 = Some m4 ->
        PrefixOf m1 m2.
    Proof using.
      intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 m4 eq;
        eq_bool; subst; inversion eq; subst; clear eq; try reflexivity.
      destruct (change_prefix m1 m2 m3) eqn: eq; inversion H1; subst; clear H1.
      apply PO_step; eapply IHm2; eauto.
    Qed.

    Lemma prefix_changed_to_prefix : forall m1 m2 m3 m4,
        change_prefix m1 m2 m3 = Some m4 ->
        PrefixOf m3 m4.
    Proof using.
      intros m1 m2; revert m1; induction m2; cbn; intros m1 m3 m4 eq;
        eq_bool; subst; inversion eq; subst; clear eq; try reflexivity.
      destruct (change_prefix m1 m2 m3) eqn: eq; inversion H1; subst; clear H1.
      apply PO_step; eapply IHm2; eauto.
    Qed.

  
End Modality.
