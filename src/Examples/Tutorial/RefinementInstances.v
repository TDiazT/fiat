Require Export Refinement.
Require Import List.
Import ListNotations.

#[unfold_fix]
Symbol not_implemented : forall A, A.
Notation "?" := not_implemented.

Create HintDb icp.

Ltac exc_eauto := eauto with icp.

Symbol exc_list_ind : forall (A : Type) (P : list A -> Type) (Hnil : P nil)
  (Hcons : forall (a : A) (l : list A), P l -> P (cons a l))
  (Hnot_impl : P (? (list A)))
    (l : list A), P l.

Rewrite Rules exc_list_indRed :=
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl nil => ?Hnil
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl (cons ?a ?l) => ?Hcons ?a ?l (exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl ?l)
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl (? _) => ?Hnot_impl.

Rewrite Rules list_red_rew :=
  |  match @not_implemented (list ?A) as t0  return ?P with
     | nil => _
     | _ => _
     end => @not_implemented (?P@{t0 := (@not_implemented (list ?A))})
  |  match ? (list ?A) as t0  return ?P with
     | nil => _
     | _ => _
     end => @not_implemented (?P@{t0 := (? (list ?A))}).

Axioms
    (noconf_unk_nil : forall {A}, ? (list A) = @nil A -> False)
    (noconf_unk_cons : forall {A} (a : A) l, ? (list A) = cons a l -> False).

Hint Extern 0 => match goal with
  | [ H : ? (list ?A) = @nil _ |- _ ] => apply noconf_unk_nil in H; contradiction
    | [ H : ? (list ?A)  = cons _ _ |- _ ] => apply noconf_unk_cons in H; contradiction
    | [ H : @nil _ = ? (list ?A) |- _ ] => symmetry in H
    | [ H : cons _ _ = ? (list ?A) |- _ ] => symmetry in H
    | [|- context[? (list ?A) = @nil _]] => progress intros
    | [|- context[? (list ?A) = cons _ _]] => progress intros
    end : icp.

Section ListICP.
  Context {A : Type} `{HRA : Refinable A}.

  Reserved Infix "⊑l" (at level 70).
  Inductive refinement_list : list A -> list A -> Prop :=
  | is_refinement_nil : nil ⊑l nil
  | is_refinement_cons : forall (a a' : A) (l1 l2 : list A),
      a ⊑ a' -> l1 ⊑l l2 -> (cons a l1) ⊑l (cons a' l2)
  | is_refinement_unk : forall l, l ⊑l ? (list A)
  where "l1 ⊑l l2" := (refinement_list l1 l2).

  Hint Constructors refinement_list : icp.
  Hint Constructors refinement_list : typeclass_instances.

  #[export]
    Program Instance refinableList : Refinable (list A) :=
    { refinement := refinement_list }.
  Next Obligation.
    unfold Relation_Definitions.transitive; intros x; induction x as [| hd tl IH |] using exc_list_ind; intros ? ?; inversion 1; subst; inversion 1; subst; exc_eauto.
    constructor; eauto.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    intros l; induction l as [| hd tl IH |] using exc_list_ind; constructor; eauto.
    reflexivity.
  Qed.

  Lemma app_ref : forall (l l' k k' : list A),
      l ⊑ l' ->
      k ⊑ k' ->
      l ++ k ⊑ l' ++ k'.
  Proof.
    intros l l' k k' Hprec.
    induction Hprec.
    - simpl. auto.
    - simpl. intros Hprec'. constructor; auto.
      apply IHHprec; auto.
    - intros. cbn. constructor.
  Qed.

  Lemma app_ref_refl_inv_l : forall (l l' : list A),
      l ++ l' ⊑ l ++ l' ->
      l ⊑ l.
  Proof with eauto with icp.
    intros l; induction l as [| hd tl IH|] using exc_list_ind; intros l'...
    - constructor.
    - simpl. inversion 1; subst...
      constructor; auto. eapply IH; eauto.
  Qed.

  Lemma rev_ref : forall l l' : list A,
      l ⊑ l' ->
      rev l ⊑ rev l'.
  Proof with eauto with icp.
    induction l using exc_list_ind; intros l'; inversion 1; subst; eauto...
    - simpl. apply app_ref; eauto. constructor...
    - cbn. constructor.
  Qed.

  Context `{HCA : Complete A}.

  Inductive is_complete_list : list A -> Prop :=
  | is_complete_nil : is_complete_list nil
  | is_complete_cons : forall (a : A) (l : list A), is_complete a -> is_complete_list l -> is_complete_list (cons a l).

  Hint Constructors is_complete_list : icp.
  Hint Constructors is_complete_list : typeclass_instances.

  #[export]
    Instance completeList : Complete (list A) :=
    { is_complete := is_complete_list }.

  Lemma is_complete_app : forall l l' : list A,
      is_complete l ->
      is_complete l' ->
      is_complete (l ++ l').
  Proof.
    induction l using exc_list_ind; eauto; intros l'.
    inversion 1; subst; eauto. intros ?.
    simpl; constructor; eauto. apply IHl; eauto.
  Qed.

  Lemma is_complete_rev : forall l : list A,
      is_complete l ->
      is_complete (rev l).
  Proof.
    induction l using exc_list_ind; eauto.
    inversion 1; subst. simpl.
    apply is_complete_app; eauto.
    repeat constructor; eauto.
  Qed.

  Lemma is_complete_app_inv :
    forall l l' : list A, is_complete (l ++ l') ->
                     is_complete l /\ is_complete l'.
  Proof with eauto with icp.
    induction l using exc_list_ind; cbn; eauto.
    - split; eauto; constructor.
    - intros ? Hc. inversion Hc; subst. split; eauto.
      * constructor; eauto. apply (IHl l'); eauto.
      * apply IHl; eauto.
    - inversion 1...
  Qed.

  Lemma is_complete_rev_inv :
    forall l : list A, is_complete (rev l) -> is_complete l.
  Proof with eauto with icp.
    induction l using exc_list_ind...
    simpl. intros Hc.
    apply is_complete_app_inv in Hc.
    destruct Hc as [Hcl Hca].
    constructor; eauto.
    - inversion Hca; eauto.
    -
      apply IHl; eauto.
  Qed.

  #[export]
    Instance completeMinimalList `{@CompleteMinimal A HRA HCA} : CompleteMinimal (list A).
  Proof with eauto with icp.
    constructor; intros l; induction l as [|? ? IH |] using exc_list_ind; inversion 1; intros l'; inversion 1; subst...
    f_equal... eapply is_complete_minimal; eauto.
  Qed.

End ListICP.

#[export] Hint Constructors refinement_list : icp.
#[export] Hint Constructors refinement_list : typeclass_instances.
#[export] Hint Constructors is_complete_list : icp.
#[export] Hint Constructors is_complete_list : typeclass_instances.

#[export] Hint Resolve app_ref : typeclass_instances.
#[export] Hint Resolve rev_ref : typeclass_instances.
#[export] Hint Resolve is_complete_app : typeclass_instances.
#[export] Hint Resolve is_complete_rev : typeclass_instances.


Symbol exc_prod_ind :
  forall {A B}
          (P : A * B -> Type)
          (Hp : forall a b, P (a,b))
          (Hunk : P (? (A * B)))
          (p : A * B), P p.

Rewrite Rules exc_prod_ind_rew :=
| exc_prod_ind ?P ?Hp ?Hunk (?a,?b) => ?Hp ?a ?b
| exc_prod_ind ?P ?Hp ?Hunk (? _) => ?Hunk.

Rewrite Rules prod_red_rew :=
  |  match @not_implemented (?A * ?B) as t0  return ?P with
     | pair _ _ => _
     end => @not_implemented (?P@{t0 := (@not_implemented (?A * ?B))}).

Axioms
 (noconf_unk_prod : forall {A B} (p : A * B), ? (A * B) = p -> False)
.

Hint Extern 0 =>
    match goal with
    | [H : ? (?A * ?B) = (_, _) |- _] => apply noconf_unk_prod in H; contradiction
    | [H : (_, _) = ? (?A * ?B) |- _] => symmetry in H
    | [|- context[? (?A * ?B) = (_, _)]] => progress intros
    end : icp.


Section ProdICP.
  Context {A B : Type} `{HRA : Refinable A} `{HRB : Refinable B}.

  Inductive refinement_prod : A * B -> A * B -> Prop :=
  | is_refinement_pair : forall (a1 a2 : A) (b1 b2 : B),
      a1 ⊑ a2 -> b1 ⊑ b2 -> refinement_prod (a1, b1) (a2, b2)
  | is_refinement_pair_not_impl : forall ab, refinement_prod ab (? (A * B)).


  #[export, refine]
    Instance refinableProd : Refinable (A * B) :=
    {
      refinement := refinement_prod
    }.
  Proof with eauto with icp.
    - unfold Relation_Definitions.transitive; intros x; induction x using exc_prod_ind; intros ? ?; inversion 1; subst; inversion 1; subst; try constructor; try eapply is_transitive...
    - intros x. induction x using exc_prod_ind; constructor; apply is_reflexive.
  Defined.

  Hypotheses (HAnot_impl : forall a : A, a ⊑ ? A)
    (HBnot_impl : forall b : B, b ⊑ ? B).

  Lemma fst_ref : forall p p' : A * B,
      p ⊑ p' ->
      fst p ⊑ fst p'.
  Proof.
    intros ? ? Hprec.
    inversion Hprec; subst.
    - eauto.
    - cbn. apply HAnot_impl.
  Qed.

  Lemma snd_ref : forall p p' : A * B,
      p ⊑ p' ->
      snd p ⊑ snd p'.
  Proof.
    intros ? ? Hprec.
    destruct Hprec; cbn; eauto.
  Qed.

  Context `{HCA : Complete A} `{HCB : Complete B}.

  Inductive is_complete_prod : A * B -> Prop :=
  | is_complete_pair: forall (a : A) (b : B), is_complete a -> is_complete b -> is_complete_prod (a, b).

  #[export]
    Instance completeProd : Complete (A * B) :=
    {
      is_complete := is_complete_prod
    }.

  Lemma is_complete_fst : forall p : A * B,
      is_complete p ->
      is_complete (fst p).
  Proof.
    inversion 1; eauto.
  Qed.

  Lemma is_complete_snd : forall p : A * B,
      is_complete p ->
      is_complete (snd p).
  Proof.
    inversion 1; eauto.
  Qed.

  #[export]
    Instance completeMinimalProd `{@CompleteMinimal A HRA HCA} `{@CompleteMinimal B HRB HCB}: CompleteMinimal (A * B).
  Proof with eauto with icp.
    constructor; intros ab; induction ab; inversion 1; subst; intros ab'; induction ab'; inversion 1; subst...
    f_equal; apply is_complete_minimal...
  Qed.

End ProdICP.

#[export] Hint Constructors refinement_prod : icp.
#[export] Hint Constructors refinement_prod : typeclass_instances.
#[export] Hint Constructors is_complete_prod : icp.
#[export] Hint Constructors is_complete_prod : typeclass_instances.

#[export] Hint Resolve fst_ref : typeclass_instances.
#[export] Hint Resolve snd_ref : typeclass_instances.
#[export] Hint Resolve is_complete_fst : typeclass_instances.
#[export] Hint Resolve is_complete_snd : typeclass_instances.

Axioms
  (noconf_unk_none : forall {A}, ? (option A) = @None A -> False)
    (noconf_unk_some : forall {A} {a : A}, ? (option A) = Some a -> False)
.

#[export] Hint Extern 0 =>
  match goal with
  | [H : ? (option ?A) = None |- _] => apply noconf_unk_none in H; contradiction
  | [H : ? (option ?A) = Some _ |- _] => apply noconf_unk_some in H; contradiction
  | [H : None = ? (option ?A) |- _] => symmetry in H
  | [H : Some _ = ? (option ?A) |- _] => symmetry in H
  | [|- context[? (option ?A) = None]] => progress intros
  | [|- context[? (option ?A) = Some _]] => progress intros
  | [|- None <> ? (option ?A) ] => unfold not; intros
  | [|- Some _ <> ? (option ?A) ] => unfold not; intros
  end : icp.

Section OptionICP.
  Context {A : Type} {HRA : Refinable A}.

  Reserved Infix "⊑o" (at level 10).
  Inductive refinementOption : option A -> option A -> Prop :=
  | refinementOption_None : None ⊑o None
  | refinementOption_Some : forall a a', a ⊑ a' -> (Some a) ⊑o (Some a')
  | refinementOption_not_impl : forall a, a ⊑o (? (option A))
  where "o1 ⊑o o2" := (refinementOption o1 o2).

  Hint Constructors refinementOption : icp.
  Hint Constructors refinementOption : typeclass_instances.

  #[export]
    Program Instance refinableOption : Refinable (option A) :=
    { refinement := refinementOption }.
  Next Obligation with eauto with icp.
    unfold Relation_Definitions.transitive; intros [] [] [] H1 H2; try contradiction; eauto; inversion H1; subst; exc_eauto; try constructor...
    - inversion H2; subst; etransitivity; eauto...
    - inversion H2...
  Qed.
  Next Obligation.
    intros []; constructor. reflexivity.
  Qed.

  Context {HCA : Complete A}.

  Inductive is_complete_option : option A -> Prop :=
  | is_complete_option_None : is_complete_option None
  | is_complete_option_Some : forall a, is_complete a -> is_complete_option (Some a).

  Hint Constructors is_complete_option : icp.
  Hint Constructors is_complete_option : typeclass_instances.

  #[export]
    Instance CompleteOption : Complete (option A) :=
    {
      is_complete := is_complete_option
    }.

  #[export]
    Instance CompleteMinimalOption `{@CompleteMinimal A HRA HCA} : CompleteMinimal (option A).
  Proof with eauto with icp.
    constructor; unfold_refinement; intros ?; inversion 1; subst; intros ?; inversion 1; subst...
    f_equal; apply is_complete_minimal; eauto.
  Qed.
End OptionICP.

#[export] Hint Constructors refinementOption : icp.
#[export] Hint Constructors refinementOption : typeclass_instances.
#[export] Hint Constructors is_complete_option : icp.
#[export] Hint Constructors is_complete_option : typeclass_instances.
