Require Export Refinement.
Require Import List.
Import ListNotations.

#[unfold_fix]
Symbol not_implemented : forall {A}, A.
Notation "?" := not_implemented.

Create HintDb icp.

Ltac exc_eauto := eauto with icp.

Symbol exc_list_ind : forall (A : Type) (P : list A -> Type) (Hnil : P nil)
  (Hcons : forall (a : A) (l : list A), P l -> P (cons a l))
  (Hnot_impl : P (? (list A)))
    (l : list A), P l.

Rewrite Rules exc_list_indRed :=
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl nil ==> ?Hnil
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl (cons ?a ?l) ==> ?Hcons ?a ?l (exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl ?l)
  | exc_list_ind ?A ?P ?Hnil ?Hcons ?Hnot_impl (? _) ==> ?Hnot_impl.

Rewrite Rules list_red_rew :=
  |  match @not_implemented (list ?A) as t0  return ?P with
     | nil => _
     | _ => _
     end ==> @not_implemented (?P@{t0 := (@not_implemented (list ?A))}).
  (* |  match ? in list ?A  as t0  return ?P with *)
  (*    | nil => _ *)
  (*    | _ => _ *)
  (*    end ==> @not_implemented (?P@{t0 := (@not_implemented (list ?A))}) *)

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
  Context {A : Type} .

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
  Admitted.

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

  #[export]
    Instance groundList : Ground (list A).
  Proof with eauto with icp.
    constructor; intros l; induction l as [|? ? IH |] using exc_list_ind; inversion 1; intros l'; inversion 1; subst...
    f_equal...
  Qed.

End ListICP.

#[export] Hint Constructors refinement_list : icp.
#[export] Hint Constructors refinement_list : typeclass_instances.
#[export] Hint Constructors is_complete_list : icp.
#[export] Hint Constructors is_complete_list : typeclass_instances.



Section ProdICP.
  Context {A B} `{Refinable A} `{Refinable B}.

  (* Not considering exception in prod for refinement for now *)
  #[export]
  Program Instance refinable_prod : Refinable (A * B) := {
      refinement p1 p2 :=
        match p1, p2 with
        | (x1, y1), (x2, y2) => x1 ⊑ x2 /\ y1 ⊑ y2
        end
    }.
  Admit Obligations.

  Lemma fst_ref : forall p p' : A * B,
      p ⊑ p' ->
      fst p ⊑ fst p'.
  Proof.
    intros ? ? Hprec.
    (* CHECKME *)
    destruct p, p'. destruct Hprec.
    simpl. auto.
  Qed.

  Lemma snd_ref : forall p p' : A * B,
      p ⊑ p' ->
      snd p ⊑ snd p'.
  Proof.
    intros ? ? Hprec.
    (* CHECKME *)
    destruct p, p'. destruct Hprec.
    simpl. auto.
  Qed.

  Context `{Complete A} `{Complete B}.

  #[export]
  Program Instance complete_prod : Complete (A * B) := {
      is_complete p :=
        match p with
        | (a, b) => is_complete a /\ is_complete b
        end
    }.
  Admit Obligations.

  Lemma is_complete_fst : forall p : A * B,
      is_complete p ->
      is_complete (fst p).
  Admitted.

  Lemma is_complete_snd : forall p : A * B,
      is_complete p ->
      is_complete (snd p).
  Admitted.


End ProdICP.


Reserved Infix "⊑o" (at level 10).
Inductive refinement_option {A} `{Refinable A} : option A -> option A -> Prop :=
| refinement_none : None ⊑o None
| refinement_some : forall a1 a2, a1 ⊑ a2 -> Some a1 ⊑o (Some a2)
| refinement_nimpl : forall o, o ⊑o ?
where "o1 ⊑o o2" := (refinement_option o1 o2).

#[local]
  Program Instance refinableOption {A} `{Refinable A} : Refinable (option A) := {
    refinement := refinement_option
  }.
Admit Obligations.

(* Local Variables: *)
(* coq-prog-args: ("-emacs" "-native-compiler" "no" "-require" "Coq.Compat.AdmitAxiom" "-require-import" "Coq.Compat.AdmitAxiom" "-w" "unsupported-attributes" "-allow-rewrite-rules") *)
(* End: *)
