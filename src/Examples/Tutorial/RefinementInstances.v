Require Export Refinement.
Require Import List.
Import ListNotations.

#[unfold_fix]
Symbol not_implemented : forall {A}, A.
(* Symbol not_implemented : forall {A}, list A. *)
Notation "?" := not_implemented.

Symbol list_catch :
  forall {A} (P : list A -> Prop)
              (Pnil : P nil)
              (Pcons : forall (a : A) (l : list A), P l -> P (cons a l))
              (Pnot_impl : P not_implemented),
    forall l, P l.

Symbol list_catch_ty :
  forall {A} (P : list A -> Type)
              (Pnil : P nil)
              (Pcons : forall (a : A) (l : list A), P l -> P (cons a l))
              (Pnot_impl : P not_implemented),
    forall l, P l.

(* Notation clash with imports *)
Rewrite Rules list_catch_red :=
  | list_catch _ ?Pnil _ _ nil ==> ?Pnil.

Rewrite Rules list_red_rew :=
|  match @not_implemented (list ?A) as t0  return ?P with
  | nil => _
  | _ => _
  end ==> @not_implemented (?P@{t0 := (@not_implemented (list ?A))}).

Section ListICP.
  Context {A} `{Refinable A}.

  Reserved Infix "⊑l" (at level 10).
  Inductive refinement_list : list A -> list A -> Prop :=
  | ref_nil_nil : nil ⊑l nil
  | ref_cons_cons : forall a1 a2, a1 ⊑ a2 -> forall l1 l2,  l1  ⊑l l2 ->  (cons a1 l1) ⊑l (cons a2 l2)
  | ref_list_not_impl : forall l, l ⊑l not_implemented
  where "l1 ⊑l l2" := (refinement_list l1 l2).

  #[export]
  Program Instance refinable_list : Refinable (list A) := {
      refinement := refinement_list
    }.
  Admit Obligations.

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
    -  cbn. constructor.
  Qed.

  Lemma app_ref_refl_inv_l : forall (l l' : list A),
      l ++ l' ⊑ l ++ l' ->
      l ⊑ l.
  Proof.
    intros l; induction l as [| hd tl IH|] using list_catch; intros l'.
    - constructor.
    - simpl. inversion 1; subst.
      * constructor; auto. eapply IH; eauto.
      * admit. (* false premise *)
    - constructor.
  Admitted.

  Lemma rev_ref : forall l l' : list A,
      l ⊑ l' ->
      rev l ⊑ rev l'.
  Admitted.

  Context `{Complete A}.

  Inductive is_complete_list : list A -> Prop :=
  | is_complete_nil : is_complete_list nil
  | is_complete_cons : forall a, is_complete a -> forall l, is_complete_list l -> is_complete_list (cons a l).

  #[export]
    Instance complete_list : Complete (list A) := {
      is_complete := is_complete_list
    }.

  Lemma is_complete_app : forall l l' : list A,
      is_complete l ->
      is_complete l' ->
      is_complete (l ++ l').
  Proof.
    induction l using list_catch; eauto; intros l'.
    inversion 1; subst; eauto. intros ?.
    simpl; constructor; eauto. apply IHl; eauto.
  Qed.

  Lemma is_complete_rev : forall l : list A,
      is_complete l ->
      is_complete (rev l).
  Admitted.

  #[export]
    Program Instance : Ground (list A).
  Admit Obligations.

End ListICP.

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
