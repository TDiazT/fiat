
Require Import Refinement.

Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Strings.Ascii
        Coq.Bool.Bool.

Require Export Coq.Vectors.Vector
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Export Coq.Strings.String.

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


Require Export Fiat.Common.DecideableEnsembles
        Fiat.Common.List.ListFacts
        Fiat.Common.BoolFacts
        Fiat.Common.LogicFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import Coq.Logic.Eqdep_dec
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTRefinement.GeneralBuildADTRefinements.

Require Import Coq.Logic.Eqdep_dec
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation.BuildComputationalADT.
        (* Fiat.ADTRefinement.GeneralBuildADTRefinements. *)

Import Lists.List.ListNotations.


Ltac pick := erewrite refine_pick_val by eauto.
Ltac pick_by H := erewrite refine_pick_val by (eapply H; eauto).

Hint Resolve refine_pick_val.
Hint Rewrite <- app_nil_end.

Require Import Computation.Refinements.Tactics.

Lemma refineR_pick_val A R `{Reflexive A R} a (P : A -> Prop)
  : P a -> @refineR A A R ({x | P x })%comp
            (ret a).
Proof.
    t_refine.
Qed.

Ltac pick_byR H := erewrite refineR_pick_val by (eapply H; eauto).

Definition testnil A B (ls : list A) (cnil ccons : B) : B :=
  match ls with
  | nil => cnil
  | _ :: _ => ccons
  end.

(* There's a bug in the fold_heading code that is causes
   Anomaly "Uncaught exception Not_found."
   at Defined. Overwriting the following folding tactics solves this problem.
*)
(* Ltac fold_heading_hyps_in H ::= idtac. *)
(* Ltac fold_heading_hyps  ::= idtac. *)

Lemma refine_testnil : forall A (ls : list A) B R (c1 cnil ccons : Comp B),
  (ls = nil -> refineR R c1 cnil)
  -> (ls <> nil -> refineR R c1 ccons)
  -> refineR R c1 (testnil ls cnil ccons).
Proof.
  destruct ls; intuition congruence.
Qed.

Add Parametric Morphism A B
: (@testnil A (Comp B))
    with signature
    @eq (list A)
      ==> @refineEq B
      ==> @refineEq B
      ==> @refineEq B
      as refine_testnil_morphism.
Proof.
  destruct y; auto.
Qed.

Lemma refine_testnil_ret : forall A B (ls : list A) (cnil ccons : B),
  refineEq (testnil ls (ret cnil) (ret ccons)) (ret (testnil ls cnil ccons)).
Proof.
  destruct ls; reflexivity.
Qed.

Ltac refine_testnil ls' := etransitivity; [ apply refine_testnil with (ls := ls'); intro | ].

Definition let_ A B (v : A) (f : A -> B) := let x := v in f v.

Add Parametric Morphism A B
: (@let_ A (Comp B))
    with signature
    @eq A
      ==> pointwise_relation _ (@refineEq B)
      ==> @refineEq B
      as refine_let_morphism.
Proof.
  unfold pointwise_relation, let_; auto.
Qed.

Lemma refine_let : forall A B (v : A) c1 (c2 : A -> Comp B),
  (forall x, x = v -> refineEq c1 (c2 x))
  -> refineEq c1 (let_ v c2).
Proof.
  unfold let_; auto.
Qed.

Ltac refine_let x := apply (refine_let (v := x)); intros.

Lemma refine_let_ret : forall A B (v : A) (f : A -> B),
  let_ v (fun x => ret (f x)) =  ret (let_ v f).
Proof.
  reflexivity.
Qed.

Ltac monad_simpl := autosetoid_rewrite with refine_monad;
                   try simplify_with_applied_monad_laws; simpl.

Hint Rewrite refine_let_ret refine_testnil_ret : cleanup.

Global Opaque let_.

Ltac done := try match goal with
                 | [ |- refineEq ?a ?b ] => is_evar b; instantiate (1 := a)
                 | [ |- refineR ?R ?a ?b ] => is_evar b; instantiate (1 := a)
                 end; finish honing.


Require Import Coq.Logic.Eqdep_dec
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation.BuildComputationalADT.
Require Import         Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTNotation.BuildADTReplaceMethods
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.GeneralRefinements.
Require Export Fiat.Common.Coq__8_4__8_5__Compat.



Section ListICP.
  Context {A} `{Refinable A}.

  Inductive refinement_list : list A -> list A -> Prop :=
  | ref_nil_nil : refinement_list nil nil
  | ref_cons_cons : forall a1 a2, a1 ⊑ a2 -> forall l1 l2, refinement_list l1 l2 -> refinement_list (cons a1 l1) (cons a2 l2)
  | ref_list_not_impl : forall l, refinement_list l not_implemented.

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
  Program Instance complete_list : Complete (list A) := {
      is_complete := is_complete_list
    }.
  Admit Obligations.

  Lemma is_complete_app : forall l l' : list A,
      is_complete l ->
      is_complete l' ->
      is_complete (l ++ l').
  Admitted.

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

(* Require Import Tutorial. *)


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

Section data.
  Variable data : Set.

  (* TODO: Change *)
  Instance : Refinable data := mkEqRefinable data.
  Instance : Complete data := mkCompleteTrue data.
  Instance : Ground data := mkGroundTrue data.

  (* Here we parameterize over an arbitrary type of data stored within stacks. *)
  Variable dummy : data.
  (* Sometimes it's useful to have a default value of the data type. *)

  (** Type signature of an implementation of functional queues *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "empty" : rep,
      Method "enqueue" : rep * data -> rep,
      Method "dequeue" : rep -> rep * (option data)
    }.
  (* Notice that "effectful" methods just return new private-state values,
   * in addition to being passed original state values as parameters. *)


  (* Open Scope ADT. *)
  Open Scope ADTParsing.
  Open Scope methDefParsing.

  (** The specification of functional correctness *)
  Definition spec : ADT sig :=
    Def ADT
    {
      rep := (list data),
      (* This first part is the abstract representation type. *)
      Def Constructor0 "empty" : rep :=
        ret nil,,
      Def Method1 "enqueue" (self : rep) (d : data) : rep :=
        ret (self ++ d :: nil),
      Def Method0 "dequeue"(self : rep) : rep * (option data) :=
        match self with
        | nil => ret (self, None)
        | d :: self' => ret (self', Some d)
        end
    }.

  (* We define an abstraction relation, connecting abstract and concrete states.
   * Classic trick: simulate a queue with two stacks,
   * one of which needs to be reversed to reproduce the abstract queue. *)
  Definition absRel (abs : list data) (conc : list data * list data) :=
      abs = fst conc ++ rev (snd conc).


  Instance mono_absRel : forall abs, Monotonizable (absRel abs) .
    unfold absRel.
    intros abs.
    eapply monotonizableEqR.
    unfold_complete; split.
    - unfold_refinement; split; intros l1 l2 Hprec.
      * apply app_ref. apply fst_ref; auto.
        apply rev_ref. apply snd_ref; auto.
      * apply app_ref. apply fst_ref; auto.
        apply rev_ref. apply snd_ref; auto.
    - intros. apply is_complete_app.
      apply is_complete_fst; auto.
      apply is_complete_rev. apply is_complete_snd; auto.
  Defined.

  Definition absRel_mono (abs : list data) (conc : list data * list data) :=
    (monotone (absRel abs)) conc.

  Lemma list_data_refl : forall l : list data,
      l ⊑ l.
  Proof.
    induction l using list_catch; constructor.
    - reflexivity.
    - apply IHl.
  Qed.

  Lemma absRel_implies_mono : forall abs conc,
      absRel abs conc -> absRel_mono abs conc.
  Proof.
    intros abs conc. unfold absRel. intros ->.
    simpl. unfold absRel_mono. simpl.
    apply list_data_refl.
  Qed.

  (* The appropriate initial states are related. *)
  Lemma absRel_initial : absRel nil (nil, nil).
  Proof.
    reflexivity.
  Qed.
  Lemma absRel_nil_not_impl : forall l, absRel_mono l (nil, ?).
  Proof.
    induction l using list_catch; cbn; eauto; constructor.
  Qed.

  (* The simple implementation of "push" preserves the relation. *)
  Lemma absRel_push : forall d abs conc, absRel_mono abs conc
    -> absRel_mono (abs ++ d :: nil) (fst conc, ?).
  Proof.
    unfold absRel_mono; simpl; intros; subst.
    cbn.
    assert (Heq : ? = ? ++ [d]) by reflexivity.
    rewrite Heq.
    rewrite app_assoc.
    apply app_ref.
    - etransitivity. apply H.
      apply app_ref.
      * eapply app_ref_refl_inv_l.
        eapply is_right_reflexive.
        apply H.
      * constructor.
    - constructor.
      * reflexivity.
      * constructor.
  Qed.


  (* When the concrete state is empty, so must be the abstract state. *)
  Lemma absRel_must_be_nil : forall abs conc,
    absRel_mono abs conc
    -> fst conc = nil
    -> snd conc = nil
    -> abs = nil.
  Proof.
    unfold absRel_mono; destruct conc; simpl; intros; subst.
    simpl in H. inversion H. auto.
    admit.
  Admitted.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty first list.
   * In general, such a property depends on a list being nonempty. *)
  Lemma eta_abs_fst : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intuition.
    destruct (fst conc); simpl in *; intuition congruence.
  Qed.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty second list. *)
  Lemma eta_abs_snd : forall abs conc,
    absRel abs conc
    -> snd conc = hd dummy (snd conc) :: tl (snd conc)
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intros.
    destruct (snd conc); simpl in *; intuition.
    (* apply (f_equal (@length _)) in H. *)
    (* repeat rewrite app_length in H; simpl in H. *)
    (* omega. *)
    (* auto. *)
  (* Qed. *)
  Admitted.

  (* The case for preserving the relation on "pop",
   * when we need to reverse the second list. *)
  Lemma absRel_reversed_rep : forall abs conc r,
    absRel abs conc
    -> fst conc = nil
    -> snd conc <> nil
    -> r = rev (snd conc)
    -> absRel (tl abs) (tl r, nil).
  Proof.
    unfold absRel; intuition simpl in *; subst.
  (*   autorewrite with core; auto. *)
  (* Qed. *)
  Admitted.

  (* The case for returning the right data value on "pop",
   * when we need to reverse the second list. *)
  Lemma absRel_reversed_data : forall abs conc r,
    absRel abs conc
    -> fst conc = nil
    -> snd conc <> nil
    -> r = rev (snd conc)
    -> hd dummy abs = hd dummy r.
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
  Qed.

  (* The case for preserving the relation on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma absRel_fast_rep : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> absRel (tl abs) (tl (fst conc), snd conc).
  Proof.
    unfold absRel; intuition simpl in *; subst.
    destruct (fst conc); simpl in *; tauto.
  Qed.

  (* The case for returning the right data value on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma absRel_fast_data : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> hd dummy abs = hd dummy (fst conc).
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
    destruct (fst conc); simpl in *; tauto.
  Qed.


Require Import BuildADTRefinements.HoneRepresentation.
Definition RSig : forall (idx : MethodIndex sig), Core.RCod (snd (MethodDomCod sig idx) ) .
  repeat refine (fun idx => proj1_sig (cons_RCods _ _ idx)).
  - simpl. exact tt.
  - simpl.
    exact refinableOption.(refinement).
  -  eapply empty_RCods.
Defined.


Ltac refineConstr :=
  repeat (first [eapply refine_Constructors_nil
                    | eapply refine_Constructors_cons;
                      [ intros; simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E) => is_evar E; let H := fresh in fast_set (H := E)
                        | _ => idtac
                        end | ] ]).
(* Tactic Notation "hone" "representation" "using" open_constr(AbsR') := *)
(*   eapply SharpenStep; *)
(*   [eapply refineADT_BuildADT_Rep_refine_All with (AbsR := AbsR'); *)
(*     [ repeat (first [eapply refine_Constructors_nil *)
(*                     | eapply refine_Constructors_cons; *)
(*                       [ intros; simpl; intros; *)
(*                         match goal with *)
(*                         |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         | _ => idtac *)
(*                         end | ] ]) *)
(*     | repeat (first [eapply refine_Methods_nil *)
(*                     | eapply refine_Methods_cons; *)
(*                       [ intros; simpl; intros; *)
(*                         match goal with *)
(*                         |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                         |  |- refine _ (?E _) => is_evar E; let H := fresh in fast_set (H := E) *)
(*                           | _ => idtac *)
(*                         end | ] *)
(*                     ])] *)
(*   | ]. *)

Tactic Notation "hone" "representation" "using" open_constr(AbsR') :=
  eapply SharpenStep;
  [idtac|eapply refineADT_BuildADT_Rep_refine_All with (AbsR := AbsR');
    [ repeat (first [eapply refine_Constructors_nil
                    | eapply refine_Constructors_cons;
                      [ intros; simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E) => is_evar E; let H := fresh in fast_set (H := E)
                        | _ => idtac
                        end | ] ])
    | repeat (first [eapply refine_Methods_nil
                    | eapply refine_Methods_cons;
                      [ intros; simpl; unfold refineMethod, refineMethod'; intros;
                        match goal with
                        |  |- refine _ _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ _ (?E _) => is_evar E; let H := fresh in fast_set (H := E)
                          | _ => idtac
                        end | ]
                    ])]
  | ].


Instance option_Reflexive {A} `{Reflexive A} `{Refinable A} : Reflexive (refinableOption.(@refinement (option A))). Admitted.
  (* Instance rprodreflexive {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop) `{Reflexive R1} `{Reflexive R2} : Reflexive (R1 ) *)

Instance refineProd_Reflexive A B (R : A -> A -> Prop) `{Reflexive A R} : Reflexive (@refineProd A A B R ).
Admitted.

Instance refineProd_Transitive A B (R : A -> A -> Prop) `{Transitive A R} : Transitive (@refineProd A A B R ).
Admitted.

Instance refineR_Transitive A (R : A -> A -> Prop) `{Transitive A R} : Transitive (refineR R ).
(* t. *)
(* Qed. *)
Admitted.

  Axiom (nil_neq_app_cons : forall {A} l (d : A), [] <> l ++ [d]).
  Axiom (nil_neq_app_not_empty : forall {A} (l l' : list A), l <> nil -> [] <> l ++ l').

  Ltac refineEqOldSimpl := eapply refineEquiv_refine_proper; monad_simpl.

  Ltac cleanup := autorewrite with cleanup.
  (* Ltac finalize := finish_SharpeningADT_WithoutDelegation. *)

(* Ltac finish_SharpeningADT_WithoutDelegation := *)
(*   eapply FullySharpened_Finish; *)
(*   [ FullySharpenEachMethod *)
(*       (@Vector.nil ADTSig) *)
(*       (@Vector.nil Type) *)
(*       (ilist.inil (B := fun nadt => ADT (delegateeSig nadt))); *)
(*     try simplify with monad laws; simpl; try refine pick eq; try simplify with monad laws; *)
(*     try first [ simpl]; *)
(*     (* Guard setoid rewriting with [refine_if_If] to only occur when there's *) *)
(* (*     actually an [if] statement in the goal.  This prevents [setoid_rewrite] from *) *)
(* (*     uselessly descending into folded definitions. *) *)
(*     repeat lazymatch goal with *)
(*              | [ |- context [ if _ then _ else _ ] ] => *)
(*                setoid_rewrite refine_if_If at 1 *)
(*            end; *)
(*     repeat first [ *)
(*              higher_order_reflexivity *)
(*            | simplify with monad laws *)
(*            | Implement_If_Then_Else *)
(*            | Implement_If_Opt_Then_Else ] *)
(*   | extract_delegate_free_impl *)
(*   | simpl; higher_order_reflexivityT ]. *)

  (* Now we start deriving an implementation, in a correct-by-construction way. *)

  Theorem implementation : FullySharpened RSig spec .
  Proof.
    start sharpening ADT.

    hone representation using absRel_mono.

    admit.

    - monad_simpl.

      pick_by (absRel_implies_mono absRel_initial).
      done.

    (* Enqueue *)
    -
      monad_simpl.
      pick_by absRel_push.
      done.

    (* Dequeue *)
    - refine_testnil (fst r_n).
      + refine_testnil (snd r_n).
        * assert (r_o = nil) by (eapply absRel_must_be_nil; eauto).
          subst.
          refineEqOldSimpl; [reflexivity|].
          refineEqOldSimpl.
          pick_by (absRel_implies_mono absRel_initial).
          done.
          refineEqOldSimpl.
          done.
          done.
        * pose (Habs := H0). clearbody Habs.
          cbn in H0. rewrite H1 in H0. cbn in H0.
          inversion H0; subst.
          ** refineEqOldSimpl. pick_by absRel_nil_not_impl. monad_simpl. done.
             instantiate (1 := (ret ([], ?, ?))).
             unfold refineR. intros. destruct H3.
             exists ([], ?, None). repeat split; eauto.
             cbn. constructor.
          ** refineEqOldSimpl. pick_by absRel_nil_not_impl.
             monad_simpl. done.
             unfold refineR. intros. destruct H5.
             exists ([], ?, Some a1). cbn. repeat split; eauto. constructor.
          ** rewrite <- H5 in H0.
             admit.
        * done.
      + inversion H0.
        * apply nil_neq_app_not_empty in H4; eauto. contradiction.
        * refineEqOldSimpl. pick_by absRel_nil_not_impl. monad_simpl. done.
          instantiate (1 := (ret ([], ?, ?))).
          unfold refineR. intros. destruct H6.
          exists ([], ?, Some a1). cbn. repeat split; eauto. constructor.
        * unfold absRel in H0; cbn in H0. rewrite <- H4 in H0.
          admit.
      + done.

    - eapply FullySharpened_Finish.
      admit.

      finalize.
  Defined.

  (* We can now extract a standlone Gallina term for this ADT. *)
  Definition impl := Eval simpl in projT1 implementation.
  Print impl.

  (* Let's try that again, with more automation. *)
  Hint Resolve absRel_initial absRel_push absRel_must_be_nil absRel_reversed_rep absRel_fast_rep.

  Theorem more_automated_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using absRel.

    monad_simpl.
    pick.
    done.

    monad_simpl.
    pick.
    done.

    refine_testnil (fst r_n).

    refine_testnil (snd r_n).

    assert (r_o = nil) by eauto.
    subst.
    monad_simpl.
    pick.
    monad_simpl.
    done.

    refine_let (rev (snd r_n)).

    erewrite eta_abs_snd with (abs := r_o) by eauto.
    monad_simpl.
    pick.
    monad_simpl.
    erewrite absRel_reversed_data by eauto.
    done.

    cbv beta.
    done.

    erewrite eta_abs_fst with (abs := r_o) by eauto.
    monad_simpl.
    pick.
    monad_simpl.
    erewrite absRel_fast_data with (abs := r_o) by eauto.
    done.

    cleanup.
    done.

    finalize.
  Defined.

  (* We can go further, building tactics to automate most of our strategy. *)

  Ltac queue' :=
    repeat match goal with
           | _ => progress monad_simpl
           | _ => pick
           | [ H : absRel ?abs _ |- _ ] =>
             match abs with
             | nil => fail 1
             | _ => assert (abs = nil) by eauto; subst
             end
           | [ _ : absRel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] =>
             (erewrite eta_abs_fst with (abs := abs_) by eauto)
             || (erewrite eta_abs_snd with (abs := abs_) by eauto)
           | [ |- context[hd dummy _] ] =>
             (erewrite absRel_reversed_data by eauto)
             || (erewrite absRel_fast_data by eauto)
           end.

  Ltac queue := queue'; done.

  Theorem even_more_automated_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using absRel; try queue.

    refine_testnil (fst r_n); [
      refine_testnil (snd r_n); [ queue |
        refine_let (rev (snd r_n)); queue | queue ] | queue | ].

    cleanup; done.

    finalize.
  Defined.


  (* OK, we just spent all that effort on automating the derivation.
   * Ideally the same automation will keep working with different implementations.
   * Let's try another (dumb, slow) one. *)
  Definition dumbAbsRel (abs conc : list data) := conc = rev abs.

  Fixpoint getLast (ls : list data) : (list data * data) :=
    match ls with
    | nil => (nil, dummy)
    | d :: nil => (nil, d)
    | d :: ls' =>
      let p := getLast ls' in
      (d :: fst p, snd p)
    end.

  Lemma dumbAbsRel_initial : dumbAbsRel nil nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dumbAbsRel_push : forall abs conc d,
    dumbAbsRel abs conc
    -> dumbAbsRel (abs ++ d :: nil) (d :: conc).
  Proof.
    unfold dumbAbsRel; simpl; intros.
    rewrite rev_unit.
    congruence.
  Qed.

  Lemma dumbAbsRel_must_be_nil : forall abs conc,
    dumbAbsRel abs conc
    -> conc = nil
    -> abs = nil.
  Proof.
    unfold dumbAbsRel; simpl; intros.
    subst.
    destruct abs; simpl in *; intuition.
    exfalso; eauto.
  Qed.

  Lemma dumbAbsRel_eta : forall abs conc,
    dumbAbsRel abs conc
    -> conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold dumbAbsRel; simpl; intros.
    subst.
    destruct abs; intuition.
  Qed.

  Lemma getLast_append_list : forall ls d,
    fst (getLast (ls ++ d :: nil)) = ls.
  Proof.
    induction ls; simpl; intuition.
    destruct (ls ++ d :: nil) eqn:Heq.
    exfalso; eauto.
    rewrite <- Heq.
    rewrite IHls.
    auto.
  Qed.

  Lemma dumbAbsRel_pop_rep : forall abs conc r,
    dumbAbsRel abs conc
    -> conc <> nil
    -> r = getLast conc
    -> dumbAbsRel (tl abs) (fst r).
  Proof.
    unfold dumbAbsRel; intros; subst.
    destruct abs; simpl in *; intuition.
    apply getLast_append_list.
  Qed.

  Lemma getLast_append_data : forall ls d,
    snd (getLast (ls ++ d :: nil)) = d.
  Proof.
    induction ls; auto.

    intros.
    simpl app.
    unfold getLast.
    fold getLast.
    destruct (ls ++ d :: nil) eqn:Heq.
    exfalso; eauto.
    rewrite <- Heq.
    rewrite IHls.
    auto.
  Qed.

  Lemma dumbAbsRel_pop_data : forall abs conc r,
    dumbAbsRel abs conc
    -> conc <> nil
    -> r = getLast conc
    -> hd dummy abs = snd r.
  Proof.
    unfold dumbAbsRel; intros; subst.
    destruct abs; simpl in *; intuition.
    rewrite getLast_append_data; auto.
  Qed.

  Hint Resolve dumbAbsRel_initial dumbAbsRel_push dumbAbsRel_must_be_nil dumbAbsRel_pop_rep.

  (* Here's our first derivation, showing a bit more manual perspective. *)
  Theorem dumb_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using dumbAbsRel; try queue.

    refine_testnil r_n.

    assert (r_o = nil) by eauto.
    subst.
    queue.

    refine_let (getLast r_n).
    erewrite dumbAbsRel_eta with (abs := r_o) by eauto.
    erewrite dumbAbsRel_pop_data by eauto.
    queue.

    cleanup.
    done.

    finalize.
  Defined.

  (* We use a double colon to override the prior definition. *)
  Ltac queue' ::=
    repeat match goal with
           | _ => progress monad_simpl
           | _ => pick
           | [ H : dumbAbsRel ?abs _ |- _ ] =>
             match abs with
             | nil => fail 1
             | _ => assert (abs = nil) by eauto; subst
             end
           | [ _ : dumbAbsRel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] =>
             erewrite dumbAbsRel_eta with (abs := abs_) by eauto
           | [ |- context[hd dummy _] ] =>
             erewrite dumbAbsRel_pop_data by eauto
           end.

  (* Now let's automate it more. *)
  Theorem more_automated_dumb_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using dumbAbsRel; try queue.

    refine_testnil r_n; [ queue |
      refine_let (getLast r_n); queue | ].

    queue'.
    cleanup.
    done.

    finalize.
  Defined.
End data.

(* Local Variables: *)
(* coq-prog-args: ("-emacs" "-native-compiler" "no" "-require" "Coq.Compat.AdmitAxiom" "-require-import" "Coq.Compat.AdmitAxiom" "-w" "unsupported-attributes" "-allow-rewrite-rules") *)
(* End: *)
