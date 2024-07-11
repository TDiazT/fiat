Require Import Fiat.Examples.Tutorial.RefinementInstances.

Require Import
  Coq.Strings.Ascii
  Coq.Bool.Bool
  Coq.Vectors.Vector
  Coq.Bool.Bvector
  Coq.Lists.List
  Coq.Strings.String
  Coq.Logic.Eqdep_dec.

Import Lists.List.ListNotations.

Require Export
  Fiat.Common.DecideableEnsembles
  Fiat.Common.List.ListFacts
  Fiat.Common.BoolFacts
  Fiat.Common.LogicFacts
  Fiat.Common.List.FlattenList
  Fiat.Common.Ensembles.IndexedEnsembles
  Fiat.Common.IterateBoundedIndex
  Fiat.Common.Tactics.CacheStringConstant
  Fiat.Common.BoundedLookup
  Fiat.Common.ilist.
Require Import
  Fiat.ADT.ComputationalADT
  Fiat.ADT.ADTSig
  Fiat.ADT.Core.
Require Import
  Fiat.ADTNotation.BuildComputationalADT
  Fiat.ADTNotation.BuildADTSig
  Fiat.ADTNotation.BuildADT
  Fiat.ADTNotation.BuildADTReplaceMethods.
Require Import
  Fiat.ADTRefinement.GeneralBuildADTRefinements
  Fiat.ADTRefinement.Core
  Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import Fiat.Computation.Refinements.Tactics.

(***************************************************************)
(* Originally defined in Tutorial.v                            *)
(***************************************************************)
(* Moved from there because it imports and defines too many things that
   are not necessary for this case study *)

Ltac pick := erewrite refine_pick_val by eauto.
Ltac pick_by H := erewrite refine_pick_val by (eapply H; eauto).

Hint Resolve refine_pick_val.
Hint Rewrite <- app_nil_end.

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


Lemma refine_testnil : forall A `{Complete A} (ls : list A) B R (c1 cnil ccons : Comp B),
    is_complete ls ->
    (ls = nil -> refineR R c1 cnil)
    -> (ls <> nil -> refineR R c1 ccons)
    -> refineR R c1 (testnil ls cnil ccons).
Proof with eauto with icp.
  intros ? ? ls.
  induction ls using exc_list_ind; try intuition congruence.
  intros ? ? ? ? ? Hcontra.
  inversion Hcontra...
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

Ltac refine_testnil ls' := etransitivity; [ eapply refine_testnil with (ls := ls'); eauto; intro | ].

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

(***************************************************************)
(* End of Tutorial.v                                           *)
(***************************************************************)

Section data.
  Variable data : Set.
  Hypothesis (Hdata_not_impl : forall d : data, d ⊑ ? data).

  (* Here we parameterize over an arbitrary type of data stored within stacks. *)
  Variable dummy : data.
  (* Sometimes it's useful to have a default value of the data type. *)

  (** Type signature of an implementation of functional queues *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "empty" : rep,
      Method "enqueue" : rep * data -> rep,
      Method "dequeue" : rep -> rep * ↑(option data)
    }.
  (* Notice that "effectful" methods just return new private-state values,
   * in addition to being passed original state values as parameters. *)

  Open Scope ADTParsing.
  Open Scope methDefParsing.

  (** The specification of functional correctness *)
  Definition naive_implementation : ADT sig :=
    Def ADT
    {
      rep := (list data),
      (* This first part is the abstract representation type. *)
      Def Constructor0 "empty" : rep :=
        ret nil,,
      Def Method1 "enqueue" (self : rep) (d : data) : rep :=
        ret (self ++ d :: nil),
      Def Method0 "dequeue"(self : rep) : rep * ↑(option data) :=
        match self with
        | nil => ret (self, None)
        | d :: self' => ret (self', Some d)
        end
    }.

  (* We define an abstraction relation, connecting abstract and concrete states.
   * Classic trick: simulate a queue with two stacks,
   * one of which needs to be reversed to reproduce the abstract queue. *)
  Definition rel (naive : list data) (opt : list data * list data) :=
      naive = fst opt ++ rev (snd opt).

  Definition rel_mono (naive : list data) (opt : list data * list data) :=
    (ir_mono (rel naive)) opt.

  Definition rel_anti (naive : list data) (opt : list data * list data) :=
    (ir_anti (rel naive)) opt.

  Lemma list_data_refl : forall l : list data,
      l ⊑ l.
  Proof.
    induction l using exc_list_ind; constructor; eauto.
    reflexivity.
  Qed.

  Lemma rel_implies_mono : forall naive opt,
      rel naive opt -> rel_mono naive opt.
  Proof.
    intros naive opt. unfold rel. intros ->.
    simpl. unfold rel_mono. simpl.
    apply list_data_refl.
  Qed.

  (* The appropriate initial states are related. *)
  Lemma rel_initial : rel nil (nil, nil).
  Proof.
    reflexivity.
  Qed.

  Lemma rel_nil_not_impl : forall l, rel_mono l (nil, ? (list data)).
  Proof.
    induction l using exc_list_ind; cbn; constructor.
  Qed.

  Definition rel_enqueue (naive : list data) (opt : list data * list data) :=
    forall d, rel naive opt ->
         rel (naive ++ d :: nil) (fst opt, ? (list data)).

  (* The simple implementation of "push" preserves the relation. *)
  Lemma ir_rel_enqueue : forall d naive opt, rel_anti naive opt
    -> rel_mono (naive ++ d :: nil) (fst opt, ? (list data)).
  Proof.
    unfold rel_mono; simpl; intros; subst.
    unfold rel_anti in H.
    simpl in H.
    destruct H as [_ Heq]. rewrite <- Heq.
    cbn in *.
    rewrite <- app_assoc.
    apply app_ref.
    - reflexivity.
    - constructor.
  Qed.


  (* When the concrete state is empty, so must be the abstract state. *)
  Lemma rel_must_be_nil : forall naive opt,
    rel_anti naive opt
    -> fst opt = nil
    -> snd opt = nil
    -> naive = nil.
  Proof.
    unfold rel_anti; destruct opt; simpl; intros; subst.
    simpl in H. inversion H. auto.
  Qed.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty first list.
   * In general, such a property depends on a list being nonempty. *)
  Lemma eta_naive_fst : forall naive opt,
    rel_anti naive opt
    -> fst opt <> nil
    -> naive = hd dummy naive :: tl naive.
  Proof.
    unfold rel_anti; destruct naive; simpl; intuition.
    destruct (fst opt); simpl in *; intuition congruence.
  Qed.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty second list. *)
  Lemma eta_naive_snd : forall naive opt,
    rel_anti naive opt
    -> snd opt = hd dummy (snd opt) :: tl (snd opt)
    -> naive = hd dummy naive :: tl naive.
  Proof.
    unfold rel_anti; destruct naive; simpl; intros.
    destruct (snd opt); simpl in *; intuition.
    apply (f_equal (@List.length _)) in H2.
    repeat rewrite app_length in H2; simpl in H2.
    omega.
    auto.
  Qed.

  (* The case for preserving the relation on "pop",
   * when we need to reverse the second list. *)
  Lemma rel_reversed_rep : forall naive opt r,
    rel_anti naive opt
    -> fst opt = nil
    -> snd opt <> nil
    -> r = rev (snd opt)
    -> rel_mono (tl naive) (tl r, nil).
  Proof.
    unfold rel_anti, rel_mono; intuition simpl in *; subst.
    autorewrite with core; auto.
    destruct H as [_ <-]; simpl.
    apply list_data_refl.
  Qed.

  (* The case for returning the right data value on "pop",
   * when we need to reverse the second list. *)
  Lemma rel_reversed_data : forall naive opt r,
    rel_anti naive opt
    -> fst opt = nil
    -> snd opt <> nil
    -> r = rev (snd opt)
    -> hd dummy naive = hd dummy r.
  Proof.
    unfold rel_anti; intuition simpl in *; destruct H; simpl in *; subst; auto.
  Qed.

  (* The case for preserving the relation on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma rel_fast_rep : forall naive opt,
    rel_anti naive opt
    -> fst opt <> nil
    -> rel_mono (tl naive) (tl (fst opt), snd opt).
  Proof.
    unfold rel_anti, rel_mono; intuition simpl in *.
    destruct H; subst.
    destruct (fst opt); simpl in *. tauto.
    apply list_data_refl.
  Qed.

  (* The case for returning the right data value on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma rel_fast_data : forall naive opt,
    rel_anti naive opt
    -> fst opt <> nil
    -> hd dummy naive = hd dummy (fst opt).
  Proof.
    unfold rel_anti; intuition simpl in *.
    destruct H. subst; auto.
    induction (fst opt) using exc_list_ind; simpl in *; tauto.
  Qed.


Instance refineProd_Reflexive A B RCods `{forall A, Reflexive (RCods A)} : Reflexive (@refineProd RCods A B).
Proof.
  unfold refineProd, refineR.
  econstructor. repeat split; eauto.
  reflexivity.
Qed.

Instance refineProd_Transitive A B RCods `{forall A, Transitive (RCods A)} : Transitive (@refineProd RCods A B).
Proof.
  intros x y z.
  unfold refineProd, refineR.
  intros Hxy Hyz v'' Hzv''.
  destruct (Hyz _ Hzv'') as [v' [Hyv' [Heq' HRv']]].
  destruct (Hxy _ Hyv') as [v [Hxv [Heq HRv]]].
  exists v. repeat split; eauto. rewrite Heq; eauto.
  eapply H; eauto.
Qed.

(* Relation to be used for the outputs of each method *)
Definition SigRCods (A : refinableType) := (ARef A).(refinement).

  (* This could be proven in Refinement directly *)
  Instance sigRCodsPreOrder A : PreOrder (SigRCods A).
  econstructor; typeclasses eauto.
  Qed.

  Instance sigRCodsReflexive A : Reflexive (SigRCods A).
   typeclasses eauto.
  Qed.

  Instance sigRCodsTransitive A : Transitive (SigRCods A).
   typeclasses eauto.
  Qed.

  Instance refineProd_SigRCods_Reflexive {A} `{Refinable A} {B} : Reflexive (@refineProd SigRCods (↑A) B).
  typeclasses eauto.
  Qed.

  Ltac refineEqOldSimpl := eapply refineEquiv_refine_proper; monad_simpl.

  Lemma refineEquiv_refineProd_proper {X} {A : refinableType} RCods (c c' c'' : Comp (X * A))
    : refineEq c' c ->
      refineProd RCods  c c'' ->
      refineProd RCods  c' c''.
  Proof.
    intros H1.
    unfold refineProd.
    refineEqOldSimpl; eauto.
  Qed.

  Ltac refineEqProdSimpl := eapply refineEquiv_refineProd_proper; monad_simpl.

  Ltac cleanup := autorewrite with cleanup.
  (* Ltac finalize := finish_SharpeningADT_WithoutDelegation. *)


  Lemma complete_list_cons :
    forall l,
      is_complete l ->
      l <> [] ->
      l = hd dummy l :: tl l.
  Proof.
    inversion 1; eauto; contradiction.
  Qed.

  Hint Resolve complete_list_cons.



  Ltac finalize := finish_SharpeningADT_WithoutDelegation.
  (* Now we start deriving an implementation, in a correct-by-construction way. *)

Tactic Notation "hone" "representation" "using" open_constr(AbsR_mono') "and" open_constr(AbsR_anti') :=
  eapply SharpenStep;
  [
    typeclasses eauto
  | typeclasses eauto
  | eapply refineADT_BuildADT_Rep_refine_All with (AbsR_mono := AbsR_mono') (AbsR_anti := AbsR_anti');
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

  Theorem implementation : FullySharpened SigRCods naive_implementation .
  Proof.
    start sharpening ADT.

    hone representation using rel_mono and rel_anti.

    - monad_simpl.

      pick_by (rel_implies_mono rel_initial).
      done.

    (* Enqueue *)
    -
      monad_simpl.
      pick_by ir_rel_enqueue.
      done.

    (* Dequeue *)
    - pose (Hrel := H0); clearbody Hrel.
      destruct H0 as [Hc Heq].
      apply is_complete_app_inv in Hc. destruct Hc.

      refine_testnil (fst r_n).
      + apply is_complete_rev_inv in H1.
        refine_testnil (snd r_n).
        * assert (Hr_o_nil : r_o = nil) by (eapply rel_must_be_nil; eauto).
          rewrite Hr_o_nil.
          refineEqOldSimpl; [reflexivity|].
          refineEqOldSimpl.
          pick_by (rel_implies_mono rel_initial).
          done.
          refineEqOldSimpl.
          done.
          done.
        *
          refineEqOldSimpl.
          refine_let (rev (snd r_n)).
          erewrite eta_naive_snd with (naive := r_o) by eauto.
          monad_simpl.
          pick_by rel_reversed_rep.
          monad_simpl.
          erewrite rel_reversed_data by eauto.
          done.
          done.

        * cbv beta.
          done.


      +
        erewrite eta_naive_fst with (naive := r_o) by eauto.
        monad_simpl.
        refineEqOldSimpl.
        pick_by rel_fast_rep.
        monad_simpl.
        erewrite rel_fast_data with (naive := r_o) by eauto.
        done.
        done.
      + refineEqOldSimpl.
        cleanup.
        done.
        done.

      (**********)
      (* Copying tactic directly *)
      (**********)

        Ltac extract_delegate_free_impl :=
          cbv beta; simpl;
          match goal with
            |- forall (idx : Fin.t 0),
              refineADT SigRCods
                (ith inil idx)
                (ComputationalADT.LiftcADT
                   (existT
                      (ComputationalADT.pcADT
                         (delegateeSig _))
                      (?DelegateReps idx) (?DelegateSpecs idx))) =>
              unify DelegateReps (fun idx : Fin.t 0 => False);
              let P' := match type of DelegateSpecs with
                        | forall idx, @?P' idx => P'
                        end in
              unify DelegateSpecs (fun idx : Fin.t 0 => Fin.case0 P' idx);
              apply Fin.case0
          end.

Ltac FullySharpenEachMethod DelegateSigs DelegateReps delegateSpecs :=
    let Delegatees := constr:(Build_NamedDelegatees DelegateSigs DelegateReps) in
    let DelegateSpecs := constr:(ith delegateSpecs) in
    let NumDelegates := match type of DelegateSigs with
                        | Vector.t _ ?n => n
                        end in
    match goal with
      |- FullySharpenedUnderDelegates ?RCods (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
        (* idtac "ok" end. *)
      ilist_of_evar_dep n
        (Fin.t NumDelegates -> Type)
        (fun D =>
           forall idx,
             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (D idx))
        (fun Sig => ComputationalADT.cConstructorType Rep (consDom Sig))
        consSigs
        ltac:(fun cCons =>
                ilist_of_evar_dep n'
                                  (Fin.t NumDelegates -> Type)
                                  (fun D =>
                                     forall idx,
             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (D idx))
        (fun Sig => ComputationalADT.cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                eapply (@Notation_Friendly_SharpenFully
                          Rep NumDelegates n n'
                          RCods
                          consSigs methSigs
                          consDefs methDefs
                          DelegateSigs DelegateReps
                          (fun _ => Rep)
                          cCons cMeths
                          delegateSpecs
                          (fun
                              (DelegateReps'' : Fin.t NumDelegates -> Type)
                              (DelegateImpls'' : forall idx,
                                  ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (DelegateReps'' idx))
                         (ValidImpls''
                          : forall idx : Fin.t NumDelegates,
                             refineADT RCods (DelegateSpecs idx)
                                       (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls'' idx))))
                            => @eq _)
                          (* TODO: Delete this probably *)
                          (fun
                              (DelegateReps'' : Fin.t NumDelegates -> Type)
                              (DelegateImpls'' : forall idx,
                                  ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (DelegateReps'' idx))
                         (ValidImpls''
                          : forall idx : Fin.t NumDelegates,
                             refineADT RCods (DelegateSpecs idx)
                                       (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls'' idx))))
                            => @eq _)
             )))
    end; try (simpl; repeat split; intros; subst).
    - eapply FullySharpened_Finish;
      [ typeclasses eauto
      | typeclasses eauto
      | FullySharpenEachMethod
          (@Vector.nil ADTSig)
          (@Vector.nil Type)
          (ilist.inil (B := fun nadt => ADT (delegateeSig nadt)));
        try simplify with monad laws; simpl; try refine pick eq; try simplify with monad laws;
          try first [ simpl]
          ; repeat first [
              higher_order_reflexivity
              ]

        | extract_delegate_free_impl
        (* | idtac *)
        | simpl; higher_order_reflexivityT ].

      + unfold refineMethod. intros ? ? []. unfold refineMethod'. intros.
      monad_simpl.
      unfold LiftcMethod, LiftcMethod'.
      pick.
      higher_order_reflexivity.

      + unfold refineMethod. intros ? ? []. unfold refineMethod'.
        refineEqProdSimpl. pick. monad_simpl. done.
        higher_order_reflexivity.

  Defined.

  (* We can now extract a standlone Gallina term for this ADT. *)
  Definition impl := Eval simpl in projT1 implementation.
  Print impl.

  (* Let's try that again, with more automation. *)
  Hint Resolve rel_initial rel_push rel_must_be_nil rel_reversed_rep rel_fast_rep.

  Theorem more_automated_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using rel.

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
    erewrite rel_reversed_data by eauto.
    done.

    cbv beta.
    done.

    erewrite eta_abs_fst with (abs := r_o) by eauto.
    monad_simpl.
    pick.
    monad_simpl.
    erewrite rel_fast_data with (abs := r_o) by eauto.
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
           | [ H : rel ?abs _ |- _ ] =>
             match abs with
             | nil => fail 1
             | _ => assert (abs = nil) by eauto; subst
             end
           | [ _ : rel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] =>
             (erewrite eta_abs_fst with (abs := abs_) by eauto)
             || (erewrite eta_abs_snd with (abs := abs_) by eauto)
           | [ |- context[hd dummy _] ] =>
             (erewrite rel_reversed_data by eauto)
             || (erewrite rel_fast_data by eauto)
           end.

  Ltac queue := queue'; done.

  Theorem even_more_automated_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using rel; try queue.

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
