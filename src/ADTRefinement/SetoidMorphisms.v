Require Import Fiat.Common Fiat.Computation Coq.Sets.Ensembles.
Require Import Fiat.ADT.ADTSig Fiat.ADT.Core Fiat.ADTRefinement.Core.

(** Definitions for integrating [refineADT] into the setoid rewriting
    framework. *)

#[global]
Instance refineConstructor_refl rep Dom
: Reflexive (@refineConstructor rep rep eq Dom).
Proof.
  induction Dom; simpl.
  - intro; simpl; unfold refineEq; intros; subst; computes_to_econstructor; eauto.
  - intro; simpl; intros; subst; apply IHDom.
Qed.

Definition RCodReflexive (cod : option Type) (R : RCod cod) :=
  match cod as c return RCod c -> Type with
  | Some _ => fun R => Reflexive R
  | _ => fun _  => unit
  end R.

Definition RCodTransitive (cod : option Type) (R : RCod cod) :=
  match cod as c return RCod c -> Type with
  | Some _ => fun R => Transitive R
  | _ => fun _  => unit
  end R.

Definition RCodPreOrderT (cod : option Type) (R : RCod cod) :=
  match cod as c return RCod c -> Type with
  | Some _ => fun R => PreOrderT R
  | _ => fun _  => unit
  end R.
(* Definition RCodRel (cod : option Type) (R : RCod cod) := *)
(*   match cod as c return RCod c -> (RCod c -> Prop) -> Type with *)
(*   | Some _ => fun R P => P R *)
(*   | _ => fun _ _ => unit *)
(*   end R. *)

#[global]
  Instance refineMethod_refl rep Dom Cod (R : RCod Cod)
  {HR : RCodReflexive Cod R}
  (* {HR : RCodRel Cod R Reflexive} *)
(* Instance refineMethod_refl rep Dom Cod RCod `{Reflexive (Comp rep) RCod} *)
: Reflexive (@refineMethod rep rep eq Dom Cod R).
Proof.
  unfold refineMethod, methodType. intro. simpl. intros. subst.
  remember (x r_n).
  induction Dom.
  - destruct Cod; intro; simpl; intros; subst.
    exists v; repeat split; try destruct v; eauto.
    Core.computes_to_econstructor; try destruct v; eauto.
  (* Ok? *)
  - intro. intros. subst. simpl in x. eapply IHDom with (x := fun rn => x rn d). reflexivity.
Qed.

Lemma refineConstructor_trans
      rep rep' rep'' Dom
      AbsR AbsR'
  : forall c c' c'',
    @refineConstructor rep rep' AbsR Dom c c'
    -> @refineConstructor rep' rep'' AbsR' Dom c' c''
    -> refineConstructor
         (fun r_o r_n => exists r_o', AbsR r_o r_o' /\ AbsR' r_o' r_n)
         c c''.
Proof.
  induction Dom.
  - intro; simpl; intros; subst; intros v Comp_v.
    apply H0 in Comp_v; computes_to_inv; subst.
    apply H in Comp_v; computes_to_inv; subst; eauto.
  - simpl; intros; eapply IHDom; simpl in *.
    apply H.
    eapply H0.
Qed.

Lemma refineConstructor_eq_trans
      rep rep' Dom
      AbsR
  : forall c c' c'',
    @refineConstructor rep rep' AbsR Dom c c'
    -> @refineConstructor_eq rep' Dom c' c''
    -> refineConstructor AbsR c c''.
Proof.
  induction Dom.
  - intro; simpl; intros; subst; intros v Comp_v.
    apply H0 in Comp_v; computes_to_inv; subst.
    apply H in Comp_v; computes_to_inv; subst; eauto.
  - simpl; intros; eapply IHDom; simpl in *.
    apply H.
    eapply H0.
Qed.

#[global]
Instance refineConstructor_trans' rep Dom
: Transitive (@refineConstructor rep rep eq Dom).
Proof.
  induction Dom.
  - intro; intros.
    pose proof (refineConstructor_trans nil eq eq x y z H H0);
      unfold refineConstructor, refineEq; intros.
    eapply H1 in H2; computes_to_inv; subst.
    destruct_ex; intuition; subst; eauto.
  - simpl; intro; intros.
    eapply IHDom.
    apply H.
    apply H0.
Qed.

Lemma refineMethod_trans rep rep' rep'' Dom Cod
      AbsR AbsR'
      (R : RCod Cod) {HR : RCodTransitive Cod R}
  : forall m m' m'',
    @refineMethod rep rep' AbsR Dom Cod R m m'
    -> @refineMethod rep' rep'' AbsR' Dom Cod R m' m''
    -> refineMethod (fun r_o r_n => exists r_o', AbsR r_o r_o' /\ AbsR' r_o' r_n)
                         R m m''.
Proof.
  unfold refineMethod, methodType; induction Dom.
  - intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto.
      destruct Comp_v as [v' [Comp_v' [Heq Hrel]]].
      computes_to_inv; subst.
      eapply H in Comp_v'; eauto.
      destruct Comp_v' as [v'' [Comp_v''' [Heq' Hrel']]].
      computes_to_inv; subst; eauto.
      simpl in Heq, Heq', Hrel, Hrel'.
      exists (v1, snd v2). repeat split; eauto.
      eapply BindComputes. apply Comp_v'''.
      subst.
      eapply @BindComputes.
      eapply @PickComputes.
      exists (fst v0). split; eauto.
      eapply @ReturnComputes.

    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto; computes_to_inv; subst.
      eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
  - simpl; intros.
    destruct_ex; intuition.
    eapply (IHDom (fun d' => m r_o d)
                  (fun d' => m' x d)
                  (fun d' => m'' r_n d)); eauto.
Qed.

Lemma refineMethod_eq_trans rep rep' Dom Cod
      AbsR
      (R : RCod Cod) {HR : RCodTransitive Cod R}
  : forall m m' m'',
    @refineMethod rep rep' AbsR Dom Cod R m m'
    -> @refineMethod_eq rep' Dom Cod m' m''
    -> refineMethod AbsR R m m''.
Proof.
  unfold refineMethod, methodType; induction Dom.
  - intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto; computes_to_inv; subst.
      eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
    + destruct_ex; intuition.
      eapply H0 in Comp_v; eauto; computes_to_inv; subst.
      eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
  - simpl; intros.
    destruct_ex; intuition.
    unfold refineMethod_eq in *.
    eapply (IHDom (fun r_o => m r_o d)
                  (fun r_n => m' r_n d)
                  (fun r_n => m'' r_n d)); eauto.
    intros; eapply H0.
Qed.

#[global]
Instance refineMethod_trans' rep Dom Cod
(R : RCod Cod) {HR : RCodTransitive Cod R}
: Transitive (@refineMethod rep rep eq Dom Cod R).
Proof.
(*   unfold refineMethod, methodType; subst; induction Dom. *)
(*   - intro; intros. *)
(*     pose proof (refineMethod_trans H H0); *)
(*       unfold refineMethod, refineMethod', refine in *; destruct Cod; intros; subst. *)
(*     + eapply H2 in H3; eauto; computes_to_inv; subst. *)
(*       destruct_ex; intuition; subst; eauto. *)
(*     + eapply H2 in H3; eauto; computes_to_inv; subst. *)
(*       destruct_ex; intuition; subst; eauto. *)
(*   - intro; simpl; intros; subst. *)
(*     eapply (IHDom (fun d' => x r_n d) *)
(*                   (fun d' => y r_n d) *)
(*                   (fun d' => z r_n d)) with (r_o := r_n); eauto. *)
(* Qed. *)
Admitted.

Global Instance refineADT_PreOrder Sig
  RCods {HR : forall idx, RCodPreOrderT (snd (MethodDomCod Sig idx)) (RCods idx)} :
  PreOrderT (refineADT RCods).
Proof.
  split; compute in *.
  - intro x; destruct x.
    econstructor 1 with
    (AbsR := @eq Rep);
      try reflexivity.
    intros. simpl.
    apply refineMethod_refl.
    specialize (HR idx).
    unfold RCodReflexive.
    destruct Sig. simpl in *.
    unfold snd.
    revert HR.
    set (R := RCods idx).
    clearbody R.
    clear RCods.
    destruct (MethodDomCod idx).
    destruct o; eauto.
    intros HR. apply PreOrderT_ReflexiveT.
  - intros x y z H H'.
    destruct H as [AbsR ? ?].
    destruct H' as [AbsR' ? ?].
    econstructor 1 with
      (AbsR := fun x z => exists y, AbsR x y /\ AbsR' y z);
      simpl in *; intros.
    + eauto using refineConstructor_trans.
    + eauto using refineMethod_trans.
      eapply refineMethod_trans; eauto.
      specialize (HR idx). unfold RCodTransitive, snd.
      revert HR. destruct Sig; simpl.
      set (R := RCods idx); clearbody R. clear -R.
      destruct (MethodDomCod idx); destruct o; eauto.
      intros HR; eapply PreOrderT_TransitiveT.
Qed.

(*Add Parametric Relation Sig : (ADT Sig) refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.*)

(** Refining the representation type is a valid refinement, as long as
    the new methods are valid refinements.

    If we had dependent setoid relations in [Type], then we could
    write

<<
Add Parametric Morphism : @Build_ADT
  with signature
  (fun oldM newM => newM -> Comp oldM)
    ==> arrow
    ==> arrow
    ==> (pointwise_relation _ (@refineConstructor _ _ _))
    ==> (pointwise_relation _ (@refineMethod _ _ _))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  ...
Qed.
>>

    But, alas, Matthieu is still working on those.  So the rewrite
    machinery won't work very well when we're switching reps, and
    we'll instead have to use [etransitivity] and [apply] the
    [refineADT_Build_ADT_Rep] lemma to switch representations.

    The statement of [refineADT_Build_ADT_Rep] mimics the notation for
    registering [Parametric Morphism]s so that it will be easy to
    integrate if dependent setoid relations are added.

 *)

Lemma refineADT_Build_ADT_Rep Sig oldRep newRep
      (AbsR : oldRep -> newRep -> Prop)
      RCods
:
  (@respectful_heteroT
     (forall idx, constructorType oldRep (ConstructorDom Sig idx))
     (forall idx, constructorType newRep (ConstructorDom Sig idx))
     (fun oldConstrs =>
        (forall idx,
           methodType oldRep (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx)))
        -> ADT Sig)
     (fun newConstrs =>
        (forall idx,
           methodType newRep (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx)))
        -> ADT Sig)
     (fun oldConstrs newConstrs =>
        forall mutIdx,
          @refineConstructor oldRep newRep AbsR
                         _
                         (oldConstrs mutIdx)
                         (newConstrs mutIdx))
     (fun x y => @respectful_heteroT
                   (forall idx, methodType oldRep _ _)
                   (forall idx, methodType newRep _ _)
                   (fun _ => ADT Sig)
                   (fun _ => ADT Sig)
                   (fun obs obs' =>
                      forall obsIdx : MethodIndex Sig,
                        @refineMethod oldRep newRep AbsR
                                        (fst (MethodDomCod Sig obsIdx))
                                        (snd (MethodDomCod Sig obsIdx))
                                        (RCods obsIdx)
                                        (obs obsIdx)
                                        (obs' obsIdx))
                   (fun obs obs' => refineADT RCods)))
    (@Build_ADT Sig oldRep)
    (@Build_ADT Sig newRep).
Proof.
  unfold Proper, respectful_heteroT; intros.
  let A := match goal with |- refineADT ?RCods ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?RCods ?A ?B => constr:(B) end in
  eapply (@refinesADT Sig RCods A B AbsR);
    unfold id, pointwise_relation in *; simpl in *; intros; eauto.
Qed.

(** Thankfully, we can register a number of different refinements
    which follow from [refineADT_Build_ADT_Rep] as [Parametric
    Morphism]s... or we could, if [refineADT] were in [Prop]. *)

(** Refining Methods is a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Method rep Sig RCods cs
: forall ms ms',
    (forall idx, @refineMethod _ _ eq
                                 (fst (MethodDomCod Sig idx))
                                 (snd (MethodDomCod Sig idx))
                                 (RCods idx)
                                 (ms idx) (ms' idx))
    -> refineADT RCods (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs ms').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(** Refining Constructors is also a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Constructors rep Sig RCods ms
  {HR : forall idx, RCodReflexive (snd (MethodDomCod Sig idx)) (RCods idx)}
: forall cs cs',
    (forall idx, @refineConstructor _ _ eq
                                (ConstructorDom Sig idx)
                                (cs idx) (cs' idx))
    -> refineADT RCods (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs' ms).
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto.
  intros obsIdx. apply refineMethod_refl.
  specialize (HR obsIdx); revert HR.
  unfold RCodReflexive.
  set (R := RCods obsIdx); clearbody R; clear -R.
  destruct (snd _); eauto.
Qed.

(** Refining observers and mutators at the same time is also a valid
    refinement. [BD: I've come to the conclusion that smaller
    refinement steps are better, so using the previous refinements
    should be the preferred mode. ]*)

Lemma refineADT_Build_ADT_Both rep Sig RCods
: forall ms ms',
    (forall idx, @refineMethod _ _ eq
                                 (fst (MethodDomCod Sig idx))
                                 (snd (MethodDomCod Sig idx))
                                 (RCods idx)
                                 (ms idx) (ms' idx))
    -> forall cs cs',
         (forall idx, @refineConstructor _ _ eq
                                     (ConstructorDom Sig idx)
                                     (cs idx) (cs' idx))
         -> refineADT RCods (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs' ms').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* If [refineADT] lived in [Prop], we'd be able to register
   refineADT_Build_ADT_Both as a morphism.

Add Parametric Morphism Sig rep
: (@Build_ADT Sig rep)
    with signature
    (fun mut mut' =>
       forall idx, @refineConstructor _ _ eq
                                   (ConstructorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> (fun obs obs' =>
       forall idx, @refineMethod _ _ eq
                                   (fst (MethodDomCod Sig idx))
                                   (snd (MethodDomCod Sig idx))
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Both.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.*)
