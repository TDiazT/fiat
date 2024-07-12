Require Import Fiat.Common
        Fiat.ADTNotation.BuildADT Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms.

(* A notation-friendly version of the setoid morphisms
   infrastructure for ADT refinement. *)

Theorem refineADT_BuildADT_Rep RCods n n' consSigs methSigs oldRep newRep
      (AbsR_mono : oldRep -> newRep -> Prop)
      (AbsR_anti : oldRep -> newRep -> Prop)
: @respectful_heteroT _ _ _ _
      (fun oldCons newCons =>
         forall consIdx,
           @refineConstructor oldRep newRep AbsR_mono
                          _
                          (getConsDef oldCons consIdx)
                          (getConsDef newCons consIdx))
      (fun x y => @respectful_heteroT _ _ _ _
                    (fun oldMeth newMeth =>
                       forall methIdx,
                         @refineMethod oldRep newRep AbsR_mono AbsR_anti RCods _ _
                                         (getMethDef oldMeth methIdx)
                                         (getMethDef newMeth methIdx))
                    (fun m m' => refineADT RCods))
     (@BuildADT oldRep n n' consSigs methSigs)
     (@BuildADT newRep n n' consSigs methSigs).
 Proof.
   unfold Proper, respectful_heteroT; intros.
   let A := match goal with |- refineADT ?RCods ?A ?B => constr:(A) end in
   let B := match goal with |- refineADT ?RCods ?A ?B => constr:(B) end in
   eapply (@refinesADT RCods _ A B AbsR_mono AbsR_anti);
     unfold id, pointwise_relation in *; simpl in *; intros; eauto.
 Qed.

Lemma refineADT_BuildADT_Both
  RCods rep n n' consigs methSigs
  : forall oldCons newCons,
    (forall consIdx, @refineConstructor _ _ eq _
                  (getConsDef oldCons consIdx)
                  (getConsDef newCons consIdx))
    -> forall oldMeth newMeth,
      (forall methIdx, @refineMethod _ _ eq eq RCods _ _
                      (getMethDef oldMeth methIdx)
                      (getMethDef newMeth methIdx))
      -> refineADT RCods (@BuildADT n n' rep consigs methSigs oldCons oldMeth)
          (@BuildADT n n' rep consigs methSigs newCons newMeth).
Proof.
  intros; eapply refineADT_BuildADT_Rep; eauto; reflexivity.
Qed.

(*Add Parametric Morphism rep consigs methSigs
: (@BuildADT rep consigs methSigs)
    with signature
    (fun oldCons newCons =>
       forall consIdx, @refineConsator _ _ eq _
                                  (getConsDef oldCons consIdx)
                                  (getConsDef newCons consIdx))
      ==> (fun oldMeth newMeth =>
             forall methIdx, @refineMetherver _ _ eq _ _
                                         (getMethDef oldMeth methIdx)
                                         (getMethDef newMeth methIdx))
      ==> refineADT
      as refineADT_BuildADT_Both.
Proof.
  intros; apply refineADT_BuildADT_Both'.
Qed.*)
