Require Import List.
Require Import Setoid Morphisms AdditionalLemmas.

Add Parametric Morphism {A: Type} :
  (fun (P: A -> Prop) => exists x, P x)
    with signature (pointwise_relation A iff ==> iff)
      as exists_eq_iff_morphism.
Proof.
  intros * equiv;
  split; intro H; destruct H as [x0 H']; exists x0;
  apply equiv in H'; assumption.
Qed.

Add Parametric Morphism {A B: Type} :
  (fun comp seq => List.map comp seq)
    with signature (pointwise_relation A (@eq B) ==> eq ==> (@eq (list B)))
      as map_eq_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq;
  induction seq as [ | ? ? IH ]; simpl; [ | rewrite IH, equiv ]; trivial.
Qed.

Add Parametric Morphism {A B: Type} (seq: list A) :
  (fun comp => List.map comp seq)
    with signature (pointwise_relation A (@eq B) ==> (@eq (list B)))
      as map_eq_restricted_morphism.
Proof.
  intros.
  setoid_rewrite H; trivial.
Qed.

Add Parametric Morphism {A: Type} :
  (@List.filter A)
    with signature (pointwise_relation A (@eq bool) ==> @eq (list A) ==> @eq (list A))
      as filter_eq_morphism.
Proof.
  intros * equiv seq;
  unfold pointwise_relation in equiv;
  induction seq as [ | h t IH ]; 
  simpl;
  [ | rewrite equiv, IH ];
  trivial.
Qed.

Add Parametric Morphism {A: Type} (seq: list A) :
  (fun pred => @List.filter A pred seq)
    with signature (pointwise_relation A (@eq bool) ==> @eq (list A))
      as filter_eq_restricted_morphism.
Proof.
  intros * equiv;
  erewrite filter_eq_morphism; eauto.
Qed.

Require Import Permutation.

Add Parametric Morphism {A B: Type} :
  (@List.map A B)
    with signature (pointwise_relation A (@eq B) ==> @Permutation A ==> @Permutation B)
      as map_permutation_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq1 seq2 is_perm.

  induction is_perm; simpl; rewrite ?equiv.

  constructor.
  constructor; eauto.
  erewrite map_eq_restricted_morphism; eauto; constructor.
  econstructor; eauto; cbv beta; erewrite map_eq_restricted_morphism; eauto; symmetry; eassumption.
Qed.

Ltac destruct_ifs :=
  repeat match goal with
           | [ |- context [ if ?A then _ else _ ] ] => destruct A
         end.

Add Parametric Morphism {A: Type} :
  (@List.filter A)
    with signature (pointwise_relation A (@eq bool) ==> @Permutation A ==> @Permutation A)
      as filter_permutation_morphism.
Proof.
  intros * equiv * is_perm.

  induction is_perm; simpl; rewrite ?equiv.
  
  constructor.
  destruct_ifs; try constructor;
  erewrite filter_eq_restricted_morphism; eauto; symmetry; eassumption.
  destruct_ifs; try constructor;
  erewrite filter_eq_restricted_morphism; eauto; symmetry; eassumption.
  econstructor. erewrite filter_eq_restricted_morphism; try (symmetry; eassumption).
  eauto. erewrite filter_eq_restricted_morphism; try (symmetry; eassumption).
  eassumption.
Qed.

Add Parametric Morphism {A: Type} :
  (@List.In A)
    with signature (@eq A ==> @Permutation A ==> iff)
      as in_permutation_morphism.
Proof.
  intros * is_perm.
  split; apply Permutation_in; intuition.
Qed.

Add Parametric Morphism {A: Type} :
  (@flatten A)
    with signature (@Permutation (list A) ==> @Permutation A)
      as flatten_permutation_morphism.
Proof.
  intros * is_perm.
  
  induction is_perm; simpl.

  constructor.
  apply Permutation_app_head; trivial.
  rewrite ?List.app_assoc; apply Permutation_app_tail; apply Permutation_app_comm.
  econstructor; eauto.
Qed.

Add Parametric Morphism {A B : Type} :
  (fun comp seq => @flatten B (@List.map A (list B) comp seq))
    with signature (pointwise_relation A (@Permutation B) ==> @eq (list A) ==> @Permutation B)
      as flatten_map_permutation_eq_permutation_morphism.
Proof.
  intros * equiv * seq.

  induction seq; simpl.
  constructor.
  apply Permutation_app; eauto.
Qed.

Add Parametric Morphism {A B : Type} :
  (@flat_map A B)
    with signature (pointwise_relation A (@Permutation B) ==> @eq (list A) ==> @Permutation B)
      as flatmap_permutation_eq_permutation_morphism.
Proof.
  intros.
  rewrite ?flat_map_flatten.
  apply flatten_map_permutation_eq_permutation_morphism; eauto.
Qed.

Add Parametric Morphism {A B: Type} :
  (fun comp seq => @flatten B (@List.map A (list B) comp seq))
    with signature (pointwise_relation A (@Permutation B) ==> @Permutation A ==> @Permutation B)
      as flatten_map_permutation_permutation_permutation_morphism.
Proof.
  unfold pointwise_relation;
  intros * equiv seq1 seq2 is_perm.

  induction is_perm; simpl.

  constructor.
  apply Permutation_app; eauto.

  rewrite ?List.app_assoc.
  apply Permutation_app.
  rewrite Permutation_app_comm;
    apply Permutation_app; apply equiv.
  
  apply flatten_map_permutation_eq_permutation_morphism; eauto.

  etransitivity; 
    [ etransitivity; [ eauto | ] | eauto ].

  apply flatten_map_permutation_eq_permutation_morphism; try (symmetry; eauto).
Qed.

Add Parametric Morphism {A B : Type} :
  (@flat_map A B)
    with signature (pointwise_relation A (@Permutation B) ==> @Permutation A ==> @Permutation B)
      as flatmap_permutation_permutation_permutation_morphism.
Proof.
  intros.
  rewrite ?flat_map_flatten.
  apply flatten_map_permutation_permutation_permutation_morphism; eauto.
Qed.

