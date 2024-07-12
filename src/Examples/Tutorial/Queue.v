Require Import Tutorial.

Section data.
  Variable data : Set.
  Hypotheses (HRdata : Refinable data)
               (HCdata : Complete data)
               (HCMdata : CompleteMinimal data)
               (Hdata_not_impl : forall d : data, d ⊑ ? data).

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


  (* Relation to be used for the outputs of each method *)
  Definition SigRCods (A : refinableType) := (ARef A).(refinement).

  Instance sigRCodsReflexive A : Reflexive (SigRCods A).
   typeclasses eauto.
  Qed.

  Instance sigRCodsTransitive A : Transitive (SigRCods A).
   typeclasses eauto.
  Qed.

  Instance refineProd_SigRCods_Reflexive {A} `{Refinable A} {B} : Reflexive (@refineProd SigRCods (↑A) B).
  typeclasses eauto.
  Qed.

  Lemma complete_list_cons :
    forall l,
      is_complete l ->
      l <> [] ->
      l = hd dummy l :: tl l.
  Proof.
    inversion 1; eauto; contradiction.
  Qed.

  Hint Resolve complete_list_cons.


  (* Now we start deriving an implementation, in a correct-by-construction way. *)
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

    - finalize.
      + unfold refineMethod, refineMethod'; intros; subst.
        monad_simpl. pick.
        higher_order_reflexivity.

      + unfold refineMethod, refineMethod'; intros; subst.
        refineEqProdSimpl. pick. monad_simpl. done.
        higher_order_reflexivity.

  Defined.

  (* We can now extract a standlone Gallina term for this ADT. *)
  Definition impl := Eval simpl in projT1 implementation.
  Print impl.



  (*******************************************)
  (*             OLD FILE CONTENT            *)
  (*******************************************)
  (* Let's try that again, with more automation. *)
(*   Hint Resolve rel_initial rel_push rel_must_be_nil rel_reversed_rep rel_fast_rep. *)

(*   Theorem more_automated_implementation : FullySharpened spec. *)
(*   Proof. *)
(*     start sharpening ADT. *)
(*     hone representation using rel. *)

(*     monad_simpl. *)
(*     pick. *)
(*     done. *)

(*     monad_simpl. *)
(*     pick. *)
(*     done. *)

(*     refine_testnil (fst r_n). *)

(*     refine_testnil (snd r_n). *)

(*     assert (r_o = nil) by eauto. *)
(*     subst. *)
(*     monad_simpl. *)
(*     pick. *)
(*     monad_simpl. *)
(*     done. *)

(*     refine_let (rev (snd r_n)). *)

(*     erewrite eta_abs_snd with (abs := r_o) by eauto. *)
(*     monad_simpl. *)
(*     pick. *)
(*     monad_simpl. *)
(*     erewrite rel_reversed_data by eauto. *)
(*     done. *)

(*     cbv beta. *)
(*     done. *)

(*     erewrite eta_abs_fst with (abs := r_o) by eauto. *)
(*     monad_simpl. *)
(*     pick. *)
(*     monad_simpl. *)
(*     erewrite rel_fast_data with (abs := r_o) by eauto. *)
(*     done. *)

(*     cleanup. *)
(*     done. *)

(*     finalize. *)
(*   Defined. *)

(*   (* We can go further, building tactics to automate most of our strategy. *) *)

(*   Ltac queue' := *)
(*     repeat match goal with *)
(*            | _ => progress monad_simpl *)
(*            | _ => pick *)
(*            | [ H : rel ?abs _ |- _ ] => *)
(*              match abs with *)
(*              | nil => fail 1 *)
(*              | _ => assert (abs = nil) by eauto; subst *)
(*              end *)
(*            | [ _ : rel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] => *)
(*              (erewrite eta_abs_fst with (abs := abs_) by eauto) *)
(*              || (erewrite eta_abs_snd with (abs := abs_) by eauto) *)
(*            | [ |- context[hd dummy _] ] => *)
(*              (erewrite rel_reversed_data by eauto) *)
(*              || (erewrite rel_fast_data by eauto) *)
(*            end. *)

(*   Ltac queue := queue'; done. *)

(*   Theorem even_more_automated_implementation : FullySharpened spec. *)
(*   Proof. *)
(*     start sharpening ADT. *)
(*     hone representation using rel; try queue. *)

(*     refine_testnil (fst r_n); [ *)
(*       refine_testnil (snd r_n); [ queue | *)
(*         refine_let (rev (snd r_n)); queue | queue ] | queue | ]. *)

(*     cleanup; done. *)

(*     finalize. *)
(*   Defined. *)


(*   (* OK, we just spent all that effort on automating the derivation. *)
(*    * Ideally the same automation will keep working with different implementations. *)
(*    * Let's try another (dumb, slow) one. *) *)
(*   Definition dumbAbsRel (abs conc : list data) := conc = rev abs. *)

(*   Fixpoint getLast (ls : list data) : (list data * data) := *)
(*     match ls with *)
(*     | nil => (nil, dummy) *)
(*     | d :: nil => (nil, d) *)
(*     | d :: ls' => *)
(*       let p := getLast ls' in *)
(*       (d :: fst p, snd p) *)
(*     end. *)

(*   Lemma dumbAbsRel_initial : dumbAbsRel nil nil. *)
(*   Proof. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma dumbAbsRel_push : forall abs conc d, *)
(*     dumbAbsRel abs conc *)
(*     -> dumbAbsRel (abs ++ d :: nil) (d :: conc). *)
(*   Proof. *)
(*     unfold dumbAbsRel; simpl; intros. *)
(*     rewrite rev_unit. *)
(*     congruence. *)
(*   Qed. *)

(*   Lemma dumbAbsRel_must_be_nil : forall abs conc, *)
(*     dumbAbsRel abs conc *)
(*     -> conc = nil *)
(*     -> abs = nil. *)
(*   Proof. *)
(*     unfold dumbAbsRel; simpl; intros. *)
(*     subst. *)
(*     destruct abs; simpl in *; intuition. *)
(*     exfalso; eauto. *)
(*   Qed. *)

(*   Lemma dumbAbsRel_eta : forall abs conc, *)
(*     dumbAbsRel abs conc *)
(*     -> conc <> nil *)
(*     -> abs = hd dummy abs :: tl abs. *)
(*   Proof. *)
(*     unfold dumbAbsRel; simpl; intros. *)
(*     subst. *)
(*     destruct abs; intuition. *)
(*   Qed. *)

(*   Lemma getLast_append_list : forall ls d, *)
(*     fst (getLast (ls ++ d :: nil)) = ls. *)
(*   Proof. *)
(*     induction ls; simpl; intuition. *)
(*     destruct (ls ++ d :: nil) eqn:Heq. *)
(*     exfalso; eauto. *)
(*     rewrite <- Heq. *)
(*     rewrite IHls. *)
(*     auto. *)
(*   Qed. *)

(*   Lemma dumbAbsRel_pop_rep : forall abs conc r, *)
(*     dumbAbsRel abs conc *)
(*     -> conc <> nil *)
(*     -> r = getLast conc *)
(*     -> dumbAbsRel (tl abs) (fst r). *)
(*   Proof. *)
(*     unfold dumbAbsRel; intros; subst. *)
(*     destruct abs; simpl in *; intuition. *)
(*     apply getLast_append_list. *)
(*   Qed. *)

(*   Lemma getLast_append_data : forall ls d, *)
(*     snd (getLast (ls ++ d :: nil)) = d. *)
(*   Proof. *)
(*     induction ls; auto. *)

(*     intros. *)
(*     simpl app. *)
(*     unfold getLast. *)
(*     fold getLast. *)
(*     destruct (ls ++ d :: nil) eqn:Heq. *)
(*     exfalso; eauto. *)
(*     rewrite <- Heq. *)
(*     rewrite IHls. *)
(*     auto. *)
(*   Qed. *)

(*   Lemma dumbAbsRel_pop_data : forall abs conc r, *)
(*     dumbAbsRel abs conc *)
(*     -> conc <> nil *)
(*     -> r = getLast conc *)
(*     -> hd dummy abs = snd r. *)
(*   Proof. *)
(*     unfold dumbAbsRel; intros; subst. *)
(*     destruct abs; simpl in *; intuition. *)
(*     rewrite getLast_append_data; auto. *)
(*   Qed. *)

(*   Hint Resolve dumbAbsRel_initial dumbAbsRel_push dumbAbsRel_must_be_nil dumbAbsRel_pop_rep. *)

(*   (* Here's our first derivation, showing a bit more manual perspective. *) *)
(*   Theorem dumb_implementation : FullySharpened spec. *)
(*   Proof. *)
(*     start sharpening ADT. *)
(*     hone representation using dumbAbsRel; try queue. *)

(*     refine_testnil r_n. *)

(*     assert (r_o = nil) by eauto. *)
(*     subst. *)
(*     queue. *)

(*     refine_let (getLast r_n). *)
(*     erewrite dumbAbsRel_eta with (abs := r_o) by eauto. *)
(*     erewrite dumbAbsRel_pop_data by eauto. *)
(*     queue. *)

(*     cleanup. *)
(*     done. *)

(*     finalize. *)
(*   Defined. *)

(*   (* We use a double colon to override the prior definition. *) *)
(*   Ltac queue' ::= *)
(*     repeat match goal with *)
(*            | _ => progress monad_simpl *)
(*            | _ => pick *)
(*            | [ H : dumbAbsRel ?abs _ |- _ ] => *)
(*              match abs with *)
(*              | nil => fail 1 *)
(*              | _ => assert (abs = nil) by eauto; subst *)
(*              end *)
(*            | [ _ : dumbAbsRel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] => *)
(*              erewrite dumbAbsRel_eta with (abs := abs_) by eauto *)
(*            | [ |- context[hd dummy _] ] => *)
(*              erewrite dumbAbsRel_pop_data by eauto *)
(*            end. *)

(*   (* Now let's automate it more. *) *)
(*   Theorem more_automated_dumb_implementation : FullySharpened spec. *)
(*   Proof. *)
(*     start sharpening ADT. *)
(*     hone representation using dumbAbsRel; try queue. *)

(*     refine_testnil r_n; [ queue | *)
(*       refine_let (getLast r_n); queue | ]. *)

(*     queue'. *)
(*     cleanup. *)
(*     done. *)

(*     finalize. *)
(*   Defined. *)
End data.
