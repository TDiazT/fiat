(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Export Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char : Type} {HSL : StringLike Char} (G : grammar Char)
          {predata : parser_computational_predataT}
          (Hvalid : grammar_valid G).

  Local Notation P' nt := (is_true (is_valid_nonterminal initial_nonterminals_data nt)) (only parsing).
  Local Notation P nt := (P' (of_nonterminal nt)) (only parsing).

  Definition Forall_parse_of_item_valid'
             (Forall_parse_of_valid'
              : forall str pats,
                  productions_valid pats
                  -> forall p : parse_of G str pats,
                       Forall_parse_of (fun _ nt' => P nt') p)
             {str it}
             (Hit : item_valid it)
             (p : parse_of_item G str it)
  : Forall_parse_of_item (fun _ nt' => P nt') p.
  Proof.
    destruct p; simpl in *.
    { constructor. }
    { split; try assumption.
      eauto. }
  Defined.

  Fixpoint Forall_parse_of_valid
             {str pats}
             (Hv : productions_valid pats)
             (p : parse_of G str pats)
  : Forall_parse_of (fun _ nt' => P nt') p
  with Forall_parse_of_production_valid
             {str pat}
             (Hv : production_valid pat)
             (p : parse_of_production G str pat)
  : Forall_parse_of_production (fun _ nt' => P nt') p.
  Proof.
    { destruct p; simpl in *.
      { apply Forall_parse_of_production_valid.
        dependent destruction Hv; trivial. }
      { apply (fun Hv => Forall_parse_of_valid _ _ Hv p).
        dependent destruction Hv; trivial. } }
    { destruct p as [p|??? p0 p1]; simpl in *.
      { constructor. }
      { change (Forall_parse_of_item (fun _ nt' => P nt') p0
                * Forall_parse_of_production (fun _ nt' => P nt') p1).
        split.
        { apply Forall_parse_of_item_valid'; try assumption.
          dependent destruction Hv; trivial. }
        { apply Forall_parse_of_production_valid.
          dependent destruction Hv; trivial. } } }
  Defined.

  Definition Forall_parse_of_item_valid
             {str it}
             (Hit : item_valid it)
             (p : parse_of_item G str it)
  : Forall_parse_of_item (fun _ nt' => P nt') p
    := @Forall_parse_of_item_valid' (@Forall_parse_of_valid) str it Hit p.
End cfg.

Section app.
  Context {Char : Type} {HSL : StringLike Char} (G : grammar Char)
          {predata : parser_computational_predataT}.

  Lemma hd_production_valid
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : item_valid it.
  Proof.
    unfold production_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma production_valid_cons
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : production_valid its.
  Proof.
    unfold production_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma production_valid_app
        (pat pat' : production Char)
        (H : production_valid (pat ++ pat'))
  : production_valid pat'.
  Proof.
    induction pat; simpl in *; trivial.
    eapply IHpat, production_valid_cons; eassumption.
  Qed.

  (** Convenience lemmas *)
  Section convenience.
    Context {rdata : @parser_removal_dataT' _ G _}
            (Hvalid : grammar_valid G).

    Lemma reachable_production_valid
          (its : production Char)
          (Hreach : production_is_reachable G its)
    : production_valid its.
    Proof.
      destruct Hreach as [nt [prefix [Hreach Hreach']]].
      specialize (Hvalid nt Hreach).
      unfold productions_valid in Hvalid.
      rewrite Forall_forall in Hvalid.
      eapply production_valid_app, Hvalid; eassumption.
    Qed.
  End convenience.
End app.