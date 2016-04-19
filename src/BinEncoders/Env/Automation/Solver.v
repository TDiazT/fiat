Require Import Fiat.BinEncoders.Env.Common.Sig
               Fiat.BinEncoders.Env.Common.Compose.


Require Import Fiat.BinEncoders.Env.BinLib.Core
               Fiat.BinEncoders.Env.BinLib.FixInt
               Fiat.BinEncoders.Env.BinLib.Char
               Fiat.BinEncoders.Env.BinLib.Bool
               Fiat.BinEncoders.Env.BinLib.Enum
               Fiat.BinEncoders.Env.Lib.FixList
               Fiat.BinEncoders.Env.Lib.IList
               Fiat.BinEncoders.Env.Lib.SteppingCacheList.

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec _ n arg then res else h n) func;
      reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac idtac' :=
  match goal with
    | |- _ => idtac (* I actually need this idtac for some unknown reason *)
  end.

Definition FixInt_eq_dec (size : nat) (n m : {n | (n < exp2 size)%N }) : {n = m} + {n <> m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
    destruct n; destruct m; try congruence; simpl in *; rewrite <- sig_equivalence; eauto.
Defined.

Ltac solve_enum :=
  let h := fresh in
  intros h; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Ltac solve_done :=
  intros ? ? ? ? data ? ? ? ?;
    instantiate (1:=fun _ b e => (_, b, e));
    intros; destruct data; simpl in *; repeat match goal with
                   | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
                   | H : _ /\ _ |- _ => inversion H; subst; clear H
                   end; intuition eauto; fail 0.

Ltac solve_predicate :=
  unfold SteppingList_predicate, IList_predicate, FixList_predicate;
  intuition eauto; instantiate (1:=fun _ => True); solve_predicate.

Ltac eauto_typeclass :=
  match goal with
  | |- context [ Bool_encode ] => eapply Bool_encode_correct
  | |- context [ Char_encode ] => eapply Char_encode_correct
  | |- context [ FixInt_encode ] => eapply FixInt_encode_correct
  | |- context [ FixList_encode _ ] => eapply FixList_encode_correct
  | |- context [ IList_encode _ ] => eapply IList_encode_correct
  | |- context [ SteppingList_encode _ _ _ ] => eapply SteppingList_encode_correct
  end; eauto.

Ltac solve_decoder :=
  match goal with
  | |- _ => solve [ eauto_typeclass; solve_decoder ]
  | |- _ => solve [ eapply Enum_encode_correct; solve_enum ]
  | |- _ => solve [ solve_done ]
  | |- _ => eapply compose_encode_correct; [ solve_decoder | solve_predicate | intro; solve_decoder ]
  end.