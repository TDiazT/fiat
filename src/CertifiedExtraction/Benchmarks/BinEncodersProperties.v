Require Import BinEncoders.Env.Examples.Dns.
Require Import Bedrock.Memory.
Require Import NArith.

Unset Implicit Arguments.

Definition encode_continue {E B}
           (transformer : Transformer.Transformer B)
           (encode : E -> B * E)
           acc :=
  let (p, e') := encode (snd acc) in
  (Transformer.transform (fst acc) p, e').

Definition compose_acc {E B}
           (transformer : Transformer.Transformer B)
           (encode1 : E -> B * E)
           (encode2 : E -> B * E) e0 :=
  encode_continue transformer encode2 (encode1 e0).

Lemma Compose_compose_acc {E B} :
  forall transformer encode1 encode2 e0,
    @Compose.compose E B transformer encode1 encode2 e0 =
    @compose_acc E B transformer encode1 encode2 e0.
Proof.
  intros; unfold compose_acc, Compose.compose, encode_continue.
  destruct (encode1 _); simpl; destruct (encode2 _); reflexivity.
Qed.

Lemma IList_encode_bools_is_copy:
  forall bits cache,
    (IList.IList_encode' DnsMap.cache Core.btransformer Bool.Bool_encode bits cache) =
    (bits, {| DnsMap.eMap := DnsMap.eMap cache;
              DnsMap.dMap := DnsMap.dMap cache;
              DnsMap.offs := DnsMap.offs cache + (N.of_nat (List.length bits)) |}).
Proof.
  Opaque N.of_nat.
  induction bits; destruct cache; simpl in *.
  + rewrite N.add_0_r; reflexivity.
  + rewrite IHbits; simpl.
    rewrite <- N.add_assoc, N.add_1_l, Nat2N.inj_succ; reflexivity.
    Transparent N.of_nat.
Qed.

Require Import Coq.Lists.List.
Require Import Bedrock.Word.

Fixpoint ListBoolToWord (bs: list bool) : word (List.length bs) :=
  match bs as l return (word (Datatypes.length l)) with
  | nil => WO
  | b :: bs0 => WS b (ListBoolToWord bs0)
  end.

Theorem exist_irrel : forall A (P : A -> Prop) x1 pf1 x2 pf2,
    (forall x (pf1' pf2' : P x), pf1' = pf2')
    -> x1 = x2
    -> exist P x1 pf1 = exist P x2 pf2.
Proof.
  intros; subst; f_equal; auto.
Qed.

Module DecidableNat.
  Definition U := nat.
  Definition eq_dec := Peano_dec.eq_nat_dec.
End DecidableNat.

Module UipNat := Eqdep_dec.DecidableEqDepSet(DecidableNat).

Lemma WS_commute : forall n1 n2 (pf : S n1 = S n2) b w,
    match pf in _ = n return word n with
    | eq_refl => WS b w
    end
    = WS b (match NPeano.Nat.succ_inj _ _ pf in _ = n return word n with
            | eq_refl => w
            end).
Proof.
  intros.
  pose proof (NPeano.Nat.succ_inj _ _ pf); subst.
  rewrite (UipNat.UIP _ _ pf eq_refl).
  rewrite (UipNat.UIP _ _ (NPeano.Nat.succ_inj _ _ eq_refl) eq_refl).
  reflexivity.
Qed.

Lemma WS_commute' {n1 n2} :
  forall (pf : n1 = n2) f (g: forall {n}, word n -> word (f n)) w,
    match pf in _ = n return word (f n) with
    | eq_refl => g w
    end
    = g (match pf in _ = n return word n with
            | eq_refl => w
            end).
Proof.
  destruct pf; reflexivity.
Qed.

Lemma ListBoolToWord_eq : forall n ls1 ls2 (pf1 : List.length ls1 = n) (pf2 : List.length ls2 = n),
    match pf1 in _ = n return word n with
    | eq_refl => ListBoolToWord ls1
    end
    = match pf2 in _ = n return word n with
      | eq_refl => ListBoolToWord ls2
      end
    -> ls1 = ls2.
Proof.
  induction n; destruct ls1, ls2; simpl; intuition; try congruence.
  repeat rewrite (WS_commute) in H.
  inversion H; clear H; subst.
  apply UipNat.inj_pair2 in H2.
  f_equal; eauto.
Qed.

Definition ListBool16ToWord (bs: {xs: list bool | List.length xs = 16}) : word 32 :=
  let (bs, p) := bs in
  match p in _ = n return word (16 + n) with
  | eq_refl => (ListBoolToWord bs)~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  end.

Definition ListBool16ToWord_inj :
  forall bs bs', ListBool16ToWord bs = ListBool16ToWord bs' -> bs = bs'.
Proof.
  intros * Heq.
  unfold ListBool16ToWord in *.
  destruct bs as [? p], bs' as [? p'].
  repeat rewrite (WS_commute' _ _ (fun n w => w~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0)) in Heq.
  injection Heq; eauto using UipNat.inj_pair2, exist_irrel, UipNat.UIP, ListBoolToWord_eq.
Qed.

Definition PadToLength encoded length :=
  FixInt.pad encoded (length - Datatypes.length encoded).

Definition EncodeAndPad n length :=
  let encoded := FixInt.encode' n in
  PadToLength encoded length.

Lemma FixInt_encode_is_copy {size}:
  forall num cache,
    (FixInt.FixInt_encode (size := size) num cache) =
    (EncodeAndPad (proj1_sig num) size, {| DnsMap.eMap := DnsMap.eMap cache;
                                           DnsMap.dMap := DnsMap.dMap cache;
                                           DnsMap.offs := DnsMap.offs cache + (N.of_nat size) |}).
Proof.
  destruct cache; reflexivity.
Qed.

Inductive ListBoolEq : (list bool) -> (list bool) -> Prop :=
| ListBoolEqLeft : forall l1 l2, ListBoolEq l1 l2 -> ListBoolEq (false :: l1) l2
| ListBoolEqRight : forall l1 l2, ListBoolEq l1 l2 -> ListBoolEq l1 (false :: l2)
| ListBoolEqEq : forall l1 l2, l1 = l2 -> ListBoolEq l1 l2.

Hint Constructors ListBoolEq : listBoolEq.

Require Import Program.

Lemma EncodeAndPad_ListBool16ToWord : forall ls, proj1_sig ls = EncodeAndPad (wordToN (ListBool16ToWord ls)) 16.
Admitted.

Lemma NToWord_of_nat:
  forall (sz : nat) (n : nat),
    NToWord _ (N.of_nat n) = natToWord sz n.
Proof.
  intros; rewrite NToWord_nat, Nat2N.id; reflexivity.
Qed.

Lemma NToWord_WordToN:
  forall (sz : nat) (w : word sz),
    NToWord _ (wordToN w) = w.
Proof.
  intros; rewrite NToWord_nat, wordToN_nat, Nat2N.id.
  apply natToWord_wordToNat.
Qed.

Lemma length_of_fixed_length_list :
  forall {size} (ls: {s : list bool | Datatypes.length s = size}),
    List.length (proj1_sig ls) = size.
Proof.
  destruct ls; auto.
Qed.

Lemma FixList_is_IList :
  forall (A bin : Type) (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (env : Cache.CacheEncode),
    @FixList.FixList_encode' A bin cache transformer A_encode xs env =
    @IList.IList_encode' A bin cache transformer A_encode xs env.
Proof.
  induction xs; simpl; intros.
  + reflexivity.
  + destruct (A_encode _ _).
    rewrite IHxs; reflexivity.
Qed.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.PropertiesOfTelescopes.

Lemma IList_post_transform_TelEq :
  forall {av} {A bin : Type}
    (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (base : bin) (env : Cache.CacheEncode)
    k__stream (tenv: _ -> Telescope av) ext,
    let fold_on b :=
        List.fold_left (IList.IList_encode'_body cache transformer A_encode) xs (b, env) in
    (forall a1 a2 b, tenv (a1, b) = tenv (a2, b)) ->
    TelEq ext
          ([[ret (fold_on Transformer.transform_id) as folded]]
             ::[[ k__stream <-- Transformer.transform base (fst folded) as _]] :: tenv folded)
          ([[ret (fold_on base) as folded]]
             ::[[ k__stream <-- fst folded as _]] :: tenv folded).
Proof.
  cbv zeta; intros * H.
  setoid_rewrite Propagate_anonymous_ret.
  rewrite (IList.IList_encode'_body_characterization _ _ _ _ base).
  destruct (List.fold_left _ _ _); simpl; erewrite H; reflexivity.
Qed.
