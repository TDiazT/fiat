Require Import
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.ib.FixList
        Fiat.Narcissus.BinLib.FixInt.

Set Implicit Arguments.

Record test_t :=
  { f1 : { n : N | (n < exp2 32)%N };
    f2 : { l : list {n : N | (n < exp2 16)%N} | length l < exp2_nat 16} } .

Instance test_cache : Cache :=
  {| CacheEncode := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance test_cache_add_nat : CacheAdd test_cache N :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ => id |}.

Definition encode_test (t : test_t) (ce : CacheEncode) :=
  compose bmonoid (FixInt_encode (f1 t)) (
  compose bmonoid (FixInt_encode (FixList_getlength (f2 t))) (
  compose bmonoid (FixList_encode FixInt_encode (f2 t)) (
                       (fun e => (nil, e))))) ce.
(* Commenting out until we update for new framework. *)
(*
Definition test_decoder
  : { decode | encode_decode_correct test_cache bmonoid (fun _ => True) encode_test decode }.
Proof.
  eexists.
  eapply compose_encode_correct. eapply FixInt_encode_correct. solve_predicate.
  intro.
  eapply compose_encode_correct. eapply FixInt_encode_correct. solve_predicate.  
  intro.
  eapply compose_encode_correct.
  eapply FixList_encode_correct.
  eapply FixInt_encode_correct.
  solve_predicate.
  intro.
  solve_done.
Defined.

Definition test_decoder'
  : list bool -> CacheDecode -> test_t * list bool * CacheDecode.
Proof.
  let p' := eval cbv delta [ proj1_sig test_decoder ] beta iota in (proj1_sig test_decoder) in
                                                                      pose p' as p.
  exact p.
Defined.
Print test_decoder'. *)