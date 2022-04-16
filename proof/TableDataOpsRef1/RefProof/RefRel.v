Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section RefineRel.

  Record relate_RData (hadt: RData) (ladt: RData) :=
      mkrelate_RData {
          id_priv: priv ladt = priv hadt;
          id_share: share ladt = share hadt;
          hrepl: repl hadt = replay 2;
          lrepl: repl ladt = replay 1;
          valid_ho: ValidOracle 2 (oracle hadt);
          valid_lo: ValidOracle 1 (oracle ladt);
          rel_oracle: forall st st' l l',
              let lh := oracle hadt l in
              let lo := oracle ladt l' in
              st = st' -> repl ladt lo st = repl hadt lh st'
        }.

End RefineRel.

Ltac rewrite_oracle_rel R H :=
  match type of H with
  | repl ?habd (oracle ?habd ?l) ?st = _ =>
    match goal with
    | [ |- context[repl ?labd (oracle ?labd ?l') st]] =>
      rewrite (R st st l l'); [rewrite H|reflexivity]
    end
  end.
