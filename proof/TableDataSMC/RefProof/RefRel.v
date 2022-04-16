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

  Inductive relate_share: option State -> option State -> Prop :=
  | RELATE_NONE: relate_share None None
  | RELATE_SHARE: forall st st'
                    (id_gs: gs st = gs st')
                    (id_gpt: gpt st = gpt st')
                    (id_gpt_lk: gpt_lk st = gpt_lk st')
                    (id_gpt_lk: tlbs st = tlbs st'),
      relate_share (Some st) (Some st').

  Record relate_RData (hadt: RData) (ladt: RData) :=
      mkrelate_RData {
          id_priv: priv ladt = priv hadt;
          rel_share: relate_share (Some (share ladt)) (Some (share hadt));
          hrepl: repl hadt = replay 4;
          lrepl: repl ladt = replay 3;
          valid_ho: ValidOracle 4 (oracle hadt);
          valid_lo: ValidOracle 3 (oracle ladt);
          rel_oracle: forall st st' l l',
              let lh := oracle hadt l in
              let lo := oracle ladt l' in
              relate_share (Some st) (Some st') -> relate_share (repl ladt lo st) (repl hadt lh st')
        }.

End RefineRel.
