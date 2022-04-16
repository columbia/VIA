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
            id_rdata: hadt = ladt
        }.

End RefineRel.

