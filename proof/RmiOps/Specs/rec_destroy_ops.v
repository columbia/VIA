Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition rec_destroy_ops_spec (g_rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base g_rec) ginfo_loc);
    let rec_gidx := (offset g_rec) in
    rely is_gidx rec_gidx;
    let gn := (gs (share adt)) @ rec_gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    rely (gtype gn =? GRANULE_STATE_REC);
    rely prop_dec (glock gn = Some CPU_ID);
    rely prop_dec (gref gn = None);
    rely (g_inited (gro gn));
    rely prop_dec ((buffer (priv adt)) @ SLOT_REC = None);
    rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
    let rd_gidx := g_rd (ginfo gn) in
    let rec_list_gidx := g_rec_rec_list (grec gn) in
    let rec_idx := g_rec_idx (gro gn) in
    rely is_int64 rec_idx; rely is_gidx rd_gidx; rely is_gidx rec_list_gidx;
    let gn_recl := (gs (share adt)) @ rec_list_gidx in
    let gn_rd := (gs (share adt)) @ rd_gidx in
    rely (gtype gn_recl =? GRANULE_STATE_REC_LIST);
    rely (gtype gn_rd =? GRANULE_STATE_RD);
    rely (gcnt gn_rd >? 0);
    let gn_recl' := gn_recl {gnorm: (gnorm gn_recl) {g_data: (g_data (gnorm gn_recl)) # rec_idx == 0}} in
    let gn_rec' := gn {ginfo: (ginfo gn) {g_rd: 0} {g_tag: GRANULE_STATE_DELEGATED}}
                      {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
    let gn_rd' := gn_rd {gcnt: (gcnt gn_rd) - 1} in
    let e := EVT CPU_ID (RECL rec_list_gidx rec_idx UNSET_RECL) in
    let e' := EVT CPU_ID (REL rec_gidx gn_rec') in
    let e'' := EVT CPU_ID (DEC_RD_GCNT rd_gidx) in
    Some adt {log: e'' :: e' :: e :: log adt}
             {share: (share adt) {gs: (gs (share adt)) # rec_list_gidx == gn_recl'
                                                       # rec_gidx == (gn_rec' {glock: None} {gtype: GRANULE_STATE_DELEGATED})
                                                       # rd_gidx == gn_rd'}}.

End Spec.
