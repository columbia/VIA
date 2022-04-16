Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition realm_destroy_ops_spec (g_rtt: Pointer) (g_rec_list: Pointer) (g_rd: Pointer) (adt: RData) : option RData :=
    when adt == query_oracle adt;
    rely (peq (base g_rtt) ginfo_loc);
    rely (peq (base g_rec_list) ginfo_loc);
    rely (peq (base g_rd) ginfo_loc);
    let rtt_gidx := offset g_rtt in
    let rec_list_gidx := offset g_rec_list in
    let rd_gidx := offset g_rd in
    rely is_gidx rtt_gidx; rely is_gidx rec_list_gidx; rely is_gidx rd_gidx;
    let grd := (gs (share adt)) @ rd_gidx in
    let grtt := (gs (share adt)) @ rtt_gidx in
    let grecl := (gs (share adt)) @ rec_list_gidx in
    rely prop_dec (glock grd = Some CPU_ID);
    rely prop_dec (glock grtt = Some CPU_ID);
    rely prop_dec (glock grecl = None);
    rely (gtype grecl =? GRANULE_STATE_REC_LIST);
    rely (gtype grd =? GRANULE_STATE_RD);
    rely (gtype grtt =? GRANULE_STATE_TABLE);
    rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
    rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
    rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
    let grd' := grd {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec}
                    {ginfo: (ginfo grd) {g_tag: GRANULE_STATE_DELEGATED}} in
    let grecl' := grecl {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec}
                        {ginfo: (ginfo grecl) {g_tag: GRANULE_STATE_DELEGATED}} in
    let grtt' := grtt {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec}
                      {ginfo: (ginfo grtt) {g_rd: 0} {g_tag: GRANULE_STATE_DELEGATED}} in
    let e := EVT CPU_ID (ACQ rec_list_gidx) in
    let e1 := EVT CPU_ID (REL rtt_gidx grtt') in
    let e' := EVT CPU_ID (REL rec_list_gidx (grecl' {glock: Some CPU_ID})) in
    Some adt {log: e' :: e1 :: e :: (log adt)}
         {share: (share adt) {gs: (gs (share adt)) # rtt_gidx == (grtt' {gtype: GRANULE_STATE_DELEGATED} {glock: None})
                                                   # rec_list_gidx == (grecl' {gtype: GRANULE_STATE_DELEGATED})
                                                   # rd_gidx == grd'}}.

End Spec.
