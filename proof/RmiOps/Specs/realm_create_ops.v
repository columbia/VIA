Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition realm_create_ops_spec  (adt: RData) : option RData :=
    let gidx_rd := (locked_g (priv adt)) @ 0 in
    let gidx_rtt := (locked_g (priv adt)) @ 1 in
    let gidx_rec_list := (locked_g (priv adt)) @ 2 in
    rely is_gidx gidx_rd; rely is_gidx gidx_rtt; rely is_gidx gidx_rec_list;
    rely (negb (gidx_rd =? gidx_rtt)); rely (negb (gidx_rd =? gidx_rec_list)); rely (negb (gidx_rtt =? gidx_rec_list));
    let grd := (gs (share adt)) @ gidx_rd in
    let grtt := (gs (share adt)) @ gidx_rtt in
    let grecl := (gs (share adt)) @ gidx_rec_list in
    rely prop_dec (glock grd = Some CPU_ID);
    rely prop_dec (glock grtt = Some CPU_ID);
    rely prop_dec (glock grecl = Some CPU_ID);
    rely (g_tag (ginfo grd) =? GRANULE_STATE_DELEGATED);
    rely (g_tag (ginfo grtt) =? GRANULE_STATE_DELEGATED);
    rely (g_tag (ginfo grecl) =? GRANULE_STATE_DELEGATED);
    let grtt' := grtt {ginfo: (ginfo grtt) {g_tag: GRANULE_STATE_TABLE} {g_rd: gidx_rd}} in
    let e1 := EVT CPU_ID (REL gidx_rtt grtt') in
    let grecl' := grecl {ginfo: (ginfo grecl) {g_tag: GRANULE_STATE_REC_LIST}} in
    let e2 := EVT CPU_ID (REL gidx_rec_list grecl') in
    rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
    let base := (realm_params (priv adt)) @ 0 in
    let size := (realm_params (priv adt)) @ 1 in
    let algo := (realm_params (priv adt)) @ 4 in
    rely is_int64 base; rely is_int64 size; rely is_int64 (base + size); rely is_int64 algo;
    let grd' := grd {gnorm: (gnorm grd) {g_realm_state: REALM_STATE_NEW} {g_par_base: base}
                                        {g_par_end: base + size} {g_rtt: gidx_rtt} {g_rec_list: gidx_rec_list}
                                        {g_measurement_algo: if algo =? MEASUREMENT_ALGO_SHA256 then
                                                              MEASUREMENT_ALGO_SHA256 else MEASUREMENT_ALGO_ZERO}
                                        {g_measurement_ctx: if algo =? MEASUREMENT_ALGO_SHA256 then measure_start
                                                            else (g_measurement_ctx (gnorm grd))}}
                    {ginfo: (ginfo grd) {g_tag: GRANULE_STATE_RD}} in
    let e3 := EVT CPU_ID (REL gidx_rd grd') in
    Some adt {log: e3 :: e2 :: e1 :: (log adt)}
         {share: (share adt) {gs: (gs (share adt)) # gidx_rd == (grd' {glock: None} {gtype: GRANULE_STATE_RD})
                                                   # gidx_rec_list == (grecl' {glock: None} {gtype: GRANULE_STATE_REC_LIST})
                                                   # gidx_rtt == (grtt' {glock: None} {gtype: GRANULE_STATE_TABLE})}}.

End Spec.
