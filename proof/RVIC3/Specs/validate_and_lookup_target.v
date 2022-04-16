Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RVIC2.Spec.
Require Import RVIC.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition validate_and_lookup_target_spec (rec: Pointer) (target: Z64) (intid: Z64) (adt: RData) : option (RData * Z64) :=
    match target, intid with
    | VZ64 target, VZ64 intid =>
      rely is_int64 target; rely is_int64 intid;
      if Z.land target 18446742978476113920 =? 0 then
        if ((intid >=? 0) && (intid <=? 31)) || ((intid >=? 32) && (intid <=? 511)) then
          rely (peq (base rec) buffer_loc);
          when gidx == ((buffer (priv adt)) @ (offset rec));
          rely is_gidx gidx;
          let gn := (gs (share adt)) @ gidx in
          rely gtype gn =? GRANULE_STATE_REC;
          rely g_inited (gro gn);
          let idx1 := __mpidr_to_rec_idx target in
          let idx2 := g_rec_idx (gro gn) in
          rely is_int64 idx1; rely is_int64 idx2;
          if idx1 =? idx2 then
            rely (g_rec (gro gn) =? gidx);
            when adt == query_oracle adt;
            let gn := (gs (share adt)) @ gidx in
            rely prop_dec (glock gn = None);
            let g' := gn {glock: Some CPU_ID} in
            Some (adt {log: (EVT CPU_ID (ACQ gidx)) :: log adt} {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
                      {priv: (priv adt) {buffer: (buffer (priv adt)) # SLOT_REC_TARGET == (Some gidx)} {target_rec: SLOT_REC_TARGET}},
                  VZ64 0)
          else
            rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
            rely (ref_accessible gn CPU_ID);
            let rd_gidx := g_rec_rd (grec gn) in
            let recl_gidx := g_rec_rec_list (grec gn) in
            rely is_gidx rd_gidx; rely is_gidx recl_gidx;
            rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
              when adt == (query_oracle adt);
              let adt := adt {log: EVT CPU_ID (RECL recl_gidx idx1 GET_RECL) :: log adt} in
              let grecl := (gs (share adt)) @ recl_gidx in
              rely (gtype grecl =? GRANULE_STATE_REC_LIST);
              let g_rec_gidx := (g_data (gnorm grecl)) @ idx1 in
              if g_rec_gidx =? 0 then
                Some (adt {priv: (priv adt) {target_rec: 0}}, VZ64 1)
              else
                rely is_gidx g_rec_gidx;
                when adt == query_oracle adt;
                let e := EVT CPU_ID (ACQ g_rec_gidx) in
                let adt := adt {log: e :: log adt} in
                let gn_target := (gs (share adt)) @ g_rec_gidx in
                rely prop_dec (glock gn_target = None);
                let gn_target := gn_target {glock: Some CPU_ID} in
                rely is_int (g_tag (ginfo gn_target));
                rely is_gidx (g_rd (ginfo gn_target));
                if g_tag (ginfo gn_target) =? GRANULE_STATE_REC then
                  if g_rd (ginfo gn_target) =? rd_gidx then
                    let adt := adt {share: (share adt) {gs: (gs (share adt)) # g_rec_gidx == gn_target}} in
                    when adt == query_oracle adt;
                    let gn_target := (gs (share adt)) @ g_rec_gidx in
                    rely (gtype gn_target =? g_tag (ginfo gn_target));
                    let e := EVT CPU_ID (RECL recl_gidx idx1 GET_RECL) in
                    rely (gtype ((gs (share adt)) @ recl_gidx) =? GRANULE_STATE_REC_LIST);
                    let g_rec_gidx' := (g_data (gnorm ((gs (share adt)) @ recl_gidx))) @ idx1 in
                    rely is_int g_rec_gidx';
                    if g_rec_gidx =? g_rec_gidx' then
                      Some (adt {log: e :: log adt}
                                {priv: (priv adt) {buffer: (buffer (priv adt)) # SLOT_REC_TARGET == (Some g_rec_gidx)}
                                                  {target_rec: SLOT_REC_TARGET}},
                            VZ64 0)
                    else
                      let e' := EVT CPU_ID (REL g_rec_gidx gn_target) in
                      Some (adt {share: (share adt) {gs: (gs (share adt)) # g_rec_gidx == (gn_target {glock: None})}}
                                {log: e' :: e :: log adt} {priv: (priv adt) {target_rec: 0}}, VZ64 1)
                  else
                    rely (gtype gn_target =? g_tag (ginfo gn_target));
                    Some (adt {log: EVT CPU_ID (REL g_rec_gidx gn_target) :: log adt}
                              {priv: (priv adt) {target_rec: 0}}, VZ64 1)
                else
                  rely (gtype gn_target =? g_tag (ginfo gn_target));
                  Some (adt {log: EVT CPU_ID (REL g_rec_gidx gn_target) :: log adt}
                            {priv: (priv adt) {target_rec: 0}}, VZ64 1)
        else Some (adt, (VZ64 1))
      else Some (adt, (VZ64 1))
    end.

End Spec.

