Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_lookup_target_spec (rec: Pointer) (target: Z64) (adt: RData) : option (RData * Pointer) :=
    match target with
    | VZ64 target =>
      rely is_int64 target;
      if __mpidr_is_valid target then
        rely (peq (base rec) buffer_loc);
        when rec_gidx == ((buffer (priv adt)) @ (offset rec));
        let gn_rec := (gs (share adt)) @ rec_gidx in
        rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
        rely (ref_accessible gn_rec CPU_ID);
        let rd_gidx := g_rec_rd (grec gn_rec) in
        let gidx := g_rec_rec_list (grec gn_rec) in
        rely is_gidx gidx; rely is_gidx rd_gidx;
        rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
        let rec_idx := __mpidr_to_rec_idx target in
        rely is_int64 rec_idx;
        when adt == (query_oracle adt);
        let adt := adt {log:  EVT CPU_ID (RECL gidx rec_idx GET_RECL) :: log adt} in
        let grecl := (gs (share adt)) @ gidx in
        rely (gtype grecl =? GRANULE_STATE_REC_LIST);
        let g_rec_gidx := (g_data (gnorm ((gs (share adt)) @ gidx))) @ rec_idx in
        if g_rec_gidx =? 0 then
          Some (adt, NULL)
        else
          rely is_gidx g_rec_gidx;
          when adt == query_oracle adt;
          let adt := adt {log: EVT CPU_ID (ACQ g_rec_gidx) :: log adt} in
          let gn := (gs (share adt)) @ g_rec_gidx in
          rely prop_dec (glock gn = None);
          let gn := gn {glock: Some CPU_ID} in
          rely is_int (g_tag (ginfo gn));
          rely (gtype gn =? g_tag (ginfo gn));
          rely is_gidx (g_rd (ginfo gn));
          if g_tag (ginfo gn) =? GRANULE_STATE_REC then
            if (g_rd (ginfo gn)) =? rd_gidx then
              let adt := adt {share: (share adt) {gs: (gs (share adt)) # g_rec_gidx == gn}} in
              when adt == query_oracle adt;
              let gn := (gs (share adt)) @ g_rec_gidx in
              rely (gtype gn =? g_tag (ginfo gn));
              let e := EVT CPU_ID (RECL gidx rec_idx GET_RECL) in
              rely (gtype ((gs (share adt)) @ gidx) =? GRANULE_STATE_REC_LIST);
              let g_rec_gidx' := (g_data (gnorm ((gs (share adt)) @ gidx))) @ rec_idx in
              rely is_int g_rec_gidx';
              if g_rec_gidx =? g_rec_gidx' then
                Some (adt {log: e :: log adt}, (ginfo_loc, g_rec_gidx))
              else
                let e' := EVT CPU_ID (REL g_rec_gidx gn) in
                Some (adt {share: (share adt) {gs: (gs (share adt)) # g_rec_gidx == (gn {glock: None})}}
                          {log: e' :: e :: log adt},
                      NULL)
            else
              let e := EVT CPU_ID (REL g_rec_gidx gn) in
              Some (adt {log: e :: log adt}, NULL)
          else
            let e := EVT CPU_ID (REL g_rec_gidx gn) in
            Some (adt {log: e :: log adt}, NULL)
      else Some (adt, NULL)
    end.

End Spec.

