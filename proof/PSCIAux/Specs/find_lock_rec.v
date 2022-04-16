Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition find_lock_rec_spec (g_rd': Pointer) (rec_list: Pointer) (rec_idx: Z64) (adt: RData) : option (RData * Pointer) :=
    match rec_idx with
    | VZ64 rec_idx =>
      rely is_int64 rec_idx;
      rely (peq (base rec_list) buffer_loc);
      when gidx == ((buffer (priv adt)) @ (offset rec_list));
      when adt == (query_oracle adt);
      let adt := adt {log: EVT CPU_ID (RECL gidx rec_idx GET_RECL) :: log adt} in
      let grecl := (gs (share adt)) @ gidx in
      rely (gtype grecl =? GRANULE_STATE_REC_LIST);
      let g_rec_gidx := (g_data (gnorm grecl)) @ rec_idx in
      if g_rec_gidx =? 0 then
        Some (adt, NULL)
      else
        rely is_gidx g_rec_gidx;
        when adt == query_oracle adt;
        let e := EVT CPU_ID (ACQ g_rec_gidx) in
        let adt := adt {log: e :: log adt} in
        let gn := (gs (share adt)) @ g_rec_gidx in
        rely prop_dec (glock gn = None);
        rely is_gidx (g_rd (ginfo gn));
        let gn := gn {glock: Some CPU_ID} in
        rely is_int (g_tag (ginfo gn));
        if g_tag (ginfo gn) =? GRANULE_STATE_REC then
          if ptr_eq (ginfo_loc, (g_rd (ginfo gn))) g_rd' then
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
            rely (gtype gn =? g_tag (ginfo gn));
            let e := EVT CPU_ID (REL g_rec_gidx gn) in
            Some (adt {log: e :: log adt}, NULL)
        else
          rely (gtype gn =? g_tag (ginfo gn));
          let e := EVT CPU_ID (REL g_rec_gidx gn) in
          Some (adt {log: e :: log adt}, NULL)
    end.

End Spec.

