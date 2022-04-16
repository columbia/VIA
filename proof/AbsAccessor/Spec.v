Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope Z_scope.

Section Spec.

  Definition assert_cond_spec (b: Z) (adt: RData) : option RData :=
    if b =? 0 then None else Some adt.

  Definition null_ptr_spec  (adt: RData) : option Pointer :=
    Some NULL.

  Definition is_null_spec (ptr: Pointer) (adt: RData) : option Z :=
    if ptr_eq ptr NULL then Some 1 else Some 0.

  Definition ptr_eq_spec (p1: Pointer) (p2: Pointer) (adt: RData) : option Z :=
    if ptr_eq p1 p2 then Some 1 else Some 0.

  Definition ptr_is_err_spec (ptr: Pointer) (adt: RData) : option Z :=
    if peq (fst ptr) error_loc then
      Some 1
    else
      Some 0.

  Definition shiftl_spec (a: Z64) (s: Z64) (adt: RData) : option Z64 :=
    match a, s with
    | VZ64 a, VZ64 s =>
      rely is_int64 (Z.shiftl a s);
      Some (VZ64 (Z.shiftl a s))
    end.

  Definition granule_lock_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    when adt == query_oracle adt;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = None);
    let e := EVT CPU_ID (ACQ gidx) in
    Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {glock: Some CPU_ID})}}.

  Definition granule_unlock_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let e := EVT CPU_ID (REL gidx gn) in
    Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {glock: None} {gtype: (g_tag (ginfo gn))})}}.

  Definition granule_addr_spec (g: Pointer) (adt: RData) : option Z64 :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    Some (VZ64 (__gidx_to_addr gidx)).

  Definition addr_to_granule_spec (addr: Z64) (adt: RData) : option Pointer :=
    match addr with
    | VZ64 addr =>
      rely (GRANULE_ALIGNED addr);
      let gidx := __addr_to_gidx addr in
      rely is_gidx gidx;
      Some (ginfo_loc, gidx)
    end.

  Definition find_granule_spec (addr: Z64) (adt: RData) : option Pointer :=
    match addr with
    | VZ64 addr =>
      if GRANULE_ALIGNED addr then
        let gidx := __addr_to_gidx addr in
        if is_gidx gidx then
          Some (ginfo_loc, gidx)
        else
          Some NULL
      else
        Some NULL
    end.

  Definition find_lock_granule_spec (addr: Z64) (expected_state: Z64) (adt: RData) : option (RData * Pointer) :=
    match addr, expected_state with
    | VZ64 addr, VZ64 expected_state =>
      let gidx := __addr_to_gidx addr in
      match GRANULE_ALIGNED addr, is_gidx gidx with
      | true, true =>
        when adt == query_oracle adt;
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = None);
        if g_tag (ginfo gn) =? expected_state then
          let e := EVT CPU_ID (ACQ gidx) in
          let st' := (share adt) {gs: (gs (share adt)) # gidx == (gn {glock: Some CPU_ID})} in
          Some (adt {log: e :: (log adt)} {share: st'}, (ginfo_loc, gidx))
        else
          let e := EVT CPU_ID (ACQ gidx) in
          let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
          let st' := (share adt) {gs: (gs (share adt)) # gidx == gn} in
          Some (adt {log: e' :: e :: (log adt)} {share: st'}, NULL)
      | _, _ => Some (adt, NULL)
      end
    end.

  Definition find_lock_unused_granule_spec (addr: Z64) (expected_state: Z64) (adt: RData) : option (RData * Pointer) :=
    match addr, expected_state with
    | VZ64 addr, VZ64 expected_state =>
      let gidx := __addr_to_gidx addr in
      match GRANULE_ALIGNED addr, is_gidx gidx with
      | true, true =>
        let lo := oracle adt (log adt) in
        when st == repl adt lo (share adt);
        let gn := (gs st) @ gidx in
        rely prop_dec (glock gn = None);
        match g_tag (ginfo gn) =? expected_state, gcnt gn =? 0 with
        | true, true =>
          let e := EVT CPU_ID (ACQ gidx) in
          let st' := st {gs: (gs st) # gidx == (gn {glock: Some CPU_ID})} in
          Some (adt {log: e :: lo ++ (log adt)} {share: st'}, (ginfo_loc, gidx))
        | _, _ =>
          let e := EVT CPU_ID (ACQ gidx) in
          let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
          let st' := st {gs: (gs st) # gidx == gn} in
          Some (adt {log: e' :: e :: lo ++ (log adt)} {share: st'}, NULL)
        end
      | _, _ => Some (adt, NULL)
      end
    end.

  Definition find_lock_three_delegated_granules_spec (addr1: Z64) (addr2: Z64) (addr3: Z64) (adt: RData) : option (RData * Z) :=
    match addr1, addr2, addr3 with
    | VZ64 addr1, VZ64 addr2, VZ64 addr3 =>
      if (negb (addr1 =? addr2)) && (negb (addr1 =? addr3)) && (negb (addr2 =? addr3)) &&
         (GRANULE_ALIGNED addr1) && (GRANULE_ALIGNED addr2) && (GRANULE_ALIGNED addr3)
      then
        let gidx1 := __addr_to_gidx addr1 in
        let gidx2 := __addr_to_gidx addr2 in
        let gidx3 := __addr_to_gidx addr3 in
        when adt == query_oracle adt;
        let st := share adt in
        let gn1 := (gs st) @ gidx1 in
        let gn2 := (gs st) @ gidx2 in
        let gn3 := (gs st) @ gidx3 in
        rely prop_dec (glock gn1 = None);
        rely prop_dec (glock gn2 = None);
        rely prop_dec (glock gn3 = None);
        let e1 := EVT CPU_ID (ACQ gidx1) in
        let e2 := EVT CPU_ID (ACQ gidx2) in
        let e3 := EVT CPU_ID (ACQ gidx3) in
        if (g_tag (ginfo gn1) =? GRANULE_STATE_DELEGATED) &&
          (g_tag (ginfo gn2) =? GRANULE_STATE_DELEGATED) &&
          (g_tag (ginfo gn3) =? GRANULE_STATE_DELEGATED)
        then
          Some (adt {log: e3 :: e2 :: e1 :: (log adt)}
              {priv: (priv adt) {locked_g: (locked_g (priv adt)) # 0 == gidx1 # 1 == gidx2 # 2 == gidx3}}
              {share: st {gs: (gs st) # gidx1 == (gn1 {glock: Some CPU_ID})
                                      # gidx2 == (gn2 {glock: Some CPU_ID})
                                      # gidx3 == (gn3 {glock: Some CPU_ID})}}, 0)
        else
          let e1' := EVT CPU_ID (REL gidx1 (gn1 {glock: Some CPU_ID})) in
          let e2' := EVT CPU_ID (REL gidx2 (gn2 {glock: Some CPU_ID})) in
          let e3' := EVT CPU_ID (REL gidx3 (gn3 {glock: Some CPU_ID})) in
          Some (adt {log: e1' :: e2' :: e3' :: e3 :: e2 :: e1 :: (log adt)}, 1)
      else
        Some (adt, 1)
    end.

  Definition get_locked_granule_spec (index: Z) (adt: RData) : option Pointer :=
    Some (ginfo_loc, (locked_g (priv adt)) @ index).

  Definition granule_get_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {ginfo: (ginfo gn) {g_refcount: (g_refcount (ginfo gn)) + 1}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition granule_put_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    rely g_refcount (ginfo gn) >? 0;
    let g' := gn {ginfo: (ginfo gn) {g_refcount: (g_refcount (ginfo gn)) - 1}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition atomic_granule_get_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let e := EVT CPU_ID (INC_GCNT gidx) in
    Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {gcnt: (gcnt gn) + 1})}}.

  Definition atomic_granule_put_spec (g: Pointer) (adt: RData) : option RData :=
    None.

  Definition atomic_granule_put_release_spec (g: Pointer) (adt: RData) : option RData :=
    let gidx := offset g in
    rely is_gidx gidx;
    rely (peq (base g) ginfo_loc);
    let gn := (gs (share adt)) @ gidx in
    if gtype gn =? GRANULE_STATE_RD then
      rely (gcnt gn >? 0);
      let e := EVT CPU_ID (DEC_RD_GCNT gidx) in
      Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {gcnt: (gcnt gn) - 1})}}
    else
      rely (gcnt gn =? 1);
      rely prop_dec (gref gn = Some CPU_ID);
      let g' := gn {gref: None} {gcnt: 0} in
      let e := EVT CPU_ID (DEC_REC_GCNT gidx gn) in
      Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition granule_get_state_spec (g: Pointer) (adt: RData) : option (RData * Z) :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    Some (adt, g_tag (ginfo gn)).

  Definition granule_set_state_spec (g: Pointer) (state: Z) (adt: RData) : option RData :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {ginfo: (ginfo gn) {g_tag: state}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition granule_map_spec (g: Pointer) (slot: Z) (adt: RData) : option (RData * Pointer) :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let priv' := (priv adt) {buffer: (buffer (priv adt)) # slot == (Some gidx)} in
    Some (adt {priv: priv'}, (buffer_loc, slot)).

  Definition buffer_unmap_spec (buf: Pointer) (adt: RData) : option RData :=
    let slot := offset buf in
    rely (peq (base buf) buffer_loc);
    let priv' := (priv adt) {buffer: (buffer (priv adt)) # slot == None} in
    Some adt {priv: priv'}.

  Definition granule_memzero_spec (g: Pointer) (slot: Z) (adt: RData) : option RData :=
    rely (peq (base g) ginfo_loc);
    let gidx := offset g in
    rely prop_dec ((buffer (priv adt)) @ slot = None);
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition granule_memzero_mapped_spec (g: Pointer) (adt: RData) : option RData :=
    rely (peq (base g) buffer_loc);
    when gidx == ((buffer (priv adt)) @ (offset g));
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

  Definition get_g_data_rd_spec (g: Pointer) (adt: RData) : option Pointer :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    Some (ginfo_loc, g_rd (ginfo gn)).

  Definition get_g_rec_rd_spec (g: Pointer) (adt: RData) : option Pointer :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    Some (ginfo_loc, g_rd (ginfo gn)).

  Definition get_rec_g_rec_list_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (ginfo_loc, g_rec_rec_list (grec gn))
    | _ => None
    end.

  Definition get_g_rtt_refcount_spec (g: Pointer) (adt: RData) : option (RData * Z64) :=
    let gidx := offset g in
    rely (peq (base g) ginfo_loc);
    rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    Some (adt, VZ64 (g_refcount (ginfo gn))).

  Definition set_g_rec_rd_spec (g_rec: Pointer) (g_rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base g_rec) ginfo_loc);
    let gidx_rec := offset g_rec in
    rely is_gidx gidx_rec;
    let gn := (gs (share adt)) @ gidx_rec in
    rely prop_dec (glock gn = Some CPU_ID);
    if peq (base g_rd) ginfo_loc then
      let g' := gn {ginfo: (ginfo gn) {g_rd: offset g_rd}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx_rec == g'}}
    else
      if peq (base g_rd) null_loc then
        let g' := gn {ginfo: (ginfo gn) {g_rd: 0}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx_rec == g'}}
      else None.

  Definition set_g_rtt_rd_spec (g_rtt: Pointer) (g_rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base g_rtt) ginfo_loc);
    let gidx_rtt := offset g_rtt in
    rely is_gidx gidx_rtt;
    let gn := (gs (share adt)) @ gidx_rtt in
    rely prop_dec (glock gn = Some CPU_ID);
    if peq (base g_rd) ginfo_loc then
      let g' := gn {ginfo: (ginfo gn) {g_rd: offset g_rd}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx_rtt == g'}}
    else
      if peq (base g_rd) null_loc then
        let g' := gn {ginfo: (ginfo gn) {g_rd: 0}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx_rtt == g'}}
      else None.

  Definition get_rd_g_rtt_spec (rd: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (ginfo_loc, g_rtt (gnorm gn))
    | _ => None
    end.

  Definition get_rd_g_rec_list_spec (rd: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (ginfo_loc, g_rec_list (gnorm gn))
    | _ => None
    end.

  Definition get_rd_state_spec (rd: Pointer) (adt: RData) : option Z :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (g_realm_state (gnorm gn))
    | _ => None
    end.

  Definition get_rd_par_base_spec (rd: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (VZ64 (g_par_base (gnorm gn)))
    | _ => None
    end.

  Definition get_rd_par_end_spec (rd: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (VZ64 (g_par_end (gnorm gn)))
    | _ => None
    end.

  Definition get_rd_measurement_spec (rd: Pointer) (idx: Z) (adt: RData) : option Z64 :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      Some (VZ64 (g_measurement (gnorm gn)))
    | _ => None
    end.

  Definition set_rd_measurement_algo_spec (rd: Pointer) (algo: Z64) (adt: RData) : option RData :=
    match algo with
    | VZ64 algo =>
      rely (peq (base rd) buffer_loc);
      match (buffer (priv adt)) @ (offset rd) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
        let g' := gn {gnorm: (gnorm gn) {g_measurement_algo: algo}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rd_state_spec (rd: Pointer) (state: Z) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      let g' := gn {gnorm: (gnorm gn) {g_realm_state: state}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rd_par_base_spec (rd: Pointer) (par_base: Z64) (adt: RData) : option RData :=
    match par_base with
    | VZ64 par_base =>
      rely (peq (base rd) buffer_loc);
      match (buffer (priv adt)) @ (offset rd) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
        let g' := gn {gnorm: (gnorm gn) {g_par_base: par_base}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rd_par_end_spec (rd: Pointer) (par_end: Z64) (adt: RData) : option RData :=
    match par_end with
    | VZ64 par_end =>
      rely (peq (base rd) buffer_loc);
      match (buffer (priv adt)) @ (offset rd) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
        let g' := gn {gnorm: (gnorm gn) {g_par_end: par_end}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rd_g_rtt_spec (rd: Pointer) (g_rtt: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base g_rtt) ginfo_loc);
    let rtt_gidx := offset g_rtt in
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      let g' := gn {gnorm: (gnorm gn) {g_rtt: rtt_gidx}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rd_g_rec_list_spec (rd: Pointer) (g_rec_list: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base g_rec_list) ginfo_loc);
    let rec_list_gidx := offset g_rec_list in
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_RD;
      let g' := gn {gnorm: (gnorm gn) {g_rec_list: rec_list_gidx}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition get_rec_params_flags_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rec_params (priv adt)) @ 9).

  Definition get_rec_rec_idx_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely gtype gn =? GRANULE_STATE_REC;
      rely g_inited (gro gn);
      Some (VZ64 (g_rec_idx (gro gn)))
    | _ => None
    end.

  Definition get_rec_dispose_pending_spec (rec: Pointer) (adt: RData) : option Z :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (g_dispose_pending (grec gn))
    | _ => None
    end.

  Definition get_rec_pc_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (g_pc (grec gn)))
    | _ => None
    end.

  Definition get_rec_pstate_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (g_pstate (grec gn)))
    | _ => None
    end.

  Definition get_rec_last_run_info_esr_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (g_esr (grec gn)))
    | _ => None
    end.

  Definition init_rec_read_only_spec (rec: Pointer) (grec: Pointer) (rec_idx: Z64) (adt: RData) : option RData :=
    match rec_idx with
    | VZ64 rec_idx =>
      rely (peq (base rec) buffer_loc);
      rely (peq (base grec) ginfo_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely gtype gn =? GRANULE_STATE_DELEGATED;
        rely (negb (g_inited (gro gn)));
        let g' := gn {gro: mkRecReadOnly true (offset grec) rec_idx} in
        let e := EVT CPU_ID (INIT_RO gidx (offset grec) rec_idx) in
        Some (adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == g'}})
      | _ => None
      end
    end.

  Definition set_rec_g_rd_spec (rec: Pointer) (g_rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    rely (peq (base g_rd) ginfo_loc);
    let rd_gidx := offset g_rd in
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (ref_accessible gn CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      let g' := gn {grec: (grec gn) {g_rec_rd: rd_gidx}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_g_rec_list_spec (rec: Pointer) (g_rec_list: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    rely (peq (base g_rec_list) ginfo_loc);
    let rec_list_gidx := offset g_rec_list in
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (ref_accessible gn CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      let g' := gn {grec: (grec gn) {g_rec_rec_list: rec_list_gidx}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_par_base_spec (rec: Pointer) (par_base: Z64) (adt: RData) : option RData :=
    match par_base with
    | VZ64 par_base =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_rec_par_base: par_base}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_par_end_spec (rec: Pointer) (par_end: Z64) (adt: RData) : option RData :=
    match par_end with
    | VZ64 par_end =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_rec_par_base: par_end}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition get_rec_runnable_spec (rec: Pointer) (adt: RData) : option Z :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      Some (g_runnable (gnorm gn))
    | _ => None
    end.

  Definition set_rec_runnable_spec (rec: Pointer) (val: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      let g' := gn {gnorm: (gnorm gn) {g_runnable: val}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_regs_spec (rec: Pointer) (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_regs: set_reg reg val (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_pc_spec (rec: Pointer) (pc: Z64) (adt: RData) : option RData :=
    match pc with
    | VZ64 pc =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_pc: pc}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_pstate_spec (rec: Pointer) (pstate: Z64) (adt: RData) : option RData :=
    match pstate with
    | VZ64 pstate =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_pstate: pstate}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rvic_mask_bits_spec (rvic: Pointer) (i: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely (peq (base rvic) rvic_loc);
      match (buffer (priv adt)) @ (offset rvic) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        rely prop_dec (glock gn = Some CPU_ID);
        let g' := gn {gnorm: (gnorm gn)
                       {g_rvic: (g_rvic (gnorm gn))
                                  {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn)))  # i == val}}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_sysregs_spec (rec: Pointer) (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_regs: set_reg reg val (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_common_sysregs_spec (rec: Pointer) (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_regs: set_reg reg val (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_dispose_pending_spec (rec: Pointer) (pending: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (ref_accessible gn CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      let g' := gn {grec: (grec gn) {g_dispose_pending: pending}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_last_run_info_esr_spec (rec: Pointer) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_esr: val}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition get_rec_run_gprs_spec (reg: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (rec_run (priv adt)) @ (5 + reg)).

  Definition get_rec_run_is_emulated_mmio_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rec_run (priv adt)) @ 13).

  Definition get_rec_run_emulated_read_val_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rec_run (priv adt)) @ 14).

  Definition pgte_read_spec (table: Pointer) (idx: Z64) (adt: RData) : option Z64 :=
    match idx with
    | VZ64 idx =>
      rely (peq (base table) buffer_loc);
      match (buffer (priv adt)) @ (offset table) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
        Some (VZ64 ((g_data (gnorm gn)) @ idx))
      | _ => None
      end
    end.

  Definition pgte_write_spec (table: Pointer) (idx: Z64) (val: Z64) (adt: RData) : option RData :=
    match idx, val with
    | VZ64 idx, VZ64 val =>
      rely (peq (base table) buffer_loc);
      match (buffer (priv adt)) @ (offset table) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
        let g' := gn {gnorm: (gnorm gn) {g_data: (g_data (gnorm gn)) # idx == val}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition link_table_spec (parent: Pointer) (child: Pointer) (level: Z64) (index: Z64) (adt: RData) : option RData :=
    match level, index with
    | VZ64 level, VZ64 index =>
      rely (peq (base parent) ginfo_loc);
      rely (peq (base child) ginfo_loc);
      let par_gidx := offset parent in
      let ch_gidx := offset child in
      let ch := (gs (share adt)) @ ch_gidx in
      rely prop_dec (glock ch = Some CPU_ID);
      let ch' := ch {gaux: mkAuxillaryVars level index par_gidx} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # ch_gidx == ch'}}
    end.

  Definition set_mapping_spec (map_addr: Z64) (data_addr: Z64) (adt: RData) : option RData :=
    match map_addr, data_addr with
    | VZ64 map_addr, VZ64 data_addr =>
      let gidx := __addr_to_gidx data_addr in
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      let g' := gn {gaux: mkAuxillaryVars 0 0 map_addr} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

  Definition set_retval_spec (retval: Z64) (adt: RData) : option RData :=
    match retval with
    | VZ64 retval =>
      Some adt {priv: (priv adt) {retval: retval}}
    end.

  Definition realm_get_rec_entry_spec (rec_idx: Z64) (rec_list: Pointer) (adt: RData) : option (RData * Pointer) :=
    match rec_idx with
    | VZ64 rec_idx =>
      rely (peq (base rec_list) buffer_loc);
      match (buffer (priv adt)) @ (offset rec_list) with
      | Some gidx =>
        when adt == query_oracle adt;
        let st := share adt in
        let gn := (gs st) @ gidx in
        rely (gtype gn =? GRANULE_STATE_REC_LIST);
        let e := EVT CPU_ID (RECL gidx rec_idx GET_RECL) in
        let rec_gidx := (g_data (gnorm gn)) @ rec_idx in
        if rec_gidx =? 0 then
          Some (adt {log: e :: (log adt)}, NULL)
        else
          Some (adt {log: e :: (log adt)}, (ginfo_loc, rec_gidx))
      | _ => None
      end
    end.

  Definition realm_set_rec_entry_spec (rec_idx: Z64) (rec_list: Pointer) (g_rec: Pointer) (adt: RData) : option RData :=
    match rec_idx with
    | VZ64 rec_idx =>
      rely (peq (base rec_list) buffer_loc);
      match (buffer (priv adt)) @ (offset rec_list) with
      | Some gidx =>
        let st := share adt in
        let gn := (gs st) @ gidx in
        rely (gtype gn =? GRANULE_STATE_REC_LIST);
        if peq (base g_rec) ginfo_loc then
          let rec_gidx := offset g_rec in
          let e := EVT CPU_ID (RECL gidx rec_idx (SET_RECL rec_gidx)) in
          let g' := gn {gnorm: (gnorm gn) {g_data: (g_data (gnorm gn)) # rec_idx == rec_gidx}} in
          Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
        else
          if peq (base g_rec) null_loc then
            let e := EVT CPU_ID (RECL gidx rec_idx UNSET_RECL) in
            let g' := gn {gnorm: (gnorm gn) {g_data: (g_data (gnorm gn)) # rec_idx == 0}} in
            Some adt {log: e :: (log adt)} {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
          else None
      | _ => None
      end
    end.

  Definition get_wi_g_llt_spec  (adt: RData) : option Pointer :=
    if (wi_llt (priv adt)) =? 0 then
      Some NULL
    else
      Some (ginfo_loc, (wi_llt (priv adt))).

  Definition get_wi_index_spec  (adt: RData) : option Z64 :=
      Some (VZ64 (wi_index (priv adt))).

  Definition set_wi_last_level_spec (last_level: Z64) (adt: RData) : option RData :=
    match last_level with
    | VZ64 last_level =>
      Some adt {priv: (priv adt) {wi_last_level: last_level}}
    end.

  Definition set_wi_g_llt_spec (g_llt: Pointer) (adt: RData) : option RData :=
    if peq (base g_llt) ginfo_loc then
      Some adt {priv: (priv adt) {wi_llt: offset g_llt}}
    else
      if peq (base g_llt) null_loc then
        Some adt {priv: (priv adt) {wi_llt: 0}}
      else None.

  Definition set_wi_index_spec (index: Z64) (adt: RData) : option RData :=
    match index with
    | VZ64 index =>
      Some adt {priv: (priv adt) {wi_index: index}}
    end.

  Definition get_realm_params_par_base_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (realm_params (priv adt)) @ 0).

  Definition get_realm_params_par_size_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (realm_params (priv adt)) @ 1).

  Definition get_realm_params_rtt_addr_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (realm_params (priv adt)) @ 3).

  Definition get_realm_params_rec_list_addr_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (realm_params (priv adt)) @ 2).

  Definition get_realm_params_measurement_algo_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (realm_params (priv adt)) @ 4).

  Definition get_rec_params_gprs_spec (idx: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (rec_params (priv adt)) @ idx).

  Definition get_rec_params_pc_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rec_params (priv adt)) @ 8).

  Definition is_addr_in_par_spec (rd: Pointer) (addr: Z64) (adt: RData) : option Z :=
    None.

  Definition mpidr_is_valid_spec (mpidr: Z64) (adt: RData) : option Z :=
    match mpidr with
    | VZ64 mpidr =>
      Some (if __mpidr_is_valid mpidr then 1 else 0)
    end.

  Definition mpidr_to_rec_idx_spec (mpidr: Z64) (adt: RData) : option Z64 :=
    match mpidr with
    | VZ64 mpidr =>
      Some (VZ64 (__mpidr_to_rec_idx mpidr))
    end.

  Definition addr_to_idx_spec (addr: Z64) (level: Z64) (adt: RData) : option Z64 :=
    match addr, level with
    | VZ64 addr, VZ64 level =>
      Some (VZ64 (__addr_to_idx addr level))
    end.

  Definition entry_is_table_spec (entry: Z64) (adt: RData) : option Z :=
    match entry with
    | VZ64 entry =>
      if __entry_is_table entry then Some 1 else Some 0
    end.

  Definition is_rec_valid_spec (rec_idx: Z64) (rec_list: Pointer) (adt: RData) : option (RData * Z) :=
    match rec_idx with
    | VZ64 rec_idx =>
      rely (peq (base rec_list) buffer_loc);
      match (buffer (priv adt)) @ (offset rec_list) with
      | Some gidx =>
        let st := share adt in
        let gn := (gs st) @ gidx in
        rely (gtype gn =? GRANULE_STATE_REC_LIST);
        let rec_gidx := (g_data (gnorm gn)) @ rec_idx in
        if rec_gidx =? 0 then
          Some (adt, 1)
        else
          Some (adt, 0)
      | _ => None
      end
    end.

  Definition esr_srt_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr => Some (__esr_srt esr)
    end.

  Definition access_mask_spec (esr: Z64) (adt: RData) : option Z64 :=
    match esr with
    | VZ64 esr => Some (VZ64 (__access_mask esr))
    end.

  Definition esr_sign_extend_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr => Some (__esr_sign_extend esr)
    end.

  Definition access_len_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr => Some (__access_len esr)
    end.

  Definition esr_sixty_four_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr => if __esr_sixty_four esr then Some 1 else Some 0
    end.

  Definition get_rec_regs_spec (rec: Pointer) (reg: Z) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (get_reg reg (g_regs (grec gn))))
    | _ => None
    end.

  Definition get_rec_par_base_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (g_rec_par_base (grec gn)))
    | _ => None
    end.

  Definition get_rec_par_end_spec (rec: Pointer) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (g_rec_par_end (grec gn)))
    | _ => None
    end.

  Definition set_rec_dispose_addr_spec (rec: Pointer) (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_dispose_addr: addr}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_dispose_size_spec (rec: Pointer) (size: Z64) (adt: RData) : option RData :=
    match size with
    | VZ64 size =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely (ref_accessible gn CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        let g' := gn {grec: (grec gn) {g_dispose_size: size}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      | _ => None
      end
    end.

  Definition set_rec_run_exit_reason_spec (exit_reason: Z64) (adt: RData) : option RData :=
    match exit_reason with
    | VZ64 ec =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 0 == ec}}
    end.

  Definition set_rec_run_disposed_addr_spec (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 12 == addr}}
    end.

  Definition get_psci_result_x0_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_x0 (priv adt))).

  Definition get_psci_result_x1_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_x1 (priv adt))).

  Definition get_psci_result_x2_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_x2 (priv adt))).

  Definition get_psci_result_x3_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_x3 (priv adt))).

  Definition get_psci_result_forward_x1_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_forward_x1 (priv adt))).

  Definition get_psci_result_forward_x2_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_forward_x2 (priv adt))).

  Definition get_psci_result_forward_x3_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (psci_forward_x3 (priv adt))).

  Definition get_psci_result_forward_psci_call_spec  (adt: RData) : option Z :=
    Some (psci_forward_psci_call (priv adt)).

  Definition set_psci_result_x0_spec (x0': Z64) (adt: RData) : option RData :=
    match x0' with
    | VZ64 x0' =>
      Some adt {priv: (priv adt) {psci_x0: x0'}}
    end.

  Definition set_psci_result_x1_spec (x1': Z64) (adt: RData) : option RData :=
    match x1' with
    | VZ64 x1' =>
      Some adt {priv: (priv adt) {psci_x1: x1'}}
    end.

  Definition set_psci_result_x2_spec (x2': Z64) (adt: RData) : option RData :=
    match x2' with
    | VZ64 x2' =>
      Some adt {priv: (priv adt) {psci_x2: x2'}}
    end.

  Definition set_psci_result_x3_spec (x3': Z64) (adt: RData) : option RData :=
    match x3' with
    | VZ64 x3' =>
      Some adt {priv: (priv adt) {psci_x3: x3'}}
    end.

  Definition set_psci_result_forward_psci_call_spec (b: Z) (adt: RData) : option RData :=
    Some adt {priv: (priv adt) {psci_forward_psci_call: b}}.

  Definition set_psci_result_forward_x1_spec (target_cpu: Z64) (adt: RData) : option RData :=
    match target_cpu with
    | VZ64 target =>
      Some adt {priv: (priv adt) {psci_forward_x1: target}}
    end.

  Definition get_rec_g_rd_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (ginfo_loc, g_rec_rd (grec gn))
    | _ => None
    end.

  Definition get_rec_sysregs_spec (rec: Pointer) (reg: Z) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (get_reg reg (g_regs (grec gn))))
    | _ => None
    end.

  Definition get_rec_common_sysregs_spec (rec: Pointer) (reg: Z) (adt: RData) : option Z64 :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (VZ64 (get_reg reg (g_regs (grec gn))))
    | _ => None
    end.

  Definition get_rvic_pending_bits_spec (rvic: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rvic) rvic_loc);
    Some (rvic_pending_loc, offset rvic).

  Definition get_rvic_mask_bits_spec (rvic: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rvic) rvic_loc);
    Some (rvic_mask_loc, offset rvic).

  Definition atomic_bit_set_release_64_spec (loc: Pointer) (bit: Z) (adt: RData) : option RData :=
    let slot0 := offset loc in
    let idx := Z.shiftr slot0 4 in
    let slot := Z.land slot0 15 in
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      if peq (base loc) rvic_pending_loc then
        let bits := (r_pending_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.lor bits (Z.shiftl 1 bit) in
        let rvic' := (g_rvic (gnorm gn)) {r_pending_bits: (r_pending_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        let bits := (r_mask_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.lor bits (Z.shiftl 1 bit) in
        let rvic' := (g_rvic (gnorm gn)) {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition atomic_bit_clear_release_64_spec (loc: Pointer) (bit: Z) (adt: RData) : option RData :=
    let slot0 := offset loc in
    let idx := Z.shiftr slot0 4 in
    let slot := Z.land slot0 15 in
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      if peq (base loc) rvic_pending_loc then
        let bits := (r_pending_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.land bits (Z.lnot (Z.shiftl 1 bit)) in
        let rvic' := (g_rvic (gnorm gn)) {r_pending_bits: (r_pending_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        let bits := (r_mask_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.land bits (Z.lnot (Z.shiftl 1 bit)) in
        let rvic' := (g_rvic (gnorm gn)) {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition test_bit_acquire_64_spec (loc: Pointer) (bit: Z) (adt: RData) : option Z :=
    let slot0 := offset loc in
    let idx := Z.shiftr slot0 4 in
    let slot := Z.land slot0 15 in
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      if peq (base loc) rvic_pending_loc then
        let bits := (r_pending_bits (g_rvic (gnorm gn))) @ idx in
        if Z.land bits (Z.shiftl 1 bit) =? 0
        then Some 0 else Some 1
      else
        let bits := (r_mask_bits (g_rvic (gnorm gn))) @ idx in
        if Z.land bits (Z.shiftl 1 bit) =? 0
        then Some 0 else Some 1
    | _ => None
    end.

  Definition get_rec_g_rec_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely gtype gn =? GRANULE_STATE_REC;
      rely (g_inited (gro gn));
      Some (ginfo_loc, g_rec (gro gn))
    | _ => None
    end.

  Definition get_rec_rvic_enabled_spec (rec: Pointer) (adt: RData) : option Z :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      Some (r_rvic_enabled (g_rvic (gnorm gn)))
    | _ => None
    end.

  Definition get_rec_rvic_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    Some (rvic_loc, (offset rec)).

  Definition set_rvic_result_x0_spec (x0': Z64) (adt: RData) : option RData :=
    match x0' with
    | VZ64 x0' =>
      Some adt {priv: (priv adt) {rvic_x0: x0'}}
    end.

  Definition set_rvic_result_x1_spec (x1': Z64) (adt: RData) : option RData :=
    match x1' with
    | VZ64 x1' =>
      Some adt {priv: (priv adt) {rvic_x1: x1'}}
    end.

  Definition set_rvic_result_x2_spec (x2': Z64) (adt: RData) : option RData :=
    match x2' with
    | VZ64 x2' =>
      Some adt {priv: (priv adt) {rvic_x2: x2'}}
    end.

  Definition set_rvic_result_x3_spec (x3': Z64) (adt: RData) : option RData :=
    match x3' with
    | VZ64 x3' =>
      Some adt {priv: (priv adt) {rvic_x3: x3'}}
    end.

  Definition get_rvic_result_target_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rvic_target (priv adt))).

  Definition get_rvic_result_ns_notify_spec  (adt: RData) : option Z :=
    Some (rvic_ns_notify (priv adt)).

  Definition set_rvic_result_ns_notify_spec (b: Z) (adt: RData) : option RData :=
    Some adt {priv: (priv adt) {rvic_ns_notify: b}}.

  Definition set_rvic_result_target_spec (target: Z64) (adt: RData) : option RData :=
    match target with
    | VZ64 target =>
      Some adt {priv: (priv adt) {rvic_target: target}}
    end.

  Definition get_rvic_result_x0_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rvic_x0 (priv adt))).

  Definition get_rvic_result_x1_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rvic_x1 (priv adt))).

  Definition get_rvic_result_x2_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rvic_x2 (priv adt))).

  Definition get_rvic_result_x3_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (rvic_x3 (priv adt))).

  Definition get_rvic_pending_bits_i_spec (rvic: Pointer) (i: Z64) (adt: RData) : option Z64 :=
    match i with
    | VZ64 i =>
      rely (peq (base rvic) rvic_loc);
      match (buffer (priv adt)) @ (offset rvic) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        rely prop_dec (glock gn = Some CPU_ID);
        Some (VZ64 (r_pending_bits (g_rvic (gnorm gn))) @ i)
      | _ => None
      end
    end.

  Fixpoint find_next_set_bit_spec (bitmap: Z64) (start: Z64) (adt: RData) : option Z :=
    match bitmap, start with
    | VZ64 bitmap, VZ64 start =>
        rely is_int64 bitmap;
        rely ((0 <=? start) && (start <=? 64));
        let ret := __find_next_set_bit_spec bitmap start in
        Some ret
    end.

  Definition set_rec_rvic_enabled_spec (rec: Pointer) (enabled: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      let g' := gn {gnorm: (gnorm gn) {g_rvic: ((g_rvic (gnorm gn)) {r_rvic_enabled : enabled})}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition resample_timer_signals_spec (rec: Pointer) (intid: Z64) (adt: RData) : option RData :=
    None.

  Definition get_bitmap_loc_spec (bitmap: Pointer) (idx: Z64) (adt: RData) : option Pointer :=
    match idx with
    | VZ64 idx =>
      let slot := offset bitmap in
      rely ((0 <=? slot) && (slot <? 16));
      Some ((base bitmap), (slot + (Z.shiftl idx 4)))
    end.

  Definition interrupt_bitmap_dword_spec (intid: Z64) (adt: RData) : option Z64 :=
    match intid with
    | VZ64 intid =>
      Some (VZ64 (intid / 64))
    end.

  Definition interrupt_bit_spec (intid: Z64) (adt: RData) : option Z64 :=
    match intid with
    | VZ64 intid =>
      Some (VZ64 (intid mod 64))
    end.

  Definition get_target_rec_spec  (adt: RData) : option Pointer :=
    if (target_rec (priv adt)) =? 0 then
      Some NULL
    else
      Some (buffer_loc, (target_rec (priv adt))).

  Definition set_target_rec_spec (rec: Pointer) (adt: RData) : option RData :=
    if peq (base rec) buffer_loc then
      Some adt {priv: (priv adt) {target_rec: offset rec}}
    else if ptr_eq rec NULL then
      Some adt {priv: (priv adt) {target_rec: 0}}
    else None.

  Definition get_rec_vtimer_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    Some (vtimer_loc, offset rec).

  Definition get_rec_ptimer_spec (rec: Pointer) (adt: RData) : option Pointer :=
    rely (peq (base rec) buffer_loc);
    Some (ptimer_loc, offset rec).

  Definition get_timer_asserted_spec (timer: Pointer) (adt: RData) : option Z :=
    match (buffer (priv adt)) @ (offset timer) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      if peq (base timer) ptimer_loc then
        Some (t_asserted (g_ptimer (grec gn)))
      else
        if peq (base timer) vtimer_loc then
          Some (t_asserted (g_vtimer (grec gn)))
        else None
    | _ => None
    end.

  Definition get_timer_masked_spec (timer: Pointer) (adt: RData) : option Z :=
    match (buffer (priv adt)) @ (offset timer) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      if peq (base timer) ptimer_loc then
        Some (t_masked (g_ptimer (grec gn)))
      else
        if peq (base timer) vtimer_loc then
          Some (t_masked (g_vtimer (grec gn)))
        else None
    | _ => None
    end.

  Definition set_timer_masked_spec (timer: Pointer) (masked: Z) (adt: RData) : option RData :=
    match (buffer (priv adt)) @ (offset timer) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      if peq (base timer) ptimer_loc then
        let g' := gn {grec: (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_masked: masked}}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        if peq (base timer) vtimer_loc then
          let g' := gn {grec: (grec gn) {g_vtimer: (g_vtimer (grec gn)) {t_masked: masked}}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
        else None
    | _ => None
    end.

  Definition emulate_timer_ctl_read_spec (timer: Pointer) (cntx_ctl: Z64) (adt: RData) : option Z64 :=
    match (buffer (priv adt)) @ (offset timer), cntx_ctl with
    | Some gidx, VZ64 cntx_ctl =>
      let cntx_ctl := Z.land cntx_ctl NOT_CNTx_CTL_IMASK in
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      if peq (base timer) ptimer_loc then
        if t_masked (g_ptimer (grec gn)) =? 1 then
          Some (VZ64 (Z.lor cntx_ctl CNTx_CTL_IMASK))
        else
          Some (VZ64 cntx_ctl)
      else
        if peq (base timer) vtimer_loc then
          if t_masked (g_vtimer (grec gn)) =? 1 then
            Some (VZ64 (Z.lor cntx_ctl CNTx_CTL_IMASK))
          else
            Some (VZ64 cntx_ctl)
        else None
    | _, _ => None
    end.

  Definition __timer_condition_met cntx_ctl :=
    if ((Z.land cntx_ctl 1) =? 1) && (Z.land cntx_ctl 4 =? 4) then true else false.

  Definition timer_condition_met_spec (cntx_ctl: Z64) (adt: RData) : option Z :=
    match cntx_ctl with
    | VZ64 cntx_ctl =>
      if __timer_condition_met cntx_ctl then Some 1 else Some 0
    end.

  Definition timer_is_masked_spec (cntx_ctl: Z64) (adt: RData) : option Z :=
    match cntx_ctl with
    | VZ64 cntx_ctl =>
      if (Z.land cntx_ctl 2) =? 2 then Some 1
      else Some 0
    end.

  Definition sysreg_read_spec (reg: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (get_reg reg (cpu_regs (priv adt)))).

  Definition sysreg_write_spec (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {cpu_regs: set_reg reg val (cpu_regs (priv adt))}}
    end.

  Definition set_rec_vtimer_asserted_spec (rec: Pointer) (asserted: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let g' := gn {grec: (grec gn) {g_vtimer: (g_vtimer (grec gn)) {t_asserted: asserted}}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_ptimer_asserted_spec (rec: Pointer) (asserted: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let g' := gn {grec: (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_asserted: asserted}}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition set_rec_vtimer_masked_spec (rec: Pointer) (masked: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let g' := gn {grec: (grec gn) {g_vtimer: (g_vtimer (grec gn)) {t_masked: masked}}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition get_rec_vtimer_masked_spec (rec: Pointer) (adt: RData) : option Z :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (t_masked (g_vtimer (grec gn)))
    | _ => None
    end.

  Definition set_rec_ptimer_masked_spec (rec: Pointer) (masked: Z) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let g' := gn {grec: (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_masked: masked}}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    | _ => None
    end.

  Definition get_rec_ptimer_masked_spec (rec: Pointer) (adt: RData) : option Z :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      Some (t_masked (g_ptimer (grec gn)))
    | _ => None
    end.

  Definition clear_realm_stage2_spec  (adt: RData) : option RData :=
    let tlb' := fun cpu gidx => if cpu =? CPU_ID then -1 else (tlbs (share adt)) cpu gidx in
    Some adt {share: (share adt) {tlbs: tlb'}}.

  Definition get_ns_state_spec (reg: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (get_reg reg (ns_regs_el2 (priv adt)))).

  Definition set_ns_state_spec (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {ns_regs_el2: set_reg reg val (ns_regs_el2 (priv adt))}}
    end.

  Definition esr_is_write_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr =>
        if __esr_is_write esr then Some 1 else Some 0
    end.

  Definition set_rec_run_esr_spec (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 1 == val}}
    end.

  Definition set_rec_run_far_spec (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 2 == val}}
    end.

  Definition set_rec_run_hpfar_spec (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 3 == val}}
    end.

  Definition set_rec_run_emulated_write_val_spec (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 4 == val}}
    end.

  Definition is_addr_in_par_rec_spec (rec: Pointer) (addr: Z64) (adt: RData) : option Z :=
    match addr with
    | VZ64 addr =>
      rely (peq (base rec) buffer_loc);
      match (buffer (priv adt)) @ (offset rec) with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        rely (ref_accessible gn CPU_ID);
        let par_base := g_rec_par_base (grec gn) in
        let par_end := g_rec_par_end (grec gn) in
        if (par_base <=? addr) && (addr <? par_end) then
          Some 1
        else
          Some 0
      | _ => None
      end
    end.

  Definition set_rec_run_target_rec_spec (target: Z64) (adt: RData) : option RData :=
    match target with
    | VZ64 target =>
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 15 == target}}
    end.

  Definition set_rec_run_gprs_spec (reg: Z) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      rely ((0 <=? reg) && (reg <? 7));
      Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # (5 + reg) == val}}
    end.

  Definition read_idreg_spec (idreg: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (ID_AA64PFR0_EL1 (id_regs (priv adt)))).

  Definition read_reg_spec (reg: Z) (adt: RData) : option Z64 :=
    Some (VZ64 (get_reg reg (cpu_regs (priv adt)))).

  Definition copy_realm_gpregs dst src :=
    dst {r_x0: (r_x0 src)} {r_x1: (r_x1 src)} {r_x2: (r_x2 src)} {r_x3: (r_x3 src)} {r_x4: (r_x4 src)}
        {r_x5: (r_x5 src)} {r_x6: (r_x6 src)} {r_x7: (r_x7 src)} {r_x8: (r_x8 src)} {r_x9: (r_x9 src)}
        {r_x10: (r_x10 src)} {r_x11: (r_x11 src)} {r_x12: (r_x12 src)} {r_x13: (r_x13 src)} {r_x14: (r_x14 src)}
        {r_x15: (r_x15 src)} {r_x16: (r_x16 src)} {r_x17: (r_x17 src)} {r_x18: (r_x18 src)} {r_x19: (r_x19 src)}
        {r_x20: (r_x20 src)} {r_x21: (r_x21 src)} {r_x22: (r_x22 src)} {r_x23: (r_x23 src)} {r_x24: (r_x24 src)}
        {r_x25: (r_x25 src)} {r_x26: (r_x26 src)} {r_x27: (r_x27 src)} {r_x28: (r_x28 src)} {r_x29: (r_x29 src)}
        {r_x30: (r_x30 src)}.

  Definition run_realm_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rec) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let ctxt := g_regs (grec gn) in
      let cregs' := copy_realm_gpregs (cpu_regs (priv adt)) ctxt in
      Some adt {priv: (priv adt) {cpu_regs: cregs'}}
    | _ => None
    end.

  Definition realm_exit_spec  (adt: RData) : option (RData * Z) :=
    match cur_rec (priv adt) with
    | Some slot =>
      match (buffer (priv adt)) @ slot with
      | Some gidx =>
        let gn := (gs (share adt)) @ gidx in
        rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
        rely (ref_accessible gn CPU_ID);
        let ctxt := cpu_regs (priv adt) in
        let gregs' := copy_realm_gpregs (g_regs (grec gn)) ctxt in
        let g' := gn {grec: (grec gn) {g_regs: gregs'}} in
        Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, trap_reason (priv adt))
      | _ => None
      end
    | _ => None
    end.

  Definition get_cur_rec_spec  (adt: RData) : option Pointer :=
    match cur_rec (priv adt) with
    | Some slot =>
      Some (buffer_loc, slot)
    | _ => None
    end.

  Definition get_cur_g_rec_spec  (adt: RData) : option Pointer :=
    match cur_rec (priv adt) with
    | Some slot =>
      match (buffer (priv adt)) @ slot with
      | Some gidx =>
        Some (ginfo_loc, gidx)
      | _ => None
      end
    | _ => None
    end.

  Definition ESR_EL2_SYSREG_IS_WRITE_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr =>
      if __ESR_EL2_SYSREG_IS_WRITE esr then Some 1 else Some 0
    end.

  Definition ESR_EL2_SYSREG_ISS_RT_spec (esr: Z64) (adt: RData) : option Z :=
    match esr with
    | VZ64 esr =>
      Some (__ESR_EL2_SYSREG_ISS_RT esr)
    end.

  Definition ns_granule_map_spec (slot: Z) (granule: Pointer) (adt: RData) : option RData :=
    let gidx := offset granule in
    rely (peq (base granule) ginfo_loc);
    rely is_gidx gidx;
    Some adt {priv: (priv adt) {buffer: (buffer (priv adt)) # slot == (Some gidx)}}.

  Definition ns_buffer_unmap_spec (slot: Z) (adt: RData) : option RData :=
    Some adt {priv: (priv adt) {buffer: (buffer (priv adt)) # slot == None}}.

  Definition ns_buffer_read_rec_params_spec (slot: Z) (adt: RData) : option (RData * Z) :=
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let st := share adt in
      let e := EVT CPU_ID (COPY_NS gidx READ_REC_PARAMS) in
      let gn := (gs st) @ gidx in
      if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
        let ns_data := g_data (gnorm gn) in
        Some (adt {log: e :: (log adt)} {share: st} {priv: (priv adt) {rec_params: ns_data}}, 0)
      else
        Some (adt {log: e :: (log adt)} {share: st}, 1)
    | _ => None
    end.

  Definition ns_buffer_read_realm_params_spec (slot: Z) (adt: RData) : option (RData * Z) :=
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let st := share adt in
      let e := EVT CPU_ID (COPY_NS gidx READ_REALM_PARAMS) in
      let gn := (gs st) @ gidx in
      if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
        let ns_data := g_data (gnorm gn) in
        Some (adt {log: e :: (log adt)} {share: st} {priv: (priv adt) {realm_params: ns_data}}, 0)
      else
        Some (adt {log: e :: (log adt)} {share: st}, 1)
    | _ => None
    end.

  Definition ns_buffer_read_rec_run_spec (slot: Z) (adt: RData) : option (RData * Z) :=
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      let st := share adt in
      let e := EVT CPU_ID (COPY_NS gidx READ_REC_RUN) in
      let gn := (gs st) @ gidx in
      if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
        let ns_data := g_data (gnorm gn) in
        Some (adt {log: e :: (log adt)} {share: st} {priv: (priv adt) {rec_run: ns_data}}, 1)
      else
        Some (adt {log: e :: (log adt)} {share: st}, 0)
    | _ => None
    end.

  Definition ns_buffer_write_rec_run_spec (slot: Z) (adt: RData) : option (RData * Z) :=
    match (buffer (priv adt)) @ slot with
    | Some gidx =>
      when adt == query_oracle adt;
      let st := share adt in
      let e := EVT CPU_ID (COPY_NS gidx (WRITE_REC_RUN (rec_run (priv adt)))) in
      let gn := (gs st) @ gidx in
      if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
        let g' := gn {gnorm: (gnorm gn) {g_data: (rec_run (priv adt))}} in
        Some (adt {log: e :: (log adt)} {share: st {gs: (gs (share adt)) # gidx == g'}}, 1)
      else
        Some (adt {log: e :: (log adt)} {share: st}, 0)
    | _ => None
    end.

  Definition ns_buffer_read_data_spec (slot: Z) (data: Pointer) (adt: RData) : option (RData * Z) :=
    rely (peq (base data) buffer_loc);
    match (buffer (priv adt)) @ slot, (buffer (priv adt)) @ (offset data) with
    | Some gidx, Some target =>
      let gt := (gs (share adt)) @ target in
      rely prop_dec (glock gt = Some CPU_ID);
      let st := share adt in
      let e := EVT CPU_ID (COPY_NS gidx (READ_DATA target)) in
      let gn := (gs st) @ gidx in
      if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
        let g' := gt {gnorm: (gnorm gt) {g_data: (g_data (gnorm gn))}} in
        Some (adt {log: e :: (log adt)} {share: st {gs: (gs (share adt)) # target == g'}}, 1)
      else
        Some (adt {log: e :: (log adt)} {share: st}, 0)
    | _, _ => None
    end.

  Definition max_ipa_size_spec  (adt: RData) : option Z64 :=
    Some (VZ64 IPA_SIZE).

  Definition region_is_contained_spec (container_base: Z64) (container_end: Z64) (region_base: Z64) (region_end: Z64) (adt: RData) : option Z :=
    match container_base, container_end, region_base, region_end with
    | VZ64 a, VZ64 b, VZ64 c, VZ64 d =>
      Some (region_is_contained_ a b c d)
    end.

  Definition check_granule_idx_spec (idx: Z64) (adt: RData) : option Z :=
    match idx with
    | VZ64 idx =>
      if (0 <=? idx) && (idx <? NR_GRANULES) then
        Some 1
      else Some 0
    end.

  Definition addr_to_gidx_spec (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      Some (VZ64 (__addr_to_gidx addr - 1))
    end.

  Definition gidx_to_addr_spec (addr: Z64) (adt: RData) : option Z64 :=
    match addr with
    | VZ64 addr =>
      Some (VZ64 (__gidx_to_addr addr))
    end.

  Definition find_spinlock_spec (addr: Z64) (adt: RData) : option Pointer :=
    match addr with
    | VZ64 addr =>
      let gidx := __addr_to_gidx addr in
      Some (spinlock_loc, gidx)
    end.

  Definition spinlock_acquire_spec (lock: Pointer) (adt: RData) : option RData :=
    rely (peq (base lock) spinlock_loc);
    let gidx := offset lock in
    when adt == query_oracle adt;
    let e := EVT CPU_ID (ACQ_GPT gidx) in
    rely prop_dec (((gpt_lk (share adt)) @ gidx) = None);
    Some adt {log: e :: (log adt)} {share: (share adt) {gpt_lk: (gpt_lk (share adt)) # gidx == (Some CPU_ID)}}.

  Definition spinlock_release_spec (lock: Pointer) (adt: RData) : option RData :=
    rely (peq (base lock) spinlock_loc);
    let gidx := offset lock in
    rely prop_dec (((gpt_lk (share adt)) @ gidx) = (Some CPU_ID));
    let e := EVT CPU_ID (REL_GPT gidx ((gpt (share adt)) @ gidx)) in
    Some adt {log: e :: (log adt)} {share: (share adt) {gpt_lk: (gpt_lk (share adt)) # gidx == None}}.

  Definition get_pas_spec (idx: Z64) (adt: RData) : option Z64 :=
    match idx with
    | VZ64 gidx =>
      let gidx := gidx + 1 in
      rely is_gidx gidx;
      rely prop_dec ((gpt_lk (share adt)) @ gidx = Some CPU_ID);
      if (gpt (share adt)) @ gidx then Some (VZ64 GPI_REALM)
      else Some (VZ64 GPI_NS)
    end.

  Definition set_pas_spec (idx: Z64) (pas: Z64) (adt: RData) : option RData :=
    match idx, pas with
    | VZ64 gidx, VZ64 pas =>
      let gidx := gidx + 1 in
      rely is_gidx gidx;
      rely prop_dec ((gpt_lk (share adt)) @ gidx = Some CPU_ID);
      Some adt {share: (share adt) {gpt: (gpt (share adt)) # gidx == (pas =? GPI_REALM)}}
    end.

  Definition tlbi_by_pa_spec (addr: Z64) (adt: RData) : option RData :=
    Some adt.

  Definition baremore_enter_spec  (adt: RData) : option (RData * Z) :=
    let cregs := cpu_regs (priv adt) in
    let stack' := (r_lr cregs) :: (r_x4 cregs) :: (r_x3 cregs) :: (r_x2 cregs) :: (r_x1 cregs) :: (r_x0 cregs) :: (el3_stack (priv adt)) in
    let x3' := (r_x0 cregs) in
    let x0' := (r_esr_el3 cregs) in
    let x1' := Z.land x0' ESR_EC in
    let x2' := ESR_EC_SMC in
    if x1' =? x2' then
      let x1' := Z.land x0' ESR_EC_SMC_IMM16 in
      if x1' =? 0 then
        let x0' := x3' in
        let x1' := r_scr_el3 cregs in
        let x4' := SCR_WORLD_MASK in
        let x1' := Z.land x1' x4' in
        if x1' =? SCR_REALM_WORLD then
          (* realm_smc_handler *)
          let x1' := Z.land x0' NOT_SMC_STD_CALL_MASK in
          let x2' := SMC_STD_CALL_BASE in
          if x1' =? x2' then
            let lr' := r_lr cregs in
            let x4' := r_x4 cregs in
            let x3' := r_x3 cregs in
            let x2' := r_x2 cregs in
            let x1' := r_x1 cregs in
            let x0' := r_x0 cregs in
            let stack' := (r_lr cregs) :: (r_x29 cregs) :: (r_x18 cregs) :: (el3_stack (priv adt)) in
            let func_id := Z.land x0' SMC_STD_CALL_MASK in
            if func_id =? SMC_ASC_MARK_REALM then
                Some (adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'}}}, SMC_ASC_MARK_REALM)
            else
              if func_id =? SMC_ASC_MARK_NONSECURE then
                Some (adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'}}}, SMC_ASC_MARK_NONSECURE)
              else None
          else
            Some (adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'}}}, EL3_TO_NS)
        else
          let x1' := Z.land x3' NOT_SMC_ARM_ARCH_CALL_MASK in
          let x2' := SMC_ARM_ARCH_CALL_BASE in
          if x1' =? x2' then
            let x0' := Z.land x3' SMC_ARM_ARCH_CALL_MASK in
            Some (adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'}}}, EL3_TO_RMM)
          else None
      else None
    else None.

  Definition baremore_to_ns_spec  (adt: RData) : option RData :=
    let cregs := cpu_regs (priv adt) in
    let realm_regs_el3' :=
        (realm_regs_el3 (priv adt)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
                              {r_afsr0_el2: (r_afsr0_el2 cregs)} {r_afsr1_el2: (r_afsr1_el2 cregs)} {r_amair_el2: (r_amair_el2 cregs)}
                              {r_cnthctl_el2: (r_cnthctl_el2 cregs)} {r_cntvoff_el2: (r_cntvoff_el2 cregs)}
                              {r_cptr_el2: (r_cptr_el2 cregs)} {r_elr_el2: (r_elr_el2 cregs)} {r_esr_el2: (r_esr_el2 cregs)}
                              {r_far_el2: (r_far_el2 cregs)} {r_hacr_el2: (r_hacr_el2 cregs)} {r_hcr_el2: (r_hcr_el2 cregs)}
                              {r_hpfar_el2: (r_hpfar_el2 cregs)} {r_hstr_el2: (r_hstr_el2 cregs)} {r_mair_el2: (r_mair_el2 cregs)}
                              {r_mpam_el2: (r_mpam_el2 cregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 cregs)} {r_pmscr_el2: (r_pmscr_el2 cregs)}
                              {r_sctlr_el2: (r_sctlr_el2 cregs)} {r_scxtnum_el2: (r_scxtnum_el2 cregs)} {r_sp_el2: (r_sp_el2 cregs)}
                              {r_spsr_el2: (r_spsr_el2 cregs)} {r_tcr_el2: (r_tcr_el2 cregs)} {r_tfsr_el2: (r_tfsr_el2 cregs)}
                              {r_tpidr_el2: (r_tpidr_el2 cregs)} {r_trfcr_el2: (r_trfcr_el2 cregs)} {r_ttbr0_el2: (r_ttbr0_el2 cregs)}
                              {r_ttbr1_el2: (r_ttbr1_el2 cregs)} {r_vbar_el2: (r_vbar_el2 cregs)} {r_vdisr_el2: (r_vdisr_el2 cregs)}
                              {r_vmpidr_el2: (r_vmpidr_el2 cregs)} {r_vncr_el2: (r_vncr_el2 cregs)} {r_vpidr_el2: (r_vpidr_el2 cregs)}
                              {r_vsesr_el2: (r_vsesr_el2 cregs)} {r_vstcr_el2: (r_vstcr_el2 cregs)} {r_vsttbr_el2: (r_vsttbr_el2 cregs)}
                              {r_vtcr_el2: (r_vtcr_el2 cregs)} {r_vttbr_el2: (r_vttbr_el2 cregs)} {r_zcr_el2: (r_zcr_el2 cregs)}
    in
    let nregs := (ns_regs_el3 (priv adt)) in
    let cregs' :=
        (cpu_regs (priv adt)) {r_spsr_el3: (r_spsr_el3 nregs)} {r_elr_el3: (r_elr_el3 nregs)} {r_actlr_el2: (r_actlr_el2 nregs)}
                        {r_afsr0_el2: (r_afsr0_el2 nregs)} {r_afsr1_el2: (r_afsr1_el2 nregs)} {r_amair_el2: (r_amair_el2 nregs)}
                        {r_cnthctl_el2: (r_cnthctl_el2 nregs)} {r_cntvoff_el2: (r_cntvoff_el2 nregs)}
                        {r_cptr_el2: (r_cptr_el2 nregs)} {r_elr_el2: (r_elr_el2 nregs)} {r_esr_el2: (r_esr_el2 nregs)}
                        {r_far_el2: (r_far_el2 nregs)} {r_hacr_el2: (r_hacr_el2 nregs)} {r_hcr_el2: (r_hcr_el2 nregs)}
                        {r_hpfar_el2: (r_hpfar_el2 nregs)} {r_hstr_el2: (r_hstr_el2 nregs)} {r_mair_el2: (r_mair_el2 nregs)}
                        {r_mpam_el2: (r_mpam_el2 nregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 nregs)} {r_pmscr_el2: (r_pmscr_el2 nregs)}
                        {r_sctlr_el2: (r_sctlr_el2 nregs)} {r_scxtnum_el2: (r_scxtnum_el2 nregs)} {r_sp_el2: (r_sp_el2 nregs)}
                        {r_spsr_el2: (r_spsr_el2 nregs)} {r_tcr_el2: (r_tcr_el2 nregs)} {r_tfsr_el2: (r_tfsr_el2 nregs)}
                        {r_tpidr_el2: (r_tpidr_el2 nregs)} {r_trfcr_el2: (r_trfcr_el2 nregs)} {r_ttbr0_el2: (r_ttbr0_el2 nregs)}
                        {r_ttbr1_el2: (r_ttbr1_el2 nregs)} {r_vbar_el2: (r_vbar_el2 nregs)} {r_vdisr_el2: (r_vdisr_el2 nregs)}
                        {r_vmpidr_el2: (r_vmpidr_el2 nregs)} {r_vncr_el2: (r_vncr_el2 nregs)} {r_vpidr_el2: (r_vpidr_el2 nregs)}
                        {r_vsesr_el2: (r_vsesr_el2 nregs)} {r_vstcr_el2: (r_vstcr_el2 nregs)} {r_vsttbr_el2: (r_vsttbr_el2 nregs)}
                        {r_vtcr_el2: (r_vtcr_el2 nregs)} {r_vttbr_el2: (r_vttbr_el2 nregs)} {r_zcr_el2: (r_zcr_el2 nregs)}
    in
    let cregs' := cregs' {r_scr_el3: SCR_EL3_NS} in
    match el3_stack (priv adt) with
    | lr' :: x4' :: x3' :: x2' :: x1' :: x0' :: stack' =>
      let cregs' := cregs' {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'} {r_x4: x4'} {r_lr: lr'} in
      Some adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs'} {realm_regs_el3: realm_regs_el3'}}
    | _ => None
    end.

  Definition baremore_to_rmm_spec  (adt: RData) : option RData :=
    let cregs := cpu_regs (priv adt) in
    let ns_regs_el3' :=
        (ns_regs_el3 (priv adt)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
                            {r_afsr0_el2: (r_afsr0_el2 cregs)} {r_afsr1_el2: (r_afsr1_el2 cregs)} {r_amair_el2: (r_amair_el2 cregs)}
                            {r_cnthctl_el2: (r_cnthctl_el2 cregs)} {r_cntvoff_el2: (r_cntvoff_el2 cregs)}
                            {r_cptr_el2: (r_cptr_el2 cregs)} {r_elr_el2: (r_elr_el2 cregs)} {r_esr_el2: (r_esr_el2 cregs)}
                            {r_far_el2: (r_far_el2 cregs)} {r_hacr_el2: (r_hacr_el2 cregs)} {r_hcr_el2: (r_hcr_el2 cregs)}
                            {r_hpfar_el2: (r_hpfar_el2 cregs)} {r_hstr_el2: (r_hstr_el2 cregs)} {r_mair_el2: (r_mair_el2 cregs)}
                            {r_mpam_el2: (r_mpam_el2 cregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 cregs)} {r_pmscr_el2: (r_pmscr_el2 cregs)}
                            {r_sctlr_el2: (r_sctlr_el2 cregs)} {r_scxtnum_el2: (r_scxtnum_el2 cregs)} {r_sp_el2: (r_sp_el2 cregs)}
                            {r_spsr_el2: (r_spsr_el2 cregs)} {r_tcr_el2: (r_tcr_el2 cregs)} {r_tfsr_el2: (r_tfsr_el2 cregs)}
                            {r_tpidr_el2: (r_tpidr_el2 cregs)} {r_trfcr_el2: (r_trfcr_el2 cregs)} {r_ttbr0_el2: (r_ttbr0_el2 cregs)}
                            {r_ttbr1_el2: (r_ttbr1_el2 cregs)} {r_vbar_el2: (r_vbar_el2 cregs)} {r_vdisr_el2: (r_vdisr_el2 cregs)}
                            {r_vmpidr_el2: (r_vmpidr_el2 cregs)} {r_vncr_el2: (r_vncr_el2 cregs)} {r_vpidr_el2: (r_vpidr_el2 cregs)}
                            {r_vsesr_el2: (r_vsesr_el2 cregs)} {r_vstcr_el2: (r_vstcr_el2 cregs)} {r_vsttbr_el2: (r_vsttbr_el2 cregs)}
                            {r_vtcr_el2: (r_vtcr_el2 cregs)} {r_vttbr_el2: (r_vttbr_el2 cregs)} {r_zcr_el2: (r_zcr_el2 cregs)}
    in
    let nregs := (realm_regs_el3 (priv adt)) in
    let cregs' :=
        (cpu_regs (priv adt)) {r_spsr_el3: (r_spsr_el3 nregs)} {r_elr_el3: (r_elr_el3 nregs)} {r_actlr_el2: (r_actlr_el2 nregs)}
                        {r_afsr0_el2: (r_afsr0_el2 nregs)} {r_afsr1_el2: (r_afsr1_el2 nregs)} {r_amair_el2: (r_amair_el2 nregs)}
                        {r_cnthctl_el2: (r_cnthctl_el2 nregs)} {r_cntvoff_el2: (r_cntvoff_el2 nregs)}
                        {r_cptr_el2: (r_cptr_el2 nregs)} {r_elr_el2: (r_elr_el2 nregs)} {r_esr_el2: (r_esr_el2 nregs)}
                        {r_far_el2: (r_far_el2 nregs)} {r_hacr_el2: (r_hacr_el2 nregs)} {r_hcr_el2: (r_hcr_el2 nregs)}
                        {r_hpfar_el2: (r_hpfar_el2 nregs)} {r_hstr_el2: (r_hstr_el2 nregs)} {r_mair_el2: (r_mair_el2 nregs)}
                        {r_mpam_el2: (r_mpam_el2 nregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 nregs)} {r_pmscr_el2: (r_pmscr_el2 nregs)}
                        {r_sctlr_el2: (r_sctlr_el2 nregs)} {r_scxtnum_el2: (r_scxtnum_el2 nregs)} {r_sp_el2: (r_sp_el2 nregs)}
                        {r_spsr_el2: (r_spsr_el2 nregs)} {r_tcr_el2: (r_tcr_el2 nregs)} {r_tfsr_el2: (r_tfsr_el2 nregs)}
                        {r_tpidr_el2: (r_tpidr_el2 nregs)} {r_trfcr_el2: (r_trfcr_el2 nregs)} {r_ttbr0_el2: (r_ttbr0_el2 nregs)}
                        {r_ttbr1_el2: (r_ttbr1_el2 nregs)} {r_vbar_el2: (r_vbar_el2 nregs)} {r_vdisr_el2: (r_vdisr_el2 nregs)}
                        {r_vmpidr_el2: (r_vmpidr_el2 nregs)} {r_vncr_el2: (r_vncr_el2 nregs)} {r_vpidr_el2: (r_vpidr_el2 nregs)}
                        {r_vsesr_el2: (r_vsesr_el2 nregs)} {r_vstcr_el2: (r_vstcr_el2 nregs)} {r_vsttbr_el2: (r_vsttbr_el2 nregs)}
                        {r_vtcr_el2: (r_vtcr_el2 nregs)} {r_vttbr_el2: (r_vttbr_el2 nregs)} {r_zcr_el2: (r_zcr_el2 nregs)}
    in
    let cregs' := cregs' {r_elr_el3: rmm_handler} {r_scr_el3: SCR_EL3_REALM} in
    match el3_stack (priv adt) with
    | lr' :: x4' :: x3' :: x2' :: x1' :: x0' :: stack' =>
      let cregs' := cregs' {r_x0: x0'} {r_x1: x1'} {r_x2: x2'} {r_x3: x3'} {r_x4: x4'} {r_lr: lr'} in
      Some adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs'} {ns_regs_el3: ns_regs_el3'}}
    | _ => None
    end.

  Definition baremore_return_rmm_spec (ret: Z64) (adt: RData) : option RData :=
    match ret with
    | VZ64 ret =>
      let cregs := cpu_regs (priv adt) in
      match el3_stack (priv adt) with
      | lr' :: x29' :: x18' :: stack' =>
        let cregs' := cregs {r_x0: ret} {r_x18: x18'} {r_x29: x29'} {r_lr: lr'} in
        Some adt {priv: (priv adt) {el3_stack: stack'} {cpu_regs: cregs'}}
      | _ => None
      end
    end.

  Definition enter_rmm_spec  (adt: RData) : option RData := Some adt.

  Definition exit_rmm_spec (ret: Z64) (adt: RData) : option RData :=
    match ret with
    | VZ64 ret =>
      let cregs := cpu_regs (priv adt) in
      let cregs' := cregs {r_x0: SMC_RMM_REQ_COMPLETE} {r_x1: ret} {r_x2: 0} {r_x3: 0}  {r_x4: 0} {r_lr: 0} in
      Some adt {priv: (priv adt) {cpu_regs: cregs'}}
    end.

  Inductive NSStep :=
  | NS_ACCESS_MEM' (addr val: Z)
  | NS_ACCESS_REG' (reg val: Z)
  | NS_TRAP'.

  Inductive RealmStep :=
  | REALM_ACCESS_MEM' (addr val: Z)
  | REALM_ACCESS_REG' (reg val: Z)
  | REALM_TRAP' (t: realm_trap_type).

  Parameter next_realm_step: Log -> RealmStep.
  Parameter next_ns_step: Log -> NSStep.

  Definition access_reg (reg: Z) (val: Z) (adt: RData) :=
    rely ((0 <=? reg) && (reg <=? 30));
    rely is_int64 val;
    Some (adt {priv: (priv adt) {cpu_regs: set_reg reg val (cpu_regs (priv adt))}},
          get_reg reg (cpu_regs (priv adt))).

  Definition ns_trap (adt: RData) :=
    rely prop_dec (mstage (priv adt) = NS);
    Some adt {priv: (priv adt) {mstage: RMM NSTRAP}}.

  Definition realm_trap (rd_gidx rec_gidx: Z) (t: realm_trap_type) (adt: RData) :=
    let esr := r_esr_el2 (cpu_regs (priv adt)) in
    let adt := adt {priv: (priv adt) {mstage: RMM (REALMTRAP t)}} in
    match t with
    | WFX =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_WFX);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | HVC =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_HVC);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | SMC =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SMC);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | IDREG =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
      rely ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | TIMER =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
      rely (negb ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID));
      rely ((Z.land esr ESR_EL2_SYSREG_TIMERS_MASK) =? ESR_EL2_SYSREG_TIMERS);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | ICC =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
      rely (negb ((Z.land esr ESR_EL2_SYSREG_TIMERS_MASK) =? ESR_EL2_SYSREG_TIMERS));
      rely (negb ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID));
      rely ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | DATA_ABORT =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_DATA_ABORT);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | INSTR_ABORT =>
      rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_INST_ABORT);
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
    | IRQ =>
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_IRQ_LEL}}
    | FIQ =>
      Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_FIQ_LEL}}
    end.

  Definition user_step_spec (adt: RData) : option (RData * Z64) :=
    match mstage (priv adt), cur_rec (priv adt) with
    | REALM rd_gidx rec_gidx, Some cur_rec_gidx =>
      let grd := (gs (share adt)) @ rd_gidx in
      let grec := (gs (share adt)) @ rec_gidx in
      rely (g_rd (ginfo grec) =? rd_gidx);
      rely (rec_gidx =? cur_rec_gidx);
      match next_realm_step (log adt) with
      | REALM_ACCESS_MEM' addr val =>
        let e := EVT CPU_ID (REALM_ACCESS_MEM rd_gidx rec_gidx addr val) in
        when ret, st' == repl_realm_access_mem CPU_ID rd_gidx rec_gidx addr val (share adt);
        Some (adt {log: e :: log adt} {share: st'}, VZ64 ret)
      | REALM_ACCESS_REG' reg val =>
        when ret, adt == access_reg reg val adt;
        Some (adt, VZ64 ret)
      | REALM_TRAP' t =>
        when adt == realm_trap rd_gidx rec_gidx t adt;
        Some (adt, VZ64 0)
      end
    | NS, None =>
      match next_ns_step (log adt) with
      | NS_ACCESS_MEM' addr val =>
        let e := EVT CPU_ID (NS_ACCESS_MEM addr val) in
        when ret, st' == repl_ns_access_mem CPU_ID addr val (share adt);
        Some (adt {log: e :: log adt} {share: st'}, VZ64 ret)
      | NS_ACCESS_REG' reg val =>
        when ret, adt == access_reg reg val adt;
        Some (adt, VZ64 ret)
      | NS_TRAP' =>
        when adt == ns_trap adt;
        Some (adt, VZ64 0)
      end
    | _, _ => None
    end.

  Definition get_monitor_call_arg_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (r_x1 (cpu_regs (priv adt)))).

  Definition get_monitor_call_ret_spec  (adt: RData) : option Z64 :=
    Some (VZ64 (r_x0 (cpu_regs (priv adt)))).

  Definition set_monitor_call_spec (call_fn: Z) (arg: Z64) (adt: RData) : option RData :=
    match arg with
    | VZ64 arg =>
      let cregs' := (cpu_regs (priv adt)) {r_x0: call_fn} {r_x1: arg} {r_esr_el3: ESR_EC_SMC} in
      Some adt {priv: (priv adt) {cpu_regs: cregs'}}
    end.

  Parameter measure_start: Z.

  Definition measurement_start_spec (rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely prop_dec (glock gn = Some CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_start}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _ => None
    end.

  Parameter measure_extend_rec_header: Z -> Z.

  Definition measurement_extend_rec_header_spec (rd: Pointer) (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rd), (buffer (priv adt)) @ (offset rec) with
    | Some gidx, Some rec_gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely prop_dec (glock gn = Some CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_rec_header
                                                              (g_measurement_ctx (gnorm gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _, _ => None
    end.

  Parameter measure_extend_rec_regs: Z -> RegState -> Z.

  Definition measurement_extend_rec_regs_spec (rd: Pointer) (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rd), (buffer (priv adt)) @ (offset rec) with
    | Some gidx, Some rec_gidx =>
      let gn := (gs (share adt)) @ gidx in
      let gn_rec := (gs (share adt)) @ rec_gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
      rely prop_dec (glock gn = Some CPU_ID);
      rely (ref_accessible gn_rec CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_rec_regs
                                                              (g_measurement_ctx (gnorm gn))
                                                              (g_regs (grec gn_rec))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _, _ => None
    end.

  Parameter measure_extend_rec_pstate: Z -> Z -> Z.

  Definition measurement_extend_rec_pstate_spec (rd: Pointer) (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rd), (buffer (priv adt)) @ (offset rec) with
    | Some gidx, Some rec_gidx =>
      let gn := (gs (share adt)) @ gidx in
      let gn_rec := (gs (share adt)) @ rec_gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
      rely prop_dec (glock gn = Some CPU_ID);
      rely (ref_accessible gn_rec CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_rec_pstate
                                                              (g_measurement_ctx (gnorm gn))
                                                              (g_pstate (grec gn_rec))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _, _ => None
    end.

  Parameter measure_extend_rec_sysregs: Z -> RegState -> Z.

  Definition measurement_extend_rec_sysregs_spec (rd: Pointer) (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base rec) buffer_loc);
    match (buffer (priv adt)) @ (offset rd), (buffer (priv adt)) @ (offset rec) with
    | Some gidx, Some rec_gidx =>
      let gn := (gs (share adt)) @ gidx in
      let gn_rec := (gs (share adt)) @ rec_gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
      rely prop_dec (glock gn = Some CPU_ID);
      rely (ref_accessible gn_rec CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_rec_sysregs
                                                              (g_measurement_ctx (gnorm gn))
                                                              (g_regs (grec gn_rec))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _, _ => None
    end.

  Parameter measure_extend_data_header: Z -> Z.

  Definition measurement_extend_data_header_spec (rd: Pointer) (ofst: Z64) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely prop_dec (glock gn = Some CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_data_header
                                                              (g_measurement_ctx (gnorm gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _ => None
    end.

  Parameter measure_extend_data: Z -> (ZMap.t Z) -> Z.

  Definition measurement_extend_data_spec (rd: Pointer) (data: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base data) buffer_loc);
    match (buffer (priv adt)) @ (offset rd), (buffer (priv adt)) @ (offset data) with
    | Some gidx, Some data_gidx =>
      let gn := (gs (share adt)) @ gidx in
      let gn_data := (gs (share adt)) @ data_gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_data) =? GRANULE_STATE_DATA);
      rely prop_dec (glock gn = Some CPU_ID);
      rely prop_dec (glock gn_data = Some CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_extend_data
                                                              (g_measurement_ctx (gnorm gn))
                                                              (g_data (gnorm gn_data))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        Some adt
    | _, _ => None
    end.

  Parameter measure_finish: Z -> Z.

  Definition measurement_finish_spec (rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    match (buffer (priv adt)) @ (offset rd) with
    | Some gidx =>
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
      rely prop_dec (glock gn = Some CPU_ID);
      if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
        if measure_finish (g_measurement_ctx (gnorm gn)) =? 0 then
          let g' := gn {gnorm: (gnorm gn) {g_measurement: 0}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
        else None
      else
        Some adt
    | _ => None
    end.

  Parameter __addr_is_level_aligned: Z -> Z -> bool.

  Definition addr_is_level_aligned_spec (addr: Z64) (level: Z64) (adt: RData) : option Z :=
    match addr, level with
    | VZ64 addr, VZ64 level =>
      if __addr_is_level_aligned addr level then Some 1 else Some 0
    end.

  Definition barrier_spec  (adt: RData) : option RData := Some adt.

  Definition granule_refcount_inc_spec (g: Pointer) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      let gidx := offset g in
      rely (peq (base g) ginfo_loc);
      rely is_gidx gidx;
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      let g' := gn {ginfo: (ginfo gn) {g_refcount: (g_refcount (ginfo gn)) + val}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

  Definition granule_refcount_dec_spec (g: Pointer) (val: Z64) (adt: RData) : option RData :=
    match val with
    | VZ64 val =>
      let gidx := offset g in
      rely (peq (base g) ginfo_loc);
      rely is_gidx gidx;
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      let g' := gn {ginfo: (ginfo gn) {g_refcount: (g_refcount (ginfo gn)) - val}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

  Definition entry_to_phys_spec (entry: Z64) (level: Z64) (adt: RData) : option Z64 :=
    match entry, level with
    | VZ64 entry, VZ64 level =>
      Some (VZ64 (__entry_to_phys entry level))
    end.

  Definition stage2_tlbi_ipa_spec (ipa: Z64) (size: Z64) (adt: RData) : option RData :=
    match ipa, size with
    | VZ64 ipa, VZ64 size =>
      rely (GRANULE_ALIGNED ipa);
      let ipa_gidx := __addr_to_gidx ipa in
      let n_granules := size / GRANULE_SIZE in
      let tlb' := fun cpu gidx =>
                    if (gidx >=? ipa_gidx) && (gidx <? ipa_gidx + n_granules) then
                      -1
                    else
                      (tlbs (share adt)) cpu gidx
      in
      Some adt {share: (share adt) {tlbs: tlb'}}
    end.

End Spec.

Hypothesis find_next_bit_range: forall bitmap n, 0 <= n -> (if n =? 64 then n else n + 1) <= (__find_next_set_bit_spec bitmap n) <= 64.

Hypothesis entry_to_phys_range: forall entry level, is_int64 entry = true -> is_int64 (__entry_to_phys entry level) = true.
