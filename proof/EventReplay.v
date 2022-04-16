Require Import Coqlib.
Require Import Maps.
Require Import GenSem.

Require Import Constants.
Require Import CommonLib.
Require Import RData.

Open Local Scope Z_scope.

Definition Raw := 0.
Definition Gpt := 1.
Definition Table := 5.
Definition Sec := 999.

Fixpoint inlist (a: Z) (l: list Z) : bool :=
  match l with
  | nil => false
  | z :: l' =>
    match inlist a l' with
    | true => true
    | _ => a =? z
    end
  end.

Definition tbl_level_cons gt glvl lvl :=
  (negb (gt =? GRANULE_STATE_TABLE)) || (glvl >? lvl - 2).

Definition repl_acq lvl cid gidx st :=
  let g := (gs st) @ gidx in
  rely tbl_level_cons (gtype g) (tbl_level (gaux g)) lvl;
  rely prop_dec (glock g = None);
  let g' := g {glock: Some cid} in
  Some (st {gs: (gs st) # gidx == g'}, 0).

Definition push_norm g :=
  negb (inlist (gtype g) (GRANULE_STATE_REC_LIST :: GRANULE_STATE_NS :: nil)).

Definition ref_accessible g cid :=
  match gref g, glock g with
  | Some c, _ => c =? cid
  | None, Some c => c =? cid
  | _, _ => false
  end.

Definition push_rec g cid :=
  ((gtype g) =? GRANULE_STATE_REC) && (ref_accessible g cid).

Definition repl_rel cid gidx g' st :=
  let g0 := (gs st) @ gidx in
  rely prop_dec (glock g0 = Some cid);
  let g := g0 {glock: None} {gnorm: (gnorm g')} {ginfo: (ginfo g')}
              {gtype: g_tag (ginfo g')} {gaux: (gaux g')}
              {grec: if (ref_accessible g0 cid) && (negb (ref_accessible g' cid)) then
                       (grec g')
                     else (grec g0)} in
  Some (st {gs: (gs st) # gidx == g}, 0).

Definition repl_recro cid gidx g_rec rec_idx st :=
  let g := (gs st) @ gidx in
  rely prop_dec (glock g = Some cid);
  rely (gtype g =? GRANULE_STATE_DELEGATED);
  rely (negb (g_inited (gro g)));
  let g' := (g {gro: mkRecReadOnly true g_rec rec_idx}) in
  Some (st {gs: (gs st) # gidx == g'}, 0).

Definition repl_get_gcnt cid gidx st :=
  let g := (gs st) @ gidx in
  rely (inlist (gtype g) (GRANULE_STATE_RD :: GRANULE_STATE_REC :: nil));
  rely prop_dec (glock g = Some cid);
  Some (st, gcnt g).

Definition repl_inc_gcnt cid gidx st :=
  let g := (gs st) @ gidx in
  rely prop_dec (glock g = Some cid);
  if gtype g =? GRANULE_STATE_RD then
    Some (st {gs: (gs st) # gidx == (g {gcnt: (gcnt g) + 1})}, 0)
  else
    rely (gcnt g =? 0);
    rely prop_dec (gref g = None);
    Some (st {gs: (gs st) # gidx == (g {gref: Some cid} {gcnt: 1})}, 0).

Definition repl_dec_rd_gcnt (cid: Z) gidx st :=
  let g := (gs st) @ gidx in
  rely (gtype g =? GRANULE_STATE_RD);
  rely (gcnt g >? 0);
  Some (st {gs: (gs st) # gidx == (g {gcnt: (gcnt g) - 1})}, 0).

Definition repl_dec_rec_gcnt cid gidx g' st :=
  let g0 := (gs st) @ gidx in
  rely (gtype g0 =? GRANULE_STATE_REC);
  rely prop_dec (glock g0 = None);
  rely prop_dec (gref g0 = Some cid);
  rely (gcnt g0 =? 1);
  let g := g0 {grec: (grec g')} {gref: None} {gcnt: 0} in
  Some (st {gs: (gs st) # gidx == g}, 0).

Definition repl_recl (cid: Z) gidx idx t st :=
  let g := (gs st) @ gidx in
  rely (gtype g =? GRANULE_STATE_REC_LIST);
  match t with
  | GET_RECL => Some (st, (g_data (gnorm g)) @ idx)
  | SET_RECL val =>
    let grd := (gs st) @ (g_rd (ginfo g)) in
    rely prop_dec (glock grd = Some cid);
    rely ((g_data (gnorm g)) @ idx =? 0);
    let g' := g {gnorm: (gnorm g) {g_data: (g_data (gnorm g)) # idx == val}} in
    Some (st {gs: (gs st) # gidx == g'}, 0)
  | UNSET_RECL =>
    let rec_gidx := (g_data (gnorm g)) @ idx in
    rely is_gidx rec_gidx;
    let grec := (gs st) @ rec_gidx in
    rely (gtype grec =? GRANULE_STATE_REC);
    rely prop_dec (glock grec = Some cid);
    rely prop_dec (gref grec = None);
    let g' := g {gnorm: (gnorm g) {g_data: (g_data (gnorm g)) # idx == 0}} in
    Some (st {gs: (gs st) # gidx == g'}, 0)
  end.

Definition repl_acq_gpt cid gidx st :=
  rely prop_dec ((gpt_lk st) @ gidx = None);
  Some (st {gpt_lk: (gpt_lk st) # gidx == (Some cid)}, 0).

Definition repl_rel_gpt cid gidx secure st :=
  rely prop_dec ((gpt_lk st) @ gidx = Some cid);
  Some (st {gpt: (gpt st) # gidx == secure} {gpt_lk: (gpt_lk st) # gidx == None}, 0).

Definition repl_rtt_walk lvl (cid: Z) root_gidx map_addr level st :=
  rely (level =? lvl - 2);
  let idx0 := __addr_to_idx map_addr 0 in
  let idx1 := __addr_to_idx map_addr 1 in
  let idx2 := __addr_to_idx map_addr 2 in
  let idx3 := __addr_to_idx map_addr 3 in
  rely is_int64 idx0; rely is_int64 idx1; rely is_int64 idx2; rely is_int64 idx3;
  (* hold root lock *)
  rely is_gidx root_gidx;
  let groot := (gs st) @ root_gidx in
  rely (tbl_level (gaux groot) =? 0);
  rely prop_dec (glock groot = None);
  if level =? 0 then
    (* walk until root *)
    Some (st {gs: (gs st) # root_gidx == (groot {glock: Some CPU_ID})}, 0)
  else
    (* walk deeper root *)
    rely (level >? 0);
    rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
    rely (gtype groot =? GRANULE_STATE_TABLE);
    let entry0 := (g_data (gnorm groot)) @ idx0 in
      rely is_int64 entry0;
      let phys0 := __entry_to_phys entry0 3 in
      let lv1_gidx := __addr_to_gidx phys0 in
      rely is_int64 phys0;
      if (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx) then
        (* level 1 valid, hold level 1 lock *)
        let glv1 := (gs st) @ lv1_gidx in
        rely prop_dec (glock glv1 = None);
        rely (tbl_level (gaux glv1) =? 1);
        if level =? 1 then
          (* walk until level 1 *)
          Some (st {gs: (gs st) # lv1_gidx == (glv1 {glock: Some CPU_ID})}, 0)
        else
          (* walk deeper level 1 *)
          rely (level >? 1);
          rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
          rely (gtype glv1 =? GRANULE_STATE_TABLE);
          let entry1 := (g_data (gnorm glv1)) @ idx1 in
          rely is_int64 entry1;
          let phys1 := __entry_to_phys entry1 3 in
          let lv2_gidx := __addr_to_gidx phys1 in
          rely is_int64 phys1;
          if (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx) then
            (* level 2 valid, hold level 2 lock *)
            let glv2 := (gs st) @ lv2_gidx in
            rely (tbl_level (gaux glv2) =? 2);
            rely prop_dec (glock glv2 = None);
            if level =? 2 then
              (* walk until level 2 *)
              Some (st {gs: (gs st) # lv2_gidx == (glv2 {glock: Some CPU_ID})}, 0)
            else
              (* walk deeper level 2 *)
              rely (level >? 2);
              rely (g_tag (ginfo glv2) =? GRANULE_STATE_TABLE);
              rely (gtype glv2 =? GRANULE_STATE_TABLE);
              let entry2 := (g_data (gnorm glv2)) @ idx2 in
              rely is_int64 entry2;
              let phys2 := __entry_to_phys entry2 3 in
              let lv3_gidx := __addr_to_gidx phys2 in
              rely is_int64 phys2;
              if (__entry_is_table entry2) && (GRANULE_ALIGNED phys2) && (is_gidx lv3_gidx) then
                (* level 2 valid, hold level 2 lock *)
                let glv3 := (gs st) @ lv3_gidx in
                rely prop_dec (glock glv3 = None);
                rely (tbl_level (gaux glv3) =? 3);
                if level =? 3 then
                  (* walk until level 3 *)
                  Some (st {gs: (gs st) # lv3_gidx == (glv3 {glock: Some CPU_ID})}, 0)
                else (* can't be other level *) None
              else (* level 3 invalid *) Some (st, 1)
          else (* level 2 invalid *) Some (st, 1)
      else (* level 1 invalid *) Some (st, 1).

Definition repl_create_table (llt_gidx: Z) (idx: Z) (rtt_addr: Z) (rtt_gidx: Z) (st: State) :=
  let gn_llt := (gs st) @ llt_gidx in
  let gn_rtt := (gs st) @ rtt_gidx in
  rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
  rely (gtype gn_llt =? GRANULE_STATE_TABLE);
  rely (gtype gn_rtt =? GRANULE_STATE_DELEGATED);
  rely prop_dec (glock gn_rtt = Some CPU_ID);
  rely (tbl_level (gaux gn_rtt) =? 0);
  let entry := (g_data (gnorm gn_llt)) @ idx in
  rely is_int64 entry;
  if entry =? 0 then
    let pte := Z.lor rtt_addr PGTE_S2_TABLE in
    let g' := gn_llt {gnorm: (gnorm gn_llt) {g_data: (g_data (gnorm gn_llt)) # idx == pte}}
                    {ginfo : (ginfo gn_llt) {g_refcount : g_refcount (ginfo gn_llt) + 1}} in
    let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_TABLE} {g_refcount: (g_refcount (ginfo (gn_rtt))) + 1}}
                        {gaux: mkAuxillaryVars (tbl_level (gaux gn_llt) + 1) idx (llt_gidx)} in
    Some (st {gs: (gs st) # llt_gidx == g' # rtt_gidx == grtt'}, 0)
  else Some (st, 1).

Definition repl_rtt_create lvl (cid: Z) root_gidx map_addr level rtt_addr st :=
  rely (level <=? lvl - 2);
  let idx0 := __addr_to_idx map_addr 0 in
  let idx1 := __addr_to_idx map_addr 1 in
  let idx2 := __addr_to_idx map_addr 2 in
  let idx3 := __addr_to_idx map_addr 3 in
  rely is_int64 idx0; rely is_int64 idx1; rely is_int64 idx2; rely is_int64 idx3;
  let rtt_gidx := __addr_to_gidx rtt_addr in
  rely is_gidx rtt_gidx;
  (* hold root lock *)
  rely is_gidx root_gidx;
  let groot := (gs st) @ root_gidx in
  rely (tbl_level (gaux groot) =? 0);
  rely prop_dec (glock groot = None);
  if level =? 0 then
    (* walk until root *)
    repl_create_table root_gidx idx0 rtt_addr rtt_gidx st
  else
    (* walk deeper root *)
    rely (level >? 0);
    rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
    rely (gtype groot =? GRANULE_STATE_TABLE);
    let entry0 := (g_data (gnorm groot)) @ idx0 in
      rely is_int64 entry0;
      let phys0 := __entry_to_phys entry0 3 in
      let lv1_gidx := __addr_to_gidx phys0 in
      rely is_int64 phys0;
      if (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx) then
        (* level 1 valid, hold level 1 lock *)
        let glv1 := (gs st) @ lv1_gidx in
        rely prop_dec (glock glv1 = None);
        rely (tbl_level (gaux glv1) =? 1);
        if level =? 1 then
          (* walk until level 1 *)
          repl_create_table lv1_gidx idx1 rtt_addr rtt_gidx st
        else
          (* walk deeper level 1 *)
          rely (level >? 1);
          rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
          rely (gtype glv1 =? GRANULE_STATE_TABLE);
          let entry1 := (g_data (gnorm glv1)) @ idx1 in
          rely is_int64 entry1;
          let phys1 := __entry_to_phys entry1 3 in
          let lv2_gidx := __addr_to_gidx phys1 in
          rely is_int64 phys1;
          if (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx) then
            (* level 2 valid, hold level 2 lock *)
            let glv2 := (gs st) @ lv2_gidx in
            rely (tbl_level (gaux glv2) =? 2);
            rely prop_dec (glock glv2 = None);
            if level =? 2 then
              (* walk until level 2 *)
              repl_create_table lv2_gidx idx2 rtt_addr rtt_gidx st
            else None
          else (* level 2 invalid *) Some (st, 1)
      else (* level 1 invalid *) Some (st, 1).

Definition repl_destroy_table (llt_gidx: Z) (idx: Z) (st: State) :=
  let gn_llt := (gs st) @ llt_gidx in
  rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
  let entry := (g_data (gnorm gn_llt)) @ idx in
  rely is_int64 entry;
  let phys := __entry_to_phys entry 3 in
  let rtt_gidx := __addr_to_gidx phys in
  rely is_int64 phys;
  if (__entry_is_table entry) && (GRANULE_ALIGNED phys) && (is_gidx rtt_gidx) then
    let gn_rtt := (gs st) @ rtt_gidx in
    rely prop_dec (glock gn_rtt = None);
    if (g_refcount (ginfo gn_rtt)) =? 1 then
      let gn_llt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: (g_data (gnorm gn_llt)) # idx == 0}}
                    {ginfo : (ginfo gn_llt) {g_refcount : g_refcount (ginfo gn_llt) - 1}} in
      let gn_rtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_refcount: (g_refcount (ginfo (gn_rtt))) - 1}
                                                    {g_tag: GRANULE_STATE_DELEGATED}} in
      Some (st {gs: (gs st) # llt_gidx == gn_llt' # rtt_gidx == gn_rtt'}, 0)
    else
      Some (st, 1)
  else Some (st, 1).

Definition repl_rtt_destroy lvl (cid: Z) root_gidx map_addr level st :=
  rely (level <=? lvl - 2);
  let idx0 := __addr_to_idx map_addr 0 in
  let idx1 := __addr_to_idx map_addr 1 in
  let idx2 := __addr_to_idx map_addr 2 in
  let idx3 := __addr_to_idx map_addr 3 in
  rely is_int64 idx0; rely is_int64 idx1; rely is_int64 idx2; rely is_int64 idx3;
  (* hold root lock *)
  rely is_gidx root_gidx;
  let groot := (gs st) @ root_gidx in
  rely (tbl_level (gaux groot) =? 0);
  rely prop_dec (glock groot = None);
  if level =? 0 then
    (* walk until root *)
    repl_destroy_table root_gidx idx0 st
  else
    (* walk deeper root *)
    rely (level >? 0);
    rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
    rely (gtype groot =? GRANULE_STATE_TABLE);
    let entry0 := (g_data (gnorm groot)) @ idx0 in
      rely is_int64 entry0;
      let phys0 := __entry_to_phys entry0 3 in
      let lv1_gidx := __addr_to_gidx phys0 in
      rely is_int64 phys0;
      if (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx) then
        (* level 1 valid, hold level 1 lock *)
        let glv1 := (gs st) @ lv1_gidx in
        rely prop_dec (glock glv1 = None);
        rely (tbl_level (gaux glv1) =? 1);
        if level =? 1 then
          (* walk until level 1 *)
          repl_destroy_table lv1_gidx idx1 st
        else
          (* walk deeper level 1 *)
          rely (level >? 1);
          rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
          rely (gtype glv1 =? GRANULE_STATE_TABLE);
          let entry1 := (g_data (gnorm glv1)) @ idx1 in
          rely is_int64 entry1;
          let phys1 := __entry_to_phys entry1 3 in
          let lv2_gidx := __addr_to_gidx phys1 in
          rely is_int64 phys1;
          if (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx) then
            (* level 2 valid, hold level 2 lock *)
            let glv2 := (gs st) @ lv2_gidx in
            rely (tbl_level (gaux glv2) =? 2);
            rely prop_dec (glock glv2 = None);
            if level =? 2 then
              (* walk until level 2 *)
              repl_destroy_table lv2_gidx idx2 st
            else None
          else (* level 2 invalid *) Some (st, 1)
      else (* level 1 invalid *) Some (st, 1).

Definition rtt_walk rd_gidx map_addr gns :=
  let idx0 := __addr_to_idx map_addr 0 in
  let idx1 := __addr_to_idx map_addr 1 in
  let idx2 := __addr_to_idx map_addr 2 in
  let idx3 := __addr_to_idx map_addr 3 in
  let grd := gns @ rd_gidx in
  let root_gidx := g_rtt (gnorm grd) in
  let groot := gns @ root_gidx in
  let entry := (g_data (gnorm groot)) @ idx0 in
  if __entry_is_table entry then
    let lv1_gidx := __addr_to_gidx (__entry_to_phys entry 3) in
    let glv1 := gns @ lv1_gidx in
    let entry := (g_data (gnorm glv1)) @ idx1 in
    if __entry_is_table entry then
      let lv2_gidx := __addr_to_gidx (__entry_to_phys entry 3) in
      let glv2 := gns @ lv2_gidx in
      let entry := (g_data (gnorm glv2)) @ idx2 in
      if __entry_is_table entry then
        let lv3_gidx := __addr_to_gidx (__entry_to_phys entry 3) in
        let glv3 := gns @ lv3_gidx in
        let entry := (g_data (gnorm glv3)) @ idx3 in
        entry
      else -1
    else -1
  else -1.

Definition repl_copy_ns (cid: Z) gidx copy_type st :=
  let g := (gs st) @ gidx in
  let ns_data := g_data (gnorm g) in
  if (gpt st) @ gidx then Some (st, -1)
  else
    match copy_type with
    | WRITE_REC_RUN run =>
      let g' := g {gnorm: (gnorm g) {g_data: run}} in
      Some (st {gs: (gs st) # gidx == g'}, 0)
    | READ_DATA target_gidx =>
      let gt := (gs st) @ target_gidx in
      let g' := gt {gnorm: (gnorm g) {g_data: ns_data}} in
      Some (st {gs: (gs st) # target_gidx == g'}, 0)
    | _ => Some (st, (g_data (gnorm g)) @ 0)
    end.

Definition repl_ns_access_mem (cid: Z) (addr: Z) (val: Z) (st: State) :=
  rely ((MEM0_PHYS <=? addr) && (addr <? 4294967296));
  rely is_int64 val;
  let gidx := __addr_to_gidx addr in
  let ofst := addr mod 4096 in
  let g := (gs st) @ gidx in
  if (gpt st) @ gidx then
    Some (st, 0)
  else
    Some (st {gs: (gs st) # gidx == (g {gnorm: (gnorm g) {g_data: (g_data (gnorm g)) # ofst == val}})},
          (g_data (gnorm g)) @ ofst).

Definition repl_realm_access_mem (cid: Z) (rd_gidx rec_gidx: Z) (addr: Z) (val: Z) (st: State) :=
  rely ((MEM0_PHYS <=? addr) && (addr <? 4294967296));
  rely is_int64 val;
  let ipa_gidx := __addr_to_gidx addr in
  let data_gidx := (if tlbs st CPU_ID ipa_gidx =? 0 then
                      match rtts st rd_gidx ipa_gidx with
                      | (g, true) => g
                      | _ => 0
                      end
                    else tlbs st CPU_ID ipa_gidx)
  in
  if data_gidx =? 0
  then Some (st, 0)
  else
    rely is_gidx data_gidx;
    let gn := (gs st) @ data_gidx in
    let ofst := addr mod 4096 in
    Some (st {gs: (gs st) # data_gidx == (gn {gnorm: (gnorm gn) {g_data: (g_data (gnorm gn)) # ofst == val}})},
          (g_data (gnorm gn)) @ ofst).

Definition ereplay (lvl: Z) (st: State) (e: Event) :=
  match e with
  | EVT cid (ACQ gidx) => repl_acq lvl cid gidx st
  | EVT cid (REL gidx g') => repl_rel cid gidx g' st
  | EVT cid (INIT_RO gidx g_rec rec_idx) => repl_recro cid gidx g_rec rec_idx st
  | EVT cid (GET_GCNT gidx) => repl_get_gcnt cid gidx st
  | EVT cid (INC_GCNT gidx) => repl_inc_gcnt cid gidx st
  | EVT cid (DEC_RD_GCNT gidx) => repl_dec_rd_gcnt cid gidx st
  | EVT cid (DEC_REC_GCNT gidx g') => repl_dec_rec_gcnt cid gidx g' st
  | EVT cid (RECL gidx idx t) => repl_recl cid gidx idx t st
  | EVT cid (ACQ_GPT gidx) => repl_acq_gpt cid gidx st
  | EVT cid (REL_GPT gidx secure) => repl_rel_gpt cid gidx secure st
  | EVT cid (RTT_WALK root_gidx map_addr level) =>
    repl_rtt_walk lvl cid root_gidx map_addr level st
  | EVT cid (RTT_CREATE root_gidx map_addr level rtt_addr) =>
    repl_rtt_create lvl cid root_gidx map_addr level rtt_addr st
  | EVT cid (RTT_DESTROY root_gidx map_addr level) =>
    repl_rtt_destroy lvl cid root_gidx map_addr level st
  | EVT cid (COPY_NS gidx t) => repl_copy_ns cid gidx t st
  | EVT cid (NS_ACCESS_MEM addr val) => repl_ns_access_mem cid addr val st
  | EVT cid (REALM_ACCESS_MEM rd rec addr val) =>
    repl_realm_access_mem cid rd rec addr val st
  | _ => Some (st, 0)
  end.

Fixpoint replay lvl log st :=
  match log with
  | nil => Some st
  | e :: log' =>
    match replay lvl log' st with
    | Some st' =>
      match ereplay lvl st' e with
      | Some (st'', _) => Some st''
      | _ => None
      end
    | None => None
    end
  end.

Definition Repl lvl log := replay lvl log (empty_st lvl).
