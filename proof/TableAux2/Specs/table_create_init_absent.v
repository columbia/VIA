Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_create_init_absent_spec (level: Z64) (llt_pte: Z64) (pte: Pointer) (g_rtt: Pointer) (adt: RData) : option RData :=
    match level, llt_pte with
    | VZ64 level, VZ64 llt_pte =>
      rely is_int64 llt_pte;
      if level =? 3 then
        let pa := __entry_to_phys llt_pte 2 in
        rely is_int64 pa;
        let pte_val := Z.lor (IPA_STATE_TO_PTE IPA_STATE_ABSENT) pa in
        rely is_int64 pte_val; rely is_int64 (pte_val + GRANULE_SIZE * PGTES_PER_TABLE);
        rely (peq (base pte) buffer_loc);
        rely (peq (base g_rtt) ginfo_loc);
        when gidx == (buffer (priv adt)) @ (offset pte);
        let rtt_gidx := offset g_rtt in
        rely is_gidx rtt_gidx;
        rely prop_dec (gidx = rtt_gidx);
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = Some CPU_ID);
        rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
        match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn)) 0 pte_val GRANULE_SIZE with
        | (table', _, _) =>
          let g' := gn {gnorm: (gnorm gn) {g_data: table'}} {ginfo: (ginfo gn) {g_refcount: (g_refcount (ginfo gn)) + 512}} in
          Some adt {share : (share adt) {gs : (gs (share adt)) # gidx == g'}}
        end
      else None
    end.

End Spec.

