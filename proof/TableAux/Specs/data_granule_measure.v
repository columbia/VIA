Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition data_granule_measure_spec (rd: Pointer) (data: Pointer) (offset': Z64) (data_size: Z64) (adt: RData) : option RData :=
    match offset', data_size with
    | VZ64 offset', VZ64 data_size =>
      rely is_int64 data_size; rely is_int64 offset';
      rely (peq (base rd) buffer_loc);
      rely (peq (base data) buffer_loc);
      when rd_gidx == ((buffer (priv adt)) @ (offset rd));
      when data_gidx == ((buffer (priv adt)) @ (offset data));
      rely (negb (rd_gidx =? data_gidx));
      let gn_rd := (gs (share adt)) @ rd_gidx in
      let gn_data := (gs (share adt)) @ data_gidx in
      rely prop_dec (glock gn_rd = Some CPU_ID);
      rely prop_dec (glock gn_data = Some CPU_ID);
      rely (g_tag (ginfo gn_rd) =? GRANULE_STATE_RD);
      rely (gtype gn_rd =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_data) =? GRANULE_STATE_DATA);
      let gn_rd' := gn_rd {gnorm: (gnorm gn_rd)
                                    {g_measurement_ctx:
                                      if (g_measurement_algo (gnorm gn_rd)) =? MEASUREMENT_ALGO_SHA256 then
                                        measure_extend_data
                                          (measure_extend_data_header
                                              (g_measurement_ctx (gnorm gn_rd))) (g_data (gnorm gn_data))
                                      else (g_measurement_ctx (gnorm gn_rd))}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # rd_gidx == gn_rd'}}
    end.

End Spec.

