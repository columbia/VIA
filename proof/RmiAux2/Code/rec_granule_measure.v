Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _data_size := 1%positive.
Definition _g := 2%positive.
Definition _granule := 3%positive.
Definition _rd := 4%positive.
Definition _rd__1 := 5%positive.
Definition _rec := 6%positive.
Definition _rec__1 := 7%positive.
Definition _reg := 8%positive.
Definition _ret := 9%positive.
Definition _size := 10%positive.

Definition rec_granule_measure_body :=
  (Ssequence
    (Scall None
      (Evar _measurement_extend_rec_header (Tfunction
                                             (Tcons (tptr Tvoid)
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil)) tvoid cc_default))
      ((Etempvar _rd (tptr Tvoid)) ::
       (Etempvar _rec (tptr Tvoid)) :: nil))
    (Ssequence
      (Scall None
        (Evar _measurement_extend_rec_regs (Tfunction
                                             (Tcons (tptr Tvoid)
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil)) tvoid cc_default))
        ((Etempvar _rd (tptr Tvoid)) ::
         (Etempvar _rec (tptr Tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar _measurement_extend_rec_pstate (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons
                                                     (tptr Tvoid)
                                                     Tnil)) tvoid cc_default))
          ((Etempvar _rd (tptr Tvoid)) ::
           (Etempvar _rec (tptr Tvoid)) :: nil))
        (Scall None
          (Evar _measurement_extend_rec_sysregs (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      Tnil)) tvoid cc_default))
          ((Etempvar _rd (tptr Tvoid)) ::
           (Etempvar _rec (tptr Tvoid)) :: nil)))))
.

Definition f_rec_granule_measure := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rd, (tptr Tvoid)) ::
                (_rec, (tptr Tvoid)) ::
                (_data_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := rec_granule_measure_body
|}.
