Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _data := 1%positive.
Definition _data_size := 2%positive.
Definition _g := 3%positive.
Definition _granule := 4%positive.
Definition _offset := 5%positive.
Definition _rd := 6%positive.
Definition _rd__1 := 7%positive.
Definition _ret := 8%positive.
Definition _size := 9%positive.

Definition data_granule_measure_body :=
  (Ssequence
    (Scall None
      (Evar _measurement_extend_data_header (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tulong Tnil)) tvoid
                                              cc_default))
      ((Etempvar _rd (tptr Tvoid)) ::
       (Etempvar _offset tulong) :: nil))
    (Scall None
      (Evar _measurement_extend_data (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons (tptr Tvoid) Tnil)) tvoid
                                       cc_default))
      ((Etempvar _rd (tptr Tvoid)) ::
       (Etempvar _data (tptr Tvoid)) :: nil)))
.

Definition f_data_granule_measure := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rd, (tptr Tvoid)) ::
                (_data, (tptr Tvoid)) :: (_offset, tulong) ::
                (_data_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := data_granule_measure_body
|}.
