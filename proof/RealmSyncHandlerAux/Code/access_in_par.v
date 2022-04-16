Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _address := 2%positive.
Definition _esr := 3%positive.
Definition _g := 4%positive.
Definition _i := 5%positive.
Definition _par_base := 6%positive.
Definition _par_end := 7%positive.
Definition _rec := 8%positive.
Definition _rec__1 := 9%positive.
Definition _ret := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.
Definition _t'3 := 13%positive.
Definition _t'4 := 14%positive.

Definition access_in_par_body :=
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _access_len (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _esr tulong) :: nil))
        (Scall (Some _t'2)
          (Evar _get_rec_par_base (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    tulong cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil)))
      (Sifthenelse (Ebinop Ogt
                     (Ebinop Oadd (Etempvar _address tulong)
                       (Etempvar _t'1 tuint) tulong) (Etempvar _t'2 tulong)
                     tint)
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_rec_par_end (Tfunction
                                     (Tcons (tptr Tvoid) Tnil)
                                     tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Sset _t'3
            (Ecast
              (Ebinop Olt (Etempvar _address tulong) (Etempvar _t'4 tulong)
                tint) tbool)))
        (Sset _t'3 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'3 tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))))
.

Definition f_access_in_par := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_address, tulong) :: (_esr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tulong) :: (_t'3, tint) :: (_t'2, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := access_in_par_body
|}.
