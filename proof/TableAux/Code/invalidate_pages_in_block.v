Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _i := 2%positive.
Definition _ret := 3%positive.

Definition invalidate_pages_in_block_body :=
  (Ssequence
    (Scall None (Evar _barrier (Tfunction Tnil tvoid cc_default)) nil)
    (Scall None
      (Evar _stage2_tlbi_ipa (Tfunction (Tcons tulong (Tcons tulong Tnil))
                               tvoid cc_default))
      ((Etempvar _addr tulong) :: (Econst_long (Int64.repr 2097152) tulong) ::
       nil)))
.

Definition f_invalidate_pages_in_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := invalidate_pages_in_block_body
|}.
