Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_features_spec0 (rec: Pointer) (psci_func_id: Z) (adt: RData) : option RData :=
    match rec, psci_func_id with
    | (_rec_base, _rec_ofst), _psci_func_id =>
      if (_psci_func_id =? 2214592513) then
        let _t'1 := 1 in
        let _t'2 := 1 in
        let _t'3 := 1 in
        let _t'4 := 1 in
        let _t'5 := 1 in
        let _t'6 := 1 in
        let _t'7 := 1 in
        let _t'8 := 1 in
        let _t'9 := 1 in
        let _ret := 0 in
        rely is_int64 _ret;
        when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
        Some adt
      else
        let _t'1 := (_psci_func_id =? 3288334337) in
        if _t'1 then
          let _t'2 := 1 in
          let _t'3 := 1 in
          let _t'4 := 1 in
          let _t'5 := 1 in
          let _t'6 := 1 in
          let _t'7 := 1 in
          let _t'8 := 1 in
          let _t'9 := 1 in
          let _ret := 0 in
          rely is_int64 _ret;
          when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
          Some adt
        else
          let _t'2 := (_psci_func_id =? 2214592514) in
          if _t'2 then
            let _t'3 := 1 in
            let _t'4 := 1 in
            let _t'5 := 1 in
            let _t'6 := 1 in
            let _t'7 := 1 in
            let _t'8 := 1 in
            let _t'9 := 1 in
            let _ret := 0 in
            rely is_int64 _ret;
            when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
            Some adt
          else
            let _t'3 := (_psci_func_id =? 2214592515) in
            if _t'3 then
              let _t'4 := 1 in
              let _t'5 := 1 in
              let _t'6 := 1 in
              let _t'7 := 1 in
              let _t'8 := 1 in
              let _t'9 := 1 in
              let _ret := 0 in
              rely is_int64 _ret;
              when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
              Some adt
            else
              let _t'4 := (_psci_func_id =? 3288334339) in
              if _t'4 then
                let _t'5 := 1 in
                let _t'6 := 1 in
                let _t'7 := 1 in
                let _t'8 := 1 in
                let _t'9 := 1 in
                let _ret := 0 in
                rely is_int64 _ret;
                when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                Some adt
              else
                let _t'5 := (_psci_func_id =? 2214592516) in
                if _t'5 then
                  let _t'6 := 1 in
                  let _t'7 := 1 in
                  let _t'8 := 1 in
                  let _t'9 := 1 in
                  let _ret := 0 in
                  rely is_int64 _ret;
                  when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                  Some adt
                else
                  let _t'6 := (_psci_func_id =? 3288334340) in
                  if _t'6 then
                    let _t'7 := 1 in
                    let _t'8 := 1 in
                    let _t'9 := 1 in
                    let _ret := 0 in
                    rely is_int64 _ret;
                    when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                    Some adt
                  else
                    let _t'7 := (_psci_func_id =? 2214592520) in
                    if _t'7 then
                      let _t'8 := 1 in
                      let _t'9 := 1 in
                      let _ret := 0 in
                      rely is_int64 _ret;
                      when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                      Some adt
                    else
                      let _t'8 := (_psci_func_id =? 2214592521) in
                      if _t'8 then
                        let _t'9 := 1 in
                        let _ret := 0 in
                        rely is_int64 _ret;
                        when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                        Some adt
                      else
                        let _t'9 := (_psci_func_id =? 2214592522) in
                        if _t'9 then
                          let _ret := 0 in
                          rely is_int64 _ret;
                          when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                          Some adt
                        else
                          let _ret := 4294967295 in
                          rely is_int64 _ret;
                          when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
                          Some adt
     end
    .

End SpecLow.
