(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond pf b m at_pos s =
    let head, i, tail = s_split_i at_pos s in
    let e, s =
      match i.i_node with
      | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
      | Swhile(e,s1) -> e, if b then s1.s_node@[i] else []
      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the targetted instruction is not a conditionnal")
    in
    let f_e = form_of_expr m e in
    let f_e = if b then f_e else f_not f_e in

    (stmt head, e, f_e, stmt (head @ s @ tail))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_r b at_pos tc =
    let hs = tc1_as_hoareS tc in
    let m  = EcMemory.memory hs.hs_m in
    let hd,_,e,s = gen_rcond !!tc b m at_pos hs.hs_s in
    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
    let concl2  = f_hoareS_r { hs with hs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_choare_rcond_r b at_pos c tc =
    let c = EcUtils.odfl f_true c in

    let chs = tc1_as_choareS tc in
    let m  = EcMemory.memory chs.chs_m in
    let hd,e_expr,e,s = gen_rcond !!tc b m at_pos chs.chs_s in
    let cost =
      EcFol.cost_sub_self
        chs.chs_co
        (EcFol.cost_of_expr c chs.chs_m e_expr) in
    let concl1  =
      f_hoareS chs.chs_m chs.chs_pr hd (f_and_simpl c e) in
    let concl2  = f_cHoareS_r { chs with chs_s = s;
                                         chs_co = cost; } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_r b at_pos tc =
    let bhs = tc1_as_bdhoareS tc in
    let m  = EcMemory.memory bhs.bhs_m in
    let hd,_,e,s = gen_rcond !!tc b m at_pos bhs.bhs_s in
    let concl1  = f_hoareS bhs.bhs_m bhs.bhs_pr hd e in
    let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_r side b at_pos tc =
    let es = tc1_as_equivS tc in
    let m,mo,s =
      match side with
      | `Left  -> es.es_ml,es.es_mr, es.es_sl
      | `Right -> es.es_mr,es.es_ml, es.es_sr in
    let hd,_,e,s = gen_rcond !!tc b EcFol.mhr at_pos s in
    let mo' = EcIdent.create "&m" in
    let s1 = Fsubst.f_subst_id in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory m) EcFol.mhr in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory mo) mo' in
    let pre1 = Fsubst.f_subst s1 es.es_pr in
    let concl1 =
      f_forall_mems [mo', EcMemory.memtype mo]
        (f_hoareS (EcFol.mhr, EcMemory.memtype m) pre1 hd e) in
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond   = FApi.t_low2 "hoare-rcond"   t_hoare_rcond_r
  let t_choare_rcond  = FApi.t_low3 "choare-rcond"  t_choare_rcond_r
  let t_bdhoare_rcond = FApi.t_low2 "bdhoare-rcond" t_bdhoare_rcond_r
  let t_equiv_rcond   = FApi.t_low3 "equiv-rcond"   t_equiv_rcond_r
end

(* -------------------------------------------------------------------- *)
let t_rcond side b at_pos c tc =
  let concl = FApi.tc1_goal tc in

  let check_none () = if c <> None then
      tc_error !!tc "optional cost is only for choare judgements" in

  match side with
  | None when is_bdHoareS concl ->
    check_none (); Low.t_bdhoare_rcond b at_pos tc
  | None when is_cHoareS concl  -> Low.t_choare_rcond b at_pos c tc
  | None ->
    check_none (); Low.t_hoare_rcond b at_pos tc
  | Some side ->
    check_none (); Low.t_equiv_rcond side b at_pos tc

let process_rcond side b at_pos c tc =
  let c = EcUtils.omap (fun c ->
      EcProofTyping.tc1_process_Xhl_formula tc c) c in

  t_rcond side b at_pos c tc
