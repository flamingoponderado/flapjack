(* Flapjack-side certificates against the pinned original HOL definitions.
   Candidate discovery is untrusted; only closed kernel proofs yield results.
   This finite integer converter does not alter the HOL reference sources. *)
load "binary_ieeeTheory"; load "binary_ieeeLib"; load "realLib"; load "wordsLib";
structure FlapjackDirected = struct
open HolKernel Parse boolLib bossLib binary_ieeeTheory;
val closest_unique = prove (
 ``!s x (a:('t,'w) float).
    is_closest s x a /\
    (!b. is_closest s x b ==> b = a) ==> closest s x = a``,
 rw [closest_def, closest_such_def] >> SELECT_ELIM_TAC >> rw [] >> metis_tac []);
val below_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ float_to_real a <= x /\
    (!b:('t,'w) float. float_is_finite b /\ float_to_real b <= x ==>
         float_to_real b <= float_to_real a) ==>
    is_closest {b | float_is_finite b /\ float_to_real b <= x} x a``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 metis_tac [realLib.REAL_ARITH ``(a:real) <= x /\ b <= a ==> abs(a-x) <= abs(b-x)``]);
val above_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ x <= float_to_real a /\
    (!b:('t,'w) float. float_is_finite b /\ x <= float_to_real b ==>
         float_to_real a <= float_to_real b) ==>
    is_closest {b | float_is_finite b /\ x <= float_to_real b} x a``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 metis_tac [realLib.REAL_ARITH ``x <= (a:real) /\ a <= b ==> abs(a-x) <= abs(b-x)``]);
val below_closest_value = prove (
 ``!x (a:('t,'w) float) (b:('t,'w) float).
    is_closest {c | float_is_finite c /\ float_to_real c <= x} x a /\
    is_closest {c | float_is_finite c /\ float_to_real c <= x} x b ==>
    float_to_real a = float_to_real b``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 metis_tac [realLib.REAL_ARITH ``(a:real) <= x /\ b <= x /\ abs(a-x) <= abs(b-x) /\ abs(b-x) <= abs(a-x) ==> a=b``]);
val above_closest_value = prove (
 ``!x (a:('t,'w) float) (b:('t,'w) float).
    is_closest {c | float_is_finite c /\ x <= float_to_real c} x a /\
    is_closest {c | float_is_finite c /\ x <= float_to_real c} x b ==>
    float_to_real a = float_to_real b``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 metis_tac [realLib.REAL_ARITH ``x <= (a:real) /\ x <= b /\ abs(a-x) <= abs(b-x) /\ abs(b-x) <= abs(a-x) ==> a=b``]);
val closest_spec = prove (
 ``!s x (a:('t,'w) float). is_closest s x a ==> is_closest s x (closest s x)``,
 rw [closest_def, closest_such_def] >> SELECT_ELIM_TAC >> rw [] >> metis_tac []);
val below_choice_records = prove (
 ``!x (a:('t,'w) float).
    is_closest {c | float_is_finite c /\ float_to_real c <= x} x a ==>
    let b = closest {c | float_is_finite c /\ float_to_real c <= x} x in
      b = a \/ (float_is_zero b /\ float_is_zero a)``,
 rw [] >> metis_tac [closest_spec, below_closest_value, float_to_real_eq]);
val above_choice_records = prove (
 ``!x (a:('t,'w) float).
    is_closest {c | float_is_finite c /\ x <= float_to_real c} x a ==>
    let b = closest {c | float_is_finite c /\ x <= float_to_real c} x in
      b = a \/ (float_is_zero b /\ float_is_zero a)``,
 rw [] >> metis_tac [closest_spec, above_closest_value, float_to_real_eq]);
val zero_selected_records = prove (
 ``!a b (z:('t,'w) float).
     (b = a \/ (float_is_zero b /\ float_is_zero a)) ==>
     (if float_is_zero b then z else b) = (if float_is_zero a then z else a)``,
 rw [] >> fs []);
val directed_positive_finite = prove (
 ``!x (a:('t,'w) float) toneg.
    ~(x < -largest (:'t # 'w)) /\ ~(x > largest (:'t # 'w)) /\
    is_closest {c | float_is_finite c /\ x <= float_to_real c} x a ==>
    float_round roundTowardPositive toneg x =
      if float_is_zero a then
        (if toneg then float_minus_zero (:'t # 'w) else float_plus_zero (:'t # 'w))
      else a``,
 rw [float_round_def, round_def, realTheory.real_ge] >>
 metis_tac [above_choice_records, zero_selected_records]);
val directed_negative_finite = prove (
 ``!x (a:('t,'w) float) toneg.
    ~(x < -largest (:'t # 'w)) /\ ~(x > largest (:'t # 'w)) /\
    is_closest {c | float_is_finite c /\ float_to_real c <= x} x a ==>
    float_round roundTowardNegative toneg x =
      if float_is_zero a then
        (if toneg then float_minus_zero (:'t # 'w) else float_plus_zero (:'t # 'w))
      else a``,
 rw [float_round_def, round_def] >>
 metis_tac [below_choice_records, zero_selected_records]);
val below_ulp_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ float_to_real a <= x /\
    x - float_to_real a < ULP (a.Exponent, (:'t)) /\
    (!b:('t,'w) float. float_is_finite b /\ float_to_real b <= x ==>
       ~exponent_boundary b a) ==>
    is_closest {b | float_is_finite b /\ float_to_real b <= x} x a``,
 rpt strip_tac >> match_mp_tac below_closest >> simp [] >>
 rpt strip_tac >>
 metis_tac [diff_float_ULP, realLib.REAL_ARITH
   ``a <= x /\ b <= x /\ x-a < u /\
     (a <> b ==> u <= abs(a-b)) ==> b <= (a:real)``]);
val above_ulp_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ x <= float_to_real a /\
    float_to_real a - x < ULP (a.Exponent, (:'t)) /\
    (!b:('t,'w) float. float_is_finite b /\ x <= float_to_real b ==>
       ~exponent_boundary b a) ==>
    is_closest {b | float_is_finite b /\ x <= float_to_real b} x a``,
 rpt strip_tac >> match_mp_tac above_closest >> simp [] >>
 rpt strip_tac >>
 metis_tac [diff_float_ULP, realLib.REAL_ARITH
   ``x <= a /\ x <= b /\ a-x < u /\
     (a <> b ==> u <= abs(a-b)) ==> (a:real) <= b``]);
val exact_below_closest = prove (
 ``!a:('t,'w) float. float_is_finite a ==>
   is_closest {b | float_is_finite b /\ float_to_real b <= float_to_real a}
     (float_to_real a) a``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 simp [realTheory.ABS_POS]);
val exact_above_closest = prove (
 ``!a:('t,'w) float. float_is_finite a ==>
   is_closest {b | float_is_finite b /\ float_to_real a <= float_to_real b}
     (float_to_real a) a``,
 rw [is_closest_def, pred_setTheory.GSPECIFICATION] >>
 simp [realTheory.ABS_POS]);
val significand_nonzero_no_boundary = prove (
 ``!a b:('t,'w) float.
    a.Significand <> 0w ==> ~exponent_boundary b a``,
 simp [exponent_boundary_def]);
val above_nonboundary_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ x <= float_to_real a /\
    float_to_real a - x < ULP (a.Exponent, (:'t)) /\
    a.Significand <> 0w ==>
    is_closest {b | float_is_finite b /\ x <= float_to_real b} x a``,
 metis_tac [above_ulp_closest, significand_nonzero_no_boundary]);
val below_nonboundary_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ float_to_real a <= x /\
    x - float_to_real a < ULP (a.Exponent, (:'t)) /\
    a.Significand <> 0w ==>
    is_closest {b | float_is_finite b /\ float_to_real b <= x} x a``,
 metis_tac [below_ulp_closest, significand_nonzero_no_boundary]);
(* Candidate discovery is untrusted: every supplied candidate's arithmetic
   obligations are proved by original HOL EVAL before producing an equality. *)
fun directed_nonboundary_certificate upward toneg x a = let
 val closest_rule = ISPECL [x,a]
   (if upward then above_nonboundary_closest else below_nonboundary_closest)
 val numeric = EQT_ELIM (EVAL (fst (dest_imp (concl closest_rule))))
 val closest_th = MATCH_MP closest_rule numeric
 val round_rule = ISPECL [x,a,toneg]
   (if upward then directed_positive_finite else directed_negative_finite)
 val premises = strip_conj (fst (dest_imp (concl round_rule)))
 val range_th = EQT_ELIM (EVAL (mk_conj (hd premises, hd (tl premises))))
 val result = MATCH_MP round_rule
   (LIST_CONJ [CONJUNCT1 range_th,CONJUNCT2 range_th,closest_th])
 in CONV_RULE (RAND_CONV EVAL) result end;
fun directed_exact_certificate upward toneg x a = let
 val finite_th = EQT_ELIM (EVAL ``float_is_finite ^a``)
 val closest_th0 = MATCH_MP (ISPEC a
   (if upward then exact_above_closest else exact_below_closest)) finite_th
 val value_th = EVAL ``float_to_real ^a``
 val closest_th = CONV_RULE (DEPTH_CONV (REWR_CONV value_th)) closest_th0
 val expected_x = rhs (concl value_th)
 val x_th = EVAL x
 val _ = if aconv (rhs (concl x_th)) expected_x then ()
   else raise Fail "exact certificate candidate has wrong value"
 val round_rule = ISPECL [expected_x,a,toneg]
   (if upward then directed_positive_finite else directed_negative_finite)
 val premises = strip_conj (fst (dest_imp (concl round_rule)))
 val range_th = EQT_ELIM (EVAL (mk_conj (hd premises,hd (tl premises))))
 val result = MATCH_MP round_rule
   (LIST_CONJ [CONJUNCT1 range_th,CONJUNCT2 range_th,closest_th])
 val reduced = CONV_RULE (RAND_CONV EVAL) result
 in CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (SYM x_th)))) reduced end;
val below_boundary_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ float_to_real a <= x /\
    x - float_to_real a < ULP (a.Exponent, (:'t)) /\
    (!b:('t,'w) float. exponent_boundary b a ==>
       float_to_real b <= float_to_real a) ==>
    is_closest {b | float_is_finite b /\ float_to_real b <= x} x a``,
 rpt strip_tac >> match_mp_tac below_closest >> simp [] >>
 rpt strip_tac >> Cases_on `exponent_boundary b a` >- metis_tac [] >>
 metis_tac [diff_float_ULP, realLib.REAL_ARITH
   ``a <= x /\ b <= x /\ x-a < u /\
     (a <> b ==> u <= abs(a-b)) ==> b <= (a:real)``]);
val above_boundary_closest = prove (
 ``!x (a:('t,'w) float).
    float_is_finite a /\ x <= float_to_real a /\
    float_to_real a - x < ULP (a.Exponent, (:'t)) /\
    (!b:('t,'w) float. exponent_boundary b a ==>
       float_to_real a <= float_to_real b) ==>
    is_closest {b | float_is_finite b /\ x <= float_to_real b} x a``,
 rpt strip_tac >> match_mp_tac above_closest >> simp [] >>
 rpt strip_tac >> Cases_on `exponent_boundary b a` >- metis_tac [] >>
 metis_tac [diff_float_ULP, realLib.REAL_ARITH
   ``x <= a /\ x <= b /\ a-x < u /\
     (a <> b ==> u <= abs(a-b)) ==> (a:real) <= b``]);
fun directed_boundary_certificate upward toneg x a boundary_order = let
 val closest_rule = ISPECL [x,a]
   (if upward then above_boundary_closest else below_boundary_closest)
 val ps = strip_conj (fst (dest_imp (concl closest_rule)))
 val numeric = map (fn p => EQT_ELIM (EVAL p)) (List.take(ps,3))
 val boundary_th = prove (List.nth(ps,3),
   metis_tac [boundary_order,realTheory.real_gt,realTheory.REAL_LT_IMP_LE])
 val closest_th = MATCH_MP closest_rule (LIST_CONJ (numeric @ [boundary_th]))
 val round_rule = ISPECL [x,a,toneg]
   (if upward then directed_positive_finite else directed_negative_finite)
 val rs = strip_conj (fst (dest_imp (concl round_rule)))
 val ranges = map (fn p => EQT_ELIM (EVAL p)) (List.take(rs,2))
 val result = MATCH_MP round_rule (LIST_CONJ (ranges @ [closest_th]))
 in CONV_RULE (RAND_CONV EVAL) result end;
fun boundary_field_certificate less target a = let
 val b = mk_var ("b",type_of a)
 val ae = binary_ieeeSyntax.mk_float_exponent a
 val be = binary_ieeeSyntax.mk_float_exponent b
 val en = numSyntax.dest_numeral (rhs (concl (EVAL (wordsSyntax.mk_w2n ae))))
 val pn = numSyntax.mk_numeral (Arbnum.-(en,Arbnum.one))
 val pw = wordsSyntax.mk_n2w (pn,wordsSyntax.dim_of ae)
 val ne = mk_eq (wordsSyntax.mk_w2n be,pn)
 val we = mk_eq (be,pw)
 val pw_th = EVAL (wordsSyntax.mk_w2n pw)
 val br = binary_ieeeSyntax.mk_float_to_real b
 val order = if less then realSyntax.mk_less(br,target)
   else realSyntax.mk_less(target,br)
 val goal = mk_forall (b,mk_imp (``exponent_boundary ^b ^a``,order))
 in prove (goal,
   rw [exponent_boundary_def] >>
   full_simp_tac (srw_ss() ++ wordsLib.SIZES_ss) [] >>
   op by ([ANTIQUOTE ne],decide_tac) >> op by ([ANTIQUOTE we],metis_tac [wordsTheory.w2n_11,pw_th]) >>
   fs [float_to_real_def] >> EVAL_TAC) end;
fun directed_candidate_certificate upward toneg x a = let
 val ar = binary_ieeeSyntax.mk_float_to_real a
 val exact = rhs (concl (EVAL (mk_eq(ar,x)))) ~~ boolSyntax.T
 val nonzero = rhs (concl (EVAL ``^a.Significand <> 0w``)) ~~ boolSyntax.T
 val negative = rhs (concl (EVAL ``^a.Sign = 1w``)) ~~ boolSyntax.T
 in if exact then directed_exact_certificate upward toneg x a
 else if nonzero then directed_nonboundary_certificate upward toneg x a
 else if upward = negative then
   directed_boundary_certificate upward toneg x a
     (boundary_field_certificate (not negative) ar a)
 else let
   val boundary_order = boundary_field_certificate upward x a
   val rule = ISPECL [x,a] (if upward then above_ulp_closest else below_ulp_closest)
   val ps = strip_conj (fst (dest_imp (concl rule)))
   val numeric = map (fn p => EQT_ELIM (EVAL p)) (List.take(ps,3))
   val exclusion = prove (List.nth(ps,3),
     metis_tac [boundary_order,realTheory.REAL_NOT_LE])
   val closest_th = MATCH_MP rule (LIST_CONJ (numeric @ [exclusion]))
   val round_rule = ISPECL [x,a,toneg]
     (if upward then directed_positive_finite else directed_negative_finite)
   val rs = strip_conj (fst (dest_imp (concl round_rule)))
   val ranges = map (fn p => EQT_ELIM (EVAL p)) (List.take(rs,2))
   val result = MATCH_MP round_rule (LIST_CONJ (ranges @ [closest_th]))
 in CONV_RULE (RAND_CONV EVAL) result end end;
fun discover_directed_candidate upward x (t,w) = let
 val tm = binary_ieeeSyntax.mk_float_round
   (binary_ieeeSyntax.roundTowardZero_tm,``F``,x,t,w)
 val rtz = binary_ieeeLib.float_round_CONV tm
 val a = rhs (concl (EVAL (rhs (concl rtz))))
 val exact = rhs (concl (EVAL (mk_eq(binary_ieeeSyntax.mk_float_to_real a,x)))) ~~ boolSyntax.T
 val ((ti,wi),(negative,e,f)) = binary_ieeeSyntax.triple_of_float a
 in if exact orelse upward = negative then a
 else let
   val f1 = Arbnum.+(f,Arbnum.one)
   val limit = Arbnum.pow(Arbnum.fromInt 2,Arbnum.fromInt ti)
   val (e1,f2) = if f1 = limit then (Arbnum.+(e,Arbnum.one),Arbnum.zero)
     else (e,f1)
 in binary_ieeeSyntax.float_of_triple ((ti,wi),(negative,e1,f2)) end end;
fun certified_directed_float_round_CONV tm = let
 val (mode,toneg,x,t,w) = binary_ieeeSyntax.dest_float_round tm
 val upward = if mode ~~ binary_ieeeSyntax.roundTowardPositive_tm then true
   else if mode ~~ binary_ieeeSyntax.roundTowardNegative_tm then false
   else raise Fail "certified directed converter expects up/down"
 val a = discover_directed_candidate upward x (t,w)
 val th = directed_candidate_certificate upward toneg x a
 val _ = if aconv (lhs (concl th)) tm then ()
   else raise Fail "directed certificate has wrong input"
 in th end;

end;
