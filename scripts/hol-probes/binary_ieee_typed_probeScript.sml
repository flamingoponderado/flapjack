(* Typed source declarations for binary_ieee (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/src/floating-point") ::
  !loadPath;
load "binary_ieeeTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "∀*";
           app (fn v =>
             let val ts = type_to_string (type_of v)
                 val ts = if String.sub (ts, 0) = #":"
                          then String.extract (ts, 1, NONE) else ts
             in print "("; print (#1 (dest_var v));
                print " :"; print ts; print ") " end) fvs;
           print ". ");
     app (fn h => (print_term h; print " ==> ")) (hyp th);
     print_term (concl th); print "\n")
  end;

val thy = "binary_ieee";
val datatypeNames =
  List.map (fn n => String.substring (n, 0, String.size n - 6))
    (List.filter (fn n => String.isSuffix "_Axiom" n)
      (List.map #1 (DB.theorems thy)));

fun ctorsOf d =
  let
    fun try n =
      (TypeBase.constructors_of
         (mk_type (d, List.tabulate (n, fn _ => alpha)))
       handle _ => [])
    fun first [] = []
      | first (n :: ns) =
          let val cs = try n in if null cs then first ns else cs end
  in first [0, 1, 2, 3, 4] end;

val allCtors = List.concat (List.map ctorsOf datatypeNames);

fun emitDatatype label name =
  let val cs = ctorsOf name in
    if null cs then false
    else
      (print (label ^ "=");
       print (String.concatWith "; "
         (List.map (fn c =>
            let val (n, t) = dest_const c
            in n ^ ":" ^ type_to_string t end) cs));
       print "\n"; true)
  end;

fun ctorType name =
  case List.filter (fn c => #1 (dest_const c) = name) allCtors of
    [] => NONE
  | c :: _ => SOME (type_to_string (#2 (dest_const c)));

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE =>
      if emitDatatype label name then ()
      else case ctorType name of
        SOME s => (print (label ^ "="); print s; print "\n")
      | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

val _ = emit "float_typed" "float";
val _ = emit "float_compare_typed" "float_compare";
val _ = emit "float_abs_def_typed" "float_abs_def";
val _ = emit "float_compare_def_typed" "float_compare_def";
val _ = emit "float_equal_def_typed" "float_equal_def";
val _ = emit "float_greater_equal_def_typed" "float_greater_equal_def";
val _ = emit "float_greater_than_def_typed" "float_greater_than_def";
val _ = emit "float_is_finite_def_typed" "float_is_finite_def";
val _ = emit "float_is_infinite_def_typed" "float_is_infinite_def";
val _ = emit "float_is_nan_def_typed" "float_is_nan_def";
val _ = emit "float_is_normal_def_typed" "float_is_normal_def";
val _ = emit "float_is_signalling_def_typed" "float_is_signalling_def";
val _ = emit "float_is_subnormal_def_typed" "float_is_subnormal_def";
val _ = emit "float_is_zero_def_typed" "float_is_zero_def";
val _ = emit "float_less_equal_def_typed" "float_less_equal_def";
val _ = emit "float_less_than_def_typed" "float_less_than_def";
val _ = emit "float_negate_def_typed" "float_negate_def";
val _ = emit "float_to_real_def_typed" "float_to_real_def";
val _ = emit "float_value_def_typed" "float_value_def";
val _ = emit "float_add_def_typed" "float_add_def";
val _ = emit "float_div_def_typed" "float_div_def";
val _ = emit "float_mul_def_typed" "float_mul_def";
val _ = emit "float_mul_add_def_typed" "float_mul_add_def";
val _ = emit "float_sub_def_typed" "float_sub_def";
val _ = emit "float_to_int_def_typed" "float_to_int_def";
val _ = emit "flags_typed" "flags";
val _ = emit "fp_op_typed" "fp_op";
val _ = emit "rounding_typed" "rounding";
val _ = emit "check_for_signalling_def_typed" "check_for_signalling_def";
val _ = emit "clear_flags_def_typed" "clear_flags_def";
val _ = emit "dividezero_flags_def_typed" "dividezero_flags_def";
val _ = emit "float_bottom_def_typed" "float_bottom_def";
val _ = emit "float_minus_infinity_def_typed" "float_minus_infinity_def";
val _ = emit "float_minus_min_def_typed" "float_minus_min_def";
val _ = emit "float_minus_zero_def_typed" "float_minus_zero_def";
val _ = emit "float_plus_infinity_def_typed" "float_plus_infinity_def";
val _ = emit "float_plus_min_def_typed" "float_plus_min_def";
val _ = emit "float_plus_zero_def_typed" "float_plus_zero_def";
val _ = emit "float_some_qnan_def_typed" "float_some_qnan_def";
val _ = emit "float_top_def_typed" "float_top_def";
val _ = emit "invalidop_flags_def_typed" "invalidop_flags_def";
val _ = emit "float_value_typed" "float_value";
val _ = emit "closest_def_typed" "closest_def";
val _ = emit "closest_such_def_typed" "closest_such_def";
val _ = emit "largest_def_typed" "largest_def";
val _ = emit "float_round_def_typed" "float_round_def";
val _ = emit "float_round_with_flags_def_typed" "float_round_with_flags_def";
val _ = emit "float_sqrt_def_typed" "float_sqrt_def";
val _ = emit "threshold_def_typed" "threshold_def";
val _ = emit "is_closest_def_typed" "is_closest_def";
val _ = emit "real_to_float_def_typed" "real_to_float_def";
val _ = emit "real_to_float_with_flags_def_typed" "real_to_float_with_flags_def";
val _ = emit "round_def_typed" "round_def";
val _ = emit "is_integral_def_typed" "is_integral_def";
val _ = emit "float_is_integral_def_typed" "float_is_integral_def";
val _ = emit "ULP_def_typed" "ULP_def";
val _ = emit "ulp_def_typed" "ulp_def";
val _ = emit "integral_round_def_typed" "integral_round_def";
val _ = emit "float_round_to_integral_def_typed" "float_round_to_integral_def";
val _ = emit "float_mul_sub_def_typed" "float_mul_sub_def";
val _ = emit "float_unordered_def_typed" "float_unordered_def";
val _ = emit "exponent_boundary_def_typed" "exponent_boundary_def";
val _ = emit "float_ulp_def_typed" "float_ulp_def";
val _ = emit "next_hi_def_typed" "next_hi_def";
val _ = emit "next_lo_def_typed" "next_lo_def";

val _ = OS.Process.exit OS.Process.success;
