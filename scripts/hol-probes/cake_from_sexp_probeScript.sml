load "fromSexpTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show label tm =
  (print label; print "="; print_term (rhs (concl (EVAL tm))); print "\n");
fun showSimp label tm =
  (print label; print "="; print_term (rhs (concl (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [])) (EVAL tm)))); print "\n");
fun showDef label th =
  (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n");
val _ = show "control" ``MAP fromSexp$decode_control
  ["abc"; "\\\\"; "\\00"; "\\1F"; "\\7F"; "\\FF"; "\\20"; "\\5C";
   "\\1f"; "\\FG"; "\\"; [CHR 31]; "x\\00y"]``;
val _ = (print "decode_encode_control_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.decode_encode_control);
  print "\n");
val _ = (print "encode_decode_control_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.encode_decode_control);
  print "\n");
val _ = (print "sexpid_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexpid_def);
  print "\n");
val _ = (print "sexptype_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexptype_def);
  print "\n");
val _ = (print "sexppat_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexppat_def);
  print "\n");
val _ = (print "sexpexp_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexpexp_def);
  print "\n");
val _ = (print "sexptype_def_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexptype_def_def);
  print "\n");
val _ = (print "sexptype_def_type=";
  print_type (type_of ``fromSexp$sexptype_def``);
  print "\n");
val _ = (print "sexpdec_typed=";
  Lib.with_flag (Globals.show_types,true) print_term (concl fromSexpTheory.sexpdec_def);
  print "\n");
val _ = (print "sexp_constructors_typed=";
  print_type (type_of ``(SX_CONS, SX_SYM, SX_NUM, SX_STR)``);
  print "\n");
val _ = showDef "decode_control_typed" fromSexpTheory.decode_control_def;
val _ = showDef "odestSEXSTR_typed" fromSexpTheory.odestSEXSTR_def;
val _ = showDef "sexplist_typed" fromSexpTheory.sexplist_def;
val _ = showDef "sexppair_typed" fromSexpTheory.sexppair_def;
val _ = showDef "sexpopt_typed" fromSexpTheory.sexpopt_def;
val _ = showDef "sexplit_typed" fromSexpTheory.sexplit_def;
val _ = showDef "sexplocpt_typed" fromSexpTheory.sexplocpt_def;
val _ = showDef "sexplocn_typed" fromSexpTheory.sexplocn_def;
val _ = show "lists" ``MAP (fromSexp$sexplist fromSexp$odestSXNUM)
  [⟪⟫; ⟪1; 2; 3⟫; ⟪1 • 2⟫; ⟪SX_STR "x"⟫]``;
val _ = show "option" ``MAP (fromSexp$sexpopt fromSexp$odestSXNUM)
  [SX_SYM "NONE"; ⟪SX_SYM "SOME"; 5⟫; ⟪SX_SYM "SOME"; 1; 2⟫; SX_SYM "SOME"]``;
val _ = show "identifier" ``MAP (fromSexp$sexpid fromSexp$odestSEXSTR)
  [⟪SX_SYM "Short"; SX_STR "x"⟫;
   ⟪SX_SYM "Long"; SX_STR "M"; ⟪SX_SYM "Short"; SX_STR "x"⟫⟫;
   ⟪SX_SYM "Long"; SX_STR "M"; SX_SYM "x"⟫;
   ⟪SX_SYM "Long"; SX_STR "A"; ⟪SX_SYM "Long"; SX_STR "B"; ⟪SX_SYM "Short"; SX_STR "x"⟫⟫⟫;
   SX_CONS (SX_SYM "Short") (SX_CONS (SX_STR "x") (SX_SYM "bad"));
   ⟪SX_SYM "Long"; SX_STR "A"; ⟪SX_SYM "Short"; SX_STR "x"⟫; SX_NUM 1⟫]``;
val _ = show "literals" ``MAP fromSexp$sexplit
  [0; 12; SX_STR "a\\00b"; ⟪SX_SYM "-"; 0⟫; ⟪SX_SYM "-"; 12⟫;
   ⟪SX_SYM "char"; SX_STR "z"⟫; ⟪SX_SYM "char"; SX_STR "ab"⟫;
   ⟪SX_SYM "word8"; 255⟫; ⟪SX_SYM "word8"; 256⟫;
   ⟪SX_SYM "word64"; 18446744073709551615⟫; ⟪SX_SYM "word64"; 18446744073709551616⟫;
   ⟪SX_SYM "float64"; 42⟫]``;
val _ = show "locations" ``MAP fromSexp$sexplocn
  [⟪SX_SYM "unk"; SX_SYM "eof"⟫; ⟪⟪1; 2⟫; ⟪3; 4⟫⟫; ⟪SX_SYM "bad"; SX_SYM "unk"⟫; ⟪1⟫]``;
val _ = show "types" ``MAP fromSexp$sexptype
  [⟪SX_SYM "Atvar"; SX_STR "a"⟫;
   ⟪SX_SYM "Atfun"; ⟪SX_SYM "Atvar"; SX_STR "a"⟫; ⟪SX_SYM "Attup"; ⟪⟫⟫⟫;
   ⟪SX_SYM "Atapp"; ⟪⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫; ⟪SX_SYM "Short"; SX_STR "list"⟫⟫;
   ⟪SX_SYM "Atvar"; SX_SYM "x"⟫;
   ⟪SX_SYM "Attup"; ⟪⟪SX_SYM "Atvar"; SX_STR "a"⟫; ⟪SX_SYM "Atvar"; SX_STR "b"⟫⟫⟫;
   ⟪SX_SYM "Attup"; SX_CONS (⟪SX_SYM "Atvar"; SX_STR "a"⟫) (SX_SYM "bad")⟫;
   ⟪SX_SYM "Atfun"; ⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫]``;
val _ = show "patterns" ``MAP fromSexp$sexppat
  [SX_STR "x"; ⟪SX_SYM "Pany"⟫; ⟪SX_SYM "Plit"; 42⟫;
   ⟪SX_SYM "Pcon"; SX_SYM "NONE"; ⟪SX_STR "x"; ⟪SX_SYM "Pany"⟫⟫⟫;
   ⟪SX_SYM "Pas"; ⟪SX_SYM "Pref"; SX_STR "x"⟫; SX_STR "y"⟫;
   ⟪SX_SYM "Ptannot"; SX_STR "x"; ⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫;
   ⟪SX_SYM "Pany"; 1⟫;
   ⟪SX_SYM "Pcon"; SX_SYM "NONE";
     ⟪⟪SX_SYM "Pref"; SX_STR "x"⟫; ⟪SX_SYM "Pany"⟫⟫⟫;
   ⟪SX_SYM "Pcon"; SX_SYM "NONE"; SX_CONS (SX_STR "x") (SX_SYM "bad")⟫;
   SX_CONS (SX_SYM "Pany") (SX_SYM "bad")]``;
val _ = showSimp "expressions" ``MAP fromSexp$sexpexp
  [⟪SX_SYM "Lit"; 1⟫;
   ⟪SX_SYM "Var"; ⟪SX_SYM "Short"; SX_STR "x"⟫⟫;
   ⟪SX_SYM "Raise"; ⟪SX_SYM "Lit"; 1⟫⟫;
   ⟪SX_SYM "Fun"; SX_STR "x"; ⟪SX_SYM "Var"; ⟪SX_SYM "Short"; SX_STR "x"⟫⟫⟫;
   ⟪SX_SYM "Con"; SX_SYM "NONE"; ⟪⟪SX_SYM "Lit"; 1⟫; ⟪SX_SYM "Lit"; 2⟫⟫⟫;
   ⟪SX_SYM "Mat"; ⟪SX_SYM "Lit"; 1⟫;
      ⟪SX_CONS (SX_STR "x") ⟪SX_SYM "Lit"; 2⟫⟫⟫;
   ⟪SX_SYM "Letrec";
      ⟪SX_CONS (SX_STR "f") (SX_CONS (SX_STR "x") ⟪SX_SYM "Lit"; 1⟫)⟫;
      ⟪SX_SYM "Lit"; 2⟫⟫;
   ⟪SX_SYM "If"; ⟪SX_SYM "Lit"; 1⟫; ⟪SX_SYM "Lit"; 2⟫; ⟪SX_SYM "Lit"; 3⟫⟫;
   ⟪SX_SYM "App"; SX_SYM "Opref"; SX_CONS (⟪SX_SYM "Lit"; 1⟫) (SX_SYM "bad")⟫;
   ⟪SX_SYM "Mat"; ⟪SX_SYM "Lit"; 1⟫; ⟪SX_STR "x"⟫⟫;
   ⟪SX_SYM "Lit"; 1; 2⟫]``;
val _ = showSimp "declarations" ``MAP fromSexp$sexpdec
  [⟪SX_SYM "Denv"; SX_STR "x"⟫;
   ⟪SX_SYM "Dlet"; ⟪SX_SYM "unk"; SX_SYM "unk"⟫; SX_STR "x"; ⟪SX_SYM "Lit"; 1⟫⟫;
   ⟪SX_SYM "Dmod"; SX_STR "M"; ⟪⟪SX_SYM "Denv"; SX_STR "x"⟫⟫⟫;
   ⟪SX_SYM "Dlocal"; ⟪⟪SX_SYM "Denv"; SX_STR "a"⟫⟫; ⟪⟪SX_SYM "Denv"; SX_STR "b"⟫⟫⟫;
   ⟪SX_SYM "Dtype"; ⟪SX_SYM "unk"; SX_SYM "unk"⟫; ⟪⟫⟫;
   ⟪SX_SYM "Dexn"; ⟪SX_SYM "unk"; SX_SYM "unk"⟫; SX_STR "E"; ⟪⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫⟫;
   ⟪SX_SYM "Dtabbrev"; ⟪SX_SYM "unk"; SX_SYM "unk"⟫; ⟪SX_STR "a"⟫; SX_STR "t"; ⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫;
   ⟪SX_SYM "Dmod"; SX_STR "M"; SX_CONS (⟪SX_SYM "Denv"; SX_STR "x"⟫) (SX_SYM "bad")⟫;
   ⟪SX_SYM "Dlet"; SX_SYM "unk"⟫]``;
val _ = show "operators" ``MAP fromSexp$sexpop
  [SX_SYM "Equality"; SX_SYM "Opapp"; SX_SYM "Aw8subunsafe"; SX_SYM "ForceThunk";
   SX_SYM "Envid"; ⟪SX_SYM "FFI" • SX_STR "x\\00y"⟫;
   ⟪SX_SYM "AllocThunk" • SX_SYM "Evaluated"⟫;
   ⟪SX_SYM "UpdateThunk" • SX_SYM "NotEvaluated"⟫;
   ⟪SX_SYM "Shift64Ror" • 123⟫;
   ⟪SX_SYM "Arith" • ⟪SX_SYM "Add" • SX_SYM "IntT"⟫⟫;
   ⟪SX_SYM "FromTo" • ⟪SX_SYM "Word8T" • SX_SYM "Word64T"⟫⟫;
   ⟪SX_SYM "Test" • ⟪SX_SYM "AltLessEq" • SX_SYM "IntT"⟫⟫;
   ⟪SX_SYM "Arith"; SX_SYM "Add"; SX_SYM "IntT"⟫; SX_SYM "NoSuchOp"]``;
