load "fromSexpTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show label tm =
  (print label; print "="; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show "control" ``MAP fromSexp$decode_control
  ["abc"; "\\\\"; "\\00"; "\\1F"; "\\7F"; "\\FF"; "\\20"; "\\5C";
   "\\1f"; "\\FG"; "\\"; [CHR 31]; "x\\00y"]``;
val _ = show "lists" ``MAP (fromSexp$sexplist fromSexp$odestSXNUM)
  [⟪⟫; ⟪1; 2; 3⟫; ⟪1 • 2⟫; ⟪SX_STR "x"⟫]``;
val _ = show "option" ``MAP (fromSexp$sexpopt fromSexp$odestSXNUM)
  [SX_SYM "NONE"; ⟪SX_SYM "SOME"; 5⟫; ⟪SX_SYM "SOME"; 1; 2⟫; SX_SYM "SOME"]``;
val _ = show "identifier" ``MAP (fromSexp$sexpid fromSexp$odestSEXSTR)
  [⟪SX_SYM "Short"; SX_STR "x"⟫;
   ⟪SX_SYM "Long"; SX_STR "M"; ⟪SX_SYM "Short"; SX_STR "x"⟫⟫;
   ⟪SX_SYM "Long"; SX_STR "M"; SX_SYM "x"⟫]``;
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
   ⟪SX_SYM "Atvar"; SX_SYM "x"⟫]``;
val _ = show "patterns" ``MAP fromSexp$sexppat
  [SX_STR "x"; ⟪SX_SYM "Pany"⟫; ⟪SX_SYM "Plit"; 42⟫;
   ⟪SX_SYM "Pcon"; SX_SYM "NONE"; ⟪SX_STR "x"; ⟪SX_SYM "Pany"⟫⟫⟫;
   ⟪SX_SYM "Pas"; ⟪SX_SYM "Pref"; SX_STR "x"⟫; SX_STR "y"⟫;
   ⟪SX_SYM "Ptannot"; SX_STR "x"; ⟪SX_SYM "Atvar"; SX_STR "a"⟫⟫;
   ⟪SX_SYM "Pany"; 1⟫]``;
