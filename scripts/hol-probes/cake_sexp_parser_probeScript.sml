load "simpleSexpParseTheory";
load "locationTheory";
open HolKernel Parse boolLib bossLib;
val _ = computeLib.scrub_thms [pegTheory.wfG_def];
val _ = computeLib.add_thms [EQT_INTRO simpleSexpPEGTheory.wfG_sexpPEG];
val _ = Globals.linewidth := 1000000;
fun show label tm = let
  val expanded = REWRITE_CONV [simpleSexpParseTheory.parse_sexp_def,
    pegexecTheory.pegparse_def, simpleSexpPEGTheory.wfG_sexpPEG] tm
  val result = EVAL (rhs (concl expanded))
  in print label; print "="; print_term (rhs (concl result)); print "\n" end;
val _ = show "atoms" ``MAP (\s. simpleSexpParse$parse_sexp (MAP (\c. (c,location$unknown_loc)) s))
  ["nil"; "12345"; "alpha.beta"; "\"a\\\"b\""; "'  x"]``;
val _ = show "lists" ``MAP (\s. simpleSexpParse$parse_sexp (MAP (\c. (c,location$unknown_loc)) s))
  ["()"; "(1 2 3)"; "(1 2 . 3)"; "(1 (2 . 3) . 4)"; "(1 . nil)"; "(1 . (2 3))"]``;
val _ = show "failures" ``MAP (\s. simpleSexpParse$parse_sexp (MAP (\c. (c,location$unknown_loc)) s))
  [""; "(1"; "(. 1)"; "(1 . 2 3)"; "1abc"; "\"\\q\""; "\"unterminated"; "() ()"]``;
val _ = show "edges" ``MAP (\s. simpleSexpParse$parse_sexp (MAP (\c. (c,location$unknown_loc)) s))
  ["  (a .b) \n"; "a.b"; ".a"; "(a.b)"; "123.4"; "''x"; "(1 . ())";
   "(1 . 2)garbage"; "(1 . 2 . 3)"; "\"\\\\\""; "\"a\nb\""; "\"a\"b"]``;
val _ = show "bytes" ``MAP (\s. simpleSexpParse$parse_sexp (MAP (\c. (c,location$unknown_loc)) s))
  [[CHR 9; CHR 10; #"x"; CHR 13]; [CHR 0]; [CHR 127]; [CHR 128];
   [#"\""; CHR 31; #"\""]; [#"\""; CHR 126; #"\""]; [#"x"; CHR 128]]``;
