(* Re-elaborate the unchanged original proof-local Definition to inspect its
   inferred type. The original proof theory has no prebuilt object here.
   No source files/theory exports are written; this is not a substitute evaluator. *)
load "bossLib";
load "preamble";
load "labSemTheory";
open bossLib HolKernel Parse preamble;
val cake_dir = case OS.Process.getEnv "CAKEML" of SOME s => s
  | NONE => "/home/zksecurity/pancake-lean/cakeml";
val input = TextIO.openIn (cake_dir ^ "/compiler/backend/proofs/lab_to_targetProofScript.sml");
val source = TextIO.inputAll input;
val _ = TextIO.closeIn input;
val marker = "Definition enc_with_nop_def:\n";
val (_, suffix) = Substring.position marker (Substring.full source);
val after = Substring.triml (String.size marker) suffix;
val (body, _) = Substring.position "\nEnd" after;
val _ = if Substring.isEmpty body then raise Fail "Original definition missing" else ();
val definition = Define [QUOTE (Substring.string body)];
val _ = print "enc_with_nop_original_source_type=";
val _ = print_type (type_of ``enc_with_nop``);
val _ = print "\n";
