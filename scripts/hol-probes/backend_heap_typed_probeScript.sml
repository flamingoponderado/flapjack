(* Typed captures for the PR1213 heap_address/heap_element/refs_to_addresses and
   compile_to_word_conventions2 rows. The two gc_shared datatypes are captured
   through their constructor types; refs_to_addresses_def is printed from the
   loaded word_gcFunctionsTheory. backendProofTheory is not built, so
   compile_to_word_conventions2 is a typed source parse: its literal statement
   (backendProofScript.sml, between the `Theorem` header and `Proof`) is parsed with
   show_types in the loaded word_to_wordProofTheory context, and the theory of the
   resolved `compile` constant is printed. It is not re-proved. *)
load "preamble"; load "gc_sharedTheory"; load "word_gcFunctionsTheory"; load "word_to_wordProofTheory";
open HolKernel Parse boolLib bossLib preamble gc_sharedTheory word_gcFunctionsTheory
  wordConvsTheory word_to_wordTheory word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
fun read_source rel =
  let val st = TextIO.openIn (OS.Path.concat (source_cake, rel))
      val tx = TextIO.inputAll st
  in (TextIO.closeIn st; tx) end;
fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then raise Fail ("missing " ^ pre)
                 else Substring.string (Substring.triml (String.size pre) rest);
fun statement_of source header =
  let
    val rest = after_prefix header source
    val body = after_prefix ":\n" rest
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;
fun guard source name lit = if String.isSubstring lit source then ()
  else raise Fail (name ^ " literal source changed");
fun capture_type label tm = (print (label ^ "="); print_type (type_of tm); print "\n");
fun capture_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = capture_type "heap_address_Pointer_type" ``gc_shared$Pointer``;
val _ = capture_type "heap_address_Data_type" ``gc_shared$Data``;
val _ = capture_type "heap_element_Unused_type" ``gc_shared$Unused``;
val _ = capture_type "heap_element_ForwardPointer_type" ``gc_shared$ForwardPointer``;
val _ = capture_type "heap_element_DataElement_type" ``gc_shared$DataElement``;
val _ = capture_thm "refs_to_addresses_def_statement" refs_to_addresses_def;
val src = read_source "compiler/backend/proofs/backendProofScript.sml";
val conv2 = Parse.Term [QUOTE (statement_of src "\nTheorem compile_to_word_conventions2")];
val _ = (print "compile_to_word_conventions2_source_statement_typed="; print_term conv2; print "\n");
val compile_consts = HOLset.listItems (HOLset.filter (fn c => #1 (dest_const c) = "compile") (FVL [] empty_tmset |> K (HOLset.fromList Term.compare (find_terms is_const conv2))));
val _ = (print "compile_to_word_conventions2_compile_constant=";
  List.app (fn c => let val {Thy, Name, ...} = dest_thy_const c in print (Thy ^ "$" ^ Name ^ " ") end) compile_consts;
  print "\n");
