(* Full original type audit. Existing labSem constants are queried directly.
   Proof-local declarations and absent labProps definitions are re-elaborated
   from unchanged original source in memory; no artifacts are exported. *)
load "bossLib";
load "preamble";
load "labSemTheory";
open bossLib HolKernel Parse preamble labSemTheory;
val _ = new_theory "lab_to_target_navigation_types";
val cake = case OS.Process.getEnv "CAKEML" of SOME s => s
  | NONE => "/home/zksecurity/pancake-lean/cakeml";
fun read_source path = let val input = TextIO.openIn (cake ^ path)
  val source = TextIO.inputAll input val _ = TextIO.closeIn input in source end;
val proof = read_source "/compiler/backend/proofs/lab_to_targetProofScript.sml";
val props = read_source "/compiler/backend/semantics/labPropsScript.sml";
fun extract source start finish = let
  val (_, suffix) = Substring.position start (Substring.full source)
  val (body, _) = Substring.position finish (Substring.triml (String.size start) suffix)
  val _ = if Substring.isEmpty body then raise Fail ("Missing " ^ start) else ()
  in Substring.string body end;
val sec_def = Define [QUOTE (extract proof "Definition sec_loc_to_pc_def:\n" "\nEnd")];
val sec_label_def = Define [QUOTE (extract props "Definition sec_label_ok_def[simp]:\n" "\nEnd")];
val sec_labels_def = Define [QUOTE (extract props "Definition sec_labels_ok_def[simp]:\n" "\nEnd")];
fun print_type_row label term = (print(label ^ "="); print_type(type_of term); print "\n");
fun print_statement label text = let val term = Parse.Term [QUOTE text]
  in print(label ^ "="); print_term term; print "\n";
     List.app (fn variable => print_type_row (label ^ "_binder_" ^ fst(dest_var variable)) variable) (#1 (strip_forall term) @ free_vars term)
  end;
val _ = print_type_row "sec_loc_to_pc" ``sec_loc_to_pc``;
val _ = print_statement "sec_loc_to_pc_cons" (extract proof "Theorem sec_loc_to_pc_cons:\n" "\nProof");
val _ = print_statement "loc_to_pc_thm" (extract proof "Theorem loc_to_pc_thm:\n" "\nProof");
val _ = print_type_row "loc_to_pc" ``labSem$loc_to_pc``;
val _ = print_type_row "is_Label" ``labSem$is_Label``;
val _ = print_type_row "asm_fetch_aux" ``labSem$asm_fetch_aux``;
val _ = print_type_row "asm_code_length" ``labSem$asm_code_length``;
val _ = print_type_row "sec_label_ok" ``sec_label_ok``;
val _ = print_type_row "sec_labels_ok" ``sec_labels_ok``;
val _ = print_type_row "len_no_lab_original_overload" ``\xs. LENGTH (FILTER ($~ o labSem$is_Label) xs)``;
val similar_def = Define [QUOTE (extract proof "Definition line_similar_def:\n" "\nEnd")];
val code_def = Define [QUOTE (extract proof "Definition code_similar_def:\n" "\nEnd")];
val _ = print_type_row "line_similar" ``line_similar``;
val _ = print_type_row "code_similar" ``code_similar``;
val _ = print_type_row "Label" ``labLang$Label``;
val _ = print_type_row "Asm" ``labLang$Asm``;
val _ = print_type_row "LabAsm" ``labLang$LabAsm``;
val _ = print_type_row "Section" ``labLang$Section``;
val _ = print_type_row "Asmi" ``labLang$Asmi``;
val _ = print_type_row "ShareMem" ``labLang$ShareMem``;
val _ = print_type_row "JumpCmp" ``labLang$JumpCmp``;
val _ = print_type_row "CallFFI" ``labLang$CallFFI``;
val _ = print_type_row "Imm" ``asm$Imm``;
val _ = print_type_row "Addr" ``asm$Addr``;
val _ = print_statement "code_similar_IMP_asm_fetch_aux_line_similar"
  (extract proof "Theorem code_similar_IMP_asm_fetch_aux_line_similar:\n" "\nProof");
val _ = print_statement "code_similar_loc_to_pc"
  (extract proof "Theorem code_similar_loc_to_pc:\n" "\nProof");
