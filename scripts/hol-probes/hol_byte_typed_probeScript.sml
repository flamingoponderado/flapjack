(* Typed statements of the HOL `byte` theory declarations ported in
   `Flapjack/Byte*.lean`, from the built HOL4 core theory (no rebuild). *)
load "byteTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "byte_index_def_typed=" byteTheory.byte_index_def;
val _ = show_thm "get_byte_def_typed=" byteTheory.get_byte_def;
val _ = show_thm "word_to_bytes_def_typed=" byteTheory.word_to_bytes_def;
val _ = show_thm "word_to_bytes_aux_def_typed=" byteTheory.word_to_bytes_aux_def;
val _ = show_thm "get_byte_set_byte_typed=" byteTheory.get_byte_set_byte;
val _ = show_thm "set_byte_def_typed=" byteTheory.set_byte_def;
val _ = show_thm "word_of_bytes_def_typed=" byteTheory.word_of_bytes_def;
val _ = show_thm "word_slice_alt_def_typed=" byteTheory.word_slice_alt_def;
val _ = show_thm "bytes_to_word_def_typed=" byteTheory.bytes_to_word_def;
val _ = show_thm "bytes_in_word_def_typed=" byteTheory.bytes_in_word_def;
