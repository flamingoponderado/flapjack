(* Direct pinned original byte theory, arbitrary count and positive dimensions. *)
load "bossLib";
load "preamble";
load "byteTheory";
open bossLib HolKernel Parse preamble byteTheory;
fun print_eval label q =
  let val th = CONV_RULE
        (RAND_CONV (REWRITE_CONV [arithmeticTheory.MOD_0] THENC EVAL)) (EVAL q)
  in print (label ^ "=" ^ term_to_string (rconc th) ^ "\n") end;
val _ = print_eval "ByteAuxLE16Cycle" ``word_to_bytes_aux 5 (4660w:16 word) F = [52w;18w;52w;18w;52w]``;
val _ = print_eval "ByteAuxBE16Cycle" ``word_to_bytes_aux 5 (4660w:16 word) T = [18w;52w;18w;52w;18w]``;
val _ = print_eval "ByteAuxLE32Cycle" ``word_to_bytes_aux 6 (305419896w:32 word) F = [120w;86w;52w;18w;120w;86w]``;
val _ = print_eval "ByteAuxBE32Cycle" ``word_to_bytes_aux 6 (305419896w:32 word) T = [18w;52w;86w;120w;18w;52w]``;
val _ = print_eval "ByteAuxOneByteCycle" ``word_to_bytes_aux 3 (165w:8 word) F = [165w;165w;165w]``;
val _ = print_eval "ByteAuxSubByteLEWrap" ``word_to_bytes_aux 5 (1w:1 word) F = [1w;0w;1w;0w;1w]``;
val _ = print_eval "ByteAuxSubByteBEWrap" ``word_to_bytes_aux 5 (1w:1 word) T = [1w;1w;1w;1w;1w]``;
val _ = print_eval "ByteAuxZero" ``word_to_bytes_aux 0 (4660w:16 word) T = []``;
val _ = print_eval "ByteWholeLE16" ``word_to_bytes (4660w:16 word) F = [52w;18w]``;
val _ = print_eval "ByteWholeBE16" ``word_to_bytes (4660w:16 word) T = [18w;52w]``;
val _ = print_eval "ByteWholeSubByte" ``word_to_bytes (1w:1 word) F = []``;
val _ = print_eval "ByteIndexSubByteLE" ``byte_index (1w:1 word) F = 8``;
val _ = print_eval "ByteIndexSubByteBE" ``byte_index (1w:1 word) T = 0``;
val _ = print_eval "ByteGetSubByteShift" ``get_byte (1w:1 word) (1w:1 word) F = 0w``;
