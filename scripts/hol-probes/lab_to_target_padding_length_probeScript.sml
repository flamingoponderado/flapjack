(* Literal lab_to_targetProof LENGTH_pad_bytes3195 and generic pad_bytes192.
   Original theorem remains polymorphic in the list element type. *)
load "bossLib";
load "preamble";
load "lab_to_targetTheory";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetTheory lab_to_targetProofTheory;
val _ = print ("OriginalLengthPadBytes=" ^ term_to_string (concl LENGTH_pad_bytes) ^ "\n");
fun print_eval label q =
  let val th = EVAL q
  in print (label ^ "=" ^ term_to_string (rconc th) ^ "\n") end;
val _ = print_eval "PadLengthExtend" ``pad_bytes [1;2:num] 5 [9] = [1;2;9;9;9]``;
val _ = print_eval "PadLengthMultiNop" ``pad_bytes [1:num] 6 [8;9] = [1;8;9;8;9;8]``;
val _ = print_eval "PadLengthExact" ``pad_bytes [1;2:num] 2 [9] = [1;2]``;
val _ = print_eval "PadLengthZero" ``pad_bytes ([]:num list) 0 [9] = []``;
val _ = print_eval "PadLengthGenericBool" ``pad_bytes [T] 4 [F;T] = [T;F;T;F]``;
val _ = print_eval "PadLengthEmptyNopOutsidePremise" ``pad_bytes ([]:num list) 3 [] = []``;
