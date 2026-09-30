(* Source-derived GlobalAssign block address; original alignmentTheory. *)
load "bossLib"; load "preamble"; load "alignmentTheory";
open bossLib HolKernel Parse preamble alignmentTheory;
fun observe label q = let val th = EVAL q in
 print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "block32" ``let a = (12w:32 word) in let b = 4w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "wrap32" ``let a = (0w:32 word) in let b = 4w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "zero32" ``let a = (4w:32 word) in let b = 4w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "unaligned32" ``let a = (5w:32 word) in let b = 4w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "block64" ``let a = (24w:64 word) in let b = 8w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "wrap64" ``let a = (0w:64 word) in let b = 8w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "zero64" ``let a = (8w:64 word) in let b = 8w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
val _ = observe "unaligned64" ``let a = (9w:64 word) in let b = 8w in
 (w2n (a-b),byte_aligned a,byte_aligned b,byte_aligned (a-b))``;
