(* Direct HOL-EVAL observations for the lab_to_target shared-memory/FFI name
   definitions (lab_to_targetScript.sml:349-430): the shmem_info_num record,
   list_add_if_fresh, find_ffi_names, get_memop_info and get_shmem_info.
   Bead flapjack-pxn.18.5.15.10.20.

   All line/section inputs are concrete 64-bit labLang$line/labLang$sec values.
   The `shmem_info_num` rows print the record value verbatim so the field
   values and `entry_pc`/`exit_pc` byte positions are compared. *)

load "bossLib";
load "preamble";
load "lab_to_targetTheory";
load "asmTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open lab_to_targetTheory;
open asmTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

(* get_memop_info: all eight clauses *)
val _ = print_eval "GetMemopInfoLoad" ``get_memop_info Load``;
val _ = print_eval "GetMemopInfoLoad32" ``get_memop_info Load32``;
val _ = print_eval "GetMemopInfoLoad16" ``get_memop_info Load16``;
val _ = print_eval "GetMemopInfoLoad8" ``get_memop_info Load8``;
val _ = print_eval "GetMemopInfoStore" ``get_memop_info Store``;
val _ = print_eval "GetMemopInfoStore32" ``get_memop_info Store32``;
val _ = print_eval "GetMemopInfoStore16" ``get_memop_info Store16``;
val _ = print_eval "GetMemopInfoStore8" ``get_memop_info Store8``;

(* list_add_if_fresh: empty, element already present, element absent *)
val _ = print_eval "ListAddIfFreshEmpty"
  ``list_add_if_fresh (3 : num) []``;
val _ = print_eval "ListAddIfFreshPresent"
  ``list_add_if_fresh (2 : num) [1; 2]``;
val _ = print_eval "ListAddIfFreshAbsent"
  ``list_add_if_fresh (3 : num) [1; 2]``;

(* find_ffi_names: empty, a two-name program with a repeated call and skipped
   empty/non-CallFFI sections, and a program with only a non-CallFFI line *)
val ffiCode = ``[
  labLang$Section 1
    [labLang$LabAsm (labLang$CallFFI (strlit "foo")) (0w:64 word) [] 1;
     labLang$LabAsm (labLang$CallFFI (strlit "bar")) (0w:64 word) [] 1;
     labLang$LabAsm (labLang$CallFFI (strlit "foo")) (0w:64 word) [] 1];
  labLang$Section 2 ([] : 64 labLang$line list);
  labLang$Section 3
    [labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [] 1]
] : 64 labLang$sec list``;
val _ = print_eval "FindFfiNamesEmpty"
  ``find_ffi_names ([] : 64 labLang$sec list)``;
val _ = print_eval "FindFfiNamesConcrete" ``find_ffi_names ^ffiCode``;
val _ = print_eval "FindFfiNamesNonCallFFI"
  ``find_ffi_names
     ([labLang$Section 3
        [labLang$LabAsm (labLang$Jump (labLang$Lab 1 0)) (0w:64 word) [] 1]]
       : 64 labLang$sec list)``;

(* get_shmem_info: empty, a Label skipped without advancing pos, a ShareMem
   with a concrete Addr, and an ordinary Asm advancing pos before a ShareMem *)
val labelSkipCode = ``[
  labLang$Section 1
    [labLang$Label 1 0 1;
     labLang$Asm (labLang$ShareMem asm$Store 5 (asm$Addr 7 (10w:64 word)))
       [1w; 2w; 3w; 4w] 4]
] : 64 labLang$sec list``;
val shareMemCode = ``[
  labLang$Section 1
    [labLang$Asm (labLang$ShareMem asm$Store32 5 (asm$Addr 7 (10w:64 word)))
       [1w; 2w; 3w; 4w] 4]
] : 64 labLang$sec list``;
val asmAdvanceCode = ``[
  labLang$Section 1
    [labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [9w; 9w] 2;
     labLang$Asm (labLang$ShareMem asm$Store 4 (asm$Addr 3 (2w:64 word)))
       [1w] 1];
  labLang$Section 2 ([] : 64 labLang$line list)
] : 64 labLang$sec list``;
val _ = print_eval "GetShmemInfoEmpty"
  ``get_shmem_info ([] : 64 labLang$sec list) 0 [] []``;
val _ = print_eval "GetShmemInfoLabelSkip"
  ``get_shmem_info ^labelSkipCode 0 [] []``;
val _ = print_eval "GetShmemInfoShareMem"
  ``get_shmem_info ^shareMemCode 0 [] []``;
val _ = print_eval "GetShmemInfoAsmAdvance"
  ``get_shmem_info ^asmAdvanceCode 0 [] []``;