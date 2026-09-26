(* Direct HOL-EVAL probes for pan_to_crep$compile (compile_def).
   Reference: cakeml/pancake/pan_to_crepScript.sml:139-305. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
val _ = Globals.max_print_depth := 100;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "return"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Return (Const (7w : 8 word)))``;

val _ = print_eval "multi_return"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Return (RStruct [Const (1w : 8 word); Const 2w]))``;

val _ = print_eval "store32_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Store32 (panLang$Const (1w : 8 word)) (panLang$Const 2w))``;
val _ = print_eval "store32_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Store32 (panLang$RStruct ([] : 8 panLang$exp list))
        (panLang$Const 2w))``;
val _ = print_eval "store_byte_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$StoreByte (panLang$Const (3w : 8 word)) (panLang$Const 4w))``;
val _ = print_eval "store_byte_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$StoreByte (panLang$Const (3w : 8 word))
        (panLang$RStruct ([] : 8 panLang$exp list)))``;
val _ = print_eval "if_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (If (Const (1w : 8 word)) Skip Break)``;
val _ = print_eval "if_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (If (RStruct ([] : 8 panLang$exp list)) Skip Skip)``;
val _ = print_eval "while_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (While (Const (2w : 8 word)) Break)``;
val _ = print_eval "while_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (While (RStruct ([] : 8 panLang$exp list)) Skip)``;
val _ = print_eval "global_assign_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Assign Global «g» (Const (5w : 8 word)))``;
val _ = print_eval "global_shmem_load_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (ShMemLoad Op8 Global «g» (Const (3w : 8 word)))``;
val _ = print_eval "local_assign_direct"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$One, [7])) |+ («src», (panLang$One, [8]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Assign Local «dst» (Var Local «src»))``;
val _ = print_eval "local_assign_overlap_temporaries"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$One, [7])) |+ («src», (panLang$One, [7]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Assign Local «dst» (Var Local «src»))``;
val _ = print_eval "local_assign_missing_destination"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Assign Local «dst» (Var Local «src»))``;
val _ = print_eval "local_assign_length_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$Comb [panLang$One; panLang$One], [7; 8]))
           |+ («src», (panLang$One, [9]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Assign Local «dst» (Var Local «src»))``;
val _ = print_eval "primitive_destination_present"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$One, [7])) |+ («src», (panLang$One, [8]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Primitive «dst» AddCarry [Const (1w : 8 word); Var Local «src»])``;
val _ = print_eval "primitive_destination_missing"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (Primitive «dst» AddCarry [Const (1w : 8 word); Var Local «src»])``;
val _ = print_eval "store_one_word"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Store (Const (3w : 8 word)) (Const 4w))``;
val _ = print_eval "store_multiword"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Store (Const (3w : 8 word)) (RStruct [Const 4w; Const 5w]))``;
val _ = print_eval "store_address_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Store (RStruct ([] : 8 panLang$exp list)) (Const 4w))``;
val _ = print_eval "store_shape_length_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («bad», (panLang$Comb [panLang$One; panLang$One], [9]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Store (Const (3w : 8 word)) (Var Local «bad»))``;
val _ = print_eval "raise_one_word"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY;
         eids := FEMPTY |+ («E», (12w : 8 word)); vmax := 0 |>
      (Raise «E» (Const (9w : 8 word)))``;
val _ = print_eval "raise_multiword"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY;
         eids := FEMPTY |+ («E», (12w : 8 word)); vmax := 0 |>
      (Raise «E» (RStruct [Const (1w : 8 word); Const 2w]))``;
val _ = print_eval "raise_missing_eid"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Raise «missing» (Const (9w : 8 word)))``;
val _ = print_eval "raise_shape_length_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («bad», (panLang$Comb [panLang$One; panLang$One], [9]));
         funcs := FEMPTY; eids := FEMPTY |+ («E», (12w : 8 word)); vmax := 0 |>
      (Raise «E» (Var Local «bad»))``;
val _ = print_eval "shmem_store_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («src», (panLang$One, [8]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemStore Op8 (Var Local «src») (Const (3w : 8 word)))``;
val _ = print_eval "shmem_store_value_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemStore Op8 (RStruct ([] : 8 panLang$exp list)) (Const (3w : 8 word)))``;
val _ = print_eval "shmem_store_address_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemStore Op8 (Const (4w : 8 word)) (RStruct ([] : 8 panLang$exp list)))``;
val _ = print_eval "shmem_load_local_clause"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$One, [7]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemLoad Op8 Local «dst» (Const (3w : 8 word)))``;
val _ = print_eval "shmem_load_missing_destination"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemLoad Op8 Local «dst» (Const (3w : 8 word)))``;
val _ = print_eval "shmem_load_address_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («dst», (panLang$One, [7]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (ShMemLoad Op8 Local «dst» (RStruct ([] : 8 panLang$exp list)))``;
val _ = print_eval "dec_one_word"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Dec «x» panLang$One (Const (4w : 8 word))
        (Return (Var Local «x»)))``;
val _ = print_eval "dec_multiword"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Dec «pair» (panLang$Comb [panLang$One; panLang$One])
        (RStruct [Const (1w : 8 word); Const 2w]) Tick)``;
val _ = print_eval "dec_shape_length_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («bad», (panLang$Comb [panLang$One; panLang$One], [9]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Dec «x» panLang$One (Var Local «bad») Tick)``;

val _ = print_eval "struct_skip"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Skip : 8 word panLang$prog)``;

val _ = print_eval "struct_break"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Break : 8 word panLang$prog)``;

val _ = print_eval "struct_continue"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Continue : 8 word panLang$prog)``;

val _ = print_eval "struct_tick"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Tick : 8 word panLang$prog)``;

val _ = print_eval "struct_annot"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Annot «slice» «text» : 8 word panLang$prog)``;

val _ = print_eval "struct_seq"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Seq Skip (Seq Break Continue) : 8 word panLang$prog)``;

val _ = print_eval "missing_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «missing»), NONE)) «f» [])``;

val _ = print_eval "empty_one_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («empty_one», (panLang$One, []));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «empty_one»), NONE)) «f» [])``;

val _ = print_eval "extra_names_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («extra_names», (panLang$One, [4; 5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «extra_names»), NONE)) «f» [])``;

val _ = print_eval "missing_names_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («missing_names»,
          (panLang$Comb [panLang$One; panLang$One], [4]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 4 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «missing_names»), NONE)) «f» [])``;

(* Local-kind mirrors of the four Global cases above: Cake's assigned-call
   rule looks up the destination with `wrap_rt (FLOOKUP ctxt.vars rt)` and
   ignores the `rk` kind tag, so each pair must agree. *)

val _ = print_eval "missing_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «missing»), NONE)) «f» [])``;

val _ = print_eval "empty_one_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («empty_one», (panLang$One, []));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «empty_one»), NONE)) «f» [])``;

val _ = print_eval "extra_names_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («extra_names», (panLang$One, [4; 5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «extra_names»), NONE)) «f» [])``;

val _ = print_eval "missing_names_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («missing_names»,
          (panLang$Comb [panLang$One; panLang$One], [4]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 4 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «missing_names»), NONE)) «f» [])``;

val _ = print_eval "valid_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («pair»,
          (panLang$Comb [panLang$One; panLang$One], [0; 1]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 1 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «pair»), NONE)) «f» [])``;

val _ = print_eval "empty_struct_return"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Return (panLang$RStruct []))``;

val _ = print_eval "finite_map_shadow_return"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [3]))
                 |+ («p», (panLang$One, [5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Return (panLang$Var panLang$Local «p»))``;

val _ = print_eval "deccall_one_word"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 4 |>
      (panLang$DecCall «x» panLang$One «f» [panLang$Const (3w : 8 word)]
        (panLang$Return (panLang$Var panLang$Local «x»)))``;

val _ = print_eval "deccall_multiword"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 10 |>
      (panLang$DecCall «pair» (panLang$Comb [panLang$One; panLang$One]) «f»
        [panLang$Const (3w : 8 word); panLang$Const 4w]
        (panLang$Return (panLang$Var panLang$Local «pair»)))``;

(* The source freshness bound scans all var_cexp words, even though ExtCall
   requires each operand to have shape One and emits only its first word. *)
val _ = print_eval "extcall_high_tail"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («ptr1», (panLang$One, [4; 100]))
                 |+ («len1», (panLang$One, [5]))
                 |+ («ptr2», (panLang$One, [6]))
                 |+ («len2», (panLang$One, [7]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$ExtCall «f»
        (panLang$Var panLang$Local «ptr1»)
        (panLang$Var panLang$Local «len1»)
        (panLang$Var panLang$Local «ptr2»)
        (panLang$Var panLang$Local «len2»))``;

val _ = print_eval "extcall_shared_high_tail"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («x», (panLang$One, [1; 99]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$ExtCall «f»
        (panLang$Var panLang$Local «x»)
        (panLang$Var panLang$Local «x»)
        (panLang$Var panLang$Local «x»)
        (panLang$Var panLang$Local «x»))``;

val _ = print_eval "extcall_constants"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 400 |>
      (panLang$ExtCall «f» (panLang$Const (1w : 8 word))
        (panLang$Const 2w) (panLang$Const 3w) (panLang$Const 4w))``;

val _ = print_eval "extcall_shape_fallback"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$ExtCall «f» (panLang$RStruct ([] : 8 panLang$exp list))
        (panLang$Const (1w : 8 word)) (panLang$Const 2w) (panLang$Const 3w))``;

val _ = print_eval "pair_load"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [0]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Return
        (panLang$Load (panLang$Comb [panLang$One; panLang$One])
          (panLang$Var panLang$Local «p»)) : 64 word panLang$prog)``;

val _ = print_eval "pair_store"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [0]))
                 |+ («x», (panLang$One, [1]))
                 |+ («y», (panLang$One, [2]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 2 |>
      (panLang$Store (panLang$Var panLang$Local «p»)
        (panLang$RStruct
          [panLang$Var panLang$Local «x»; panLang$Var panLang$Local «y»]) :
        64 word panLang$prog)``;

val _ = print_eval "fixed_stride64"
  ``(pan_to_crep$compile_exp
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      panLang$BytesInWord : 64 word crepLang$exp list # panLang$shape)``;
