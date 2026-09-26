(* Direct HOL oracle for the *generated* datatype size functions of panLang.

   HOL's `Datatype` command generates `shape_size`/`shape1_size` and
   `exp_size`/`exp1_size`/`exp2_size`/`exp3_size` for
   cakeml/pancake/panLangScript.sml:35-39 (`shape`) and :53-69 (`exp`).  These
   are not textual source declarations (`Definition`/`Theorem`), so
   `scripts/check-hol-refs.py` cannot resolve them and the Lean ports cannot
   carry an `@[hol]` tag.  `Theorem MEM_IMP_shape_size`
   (panLangScript.sml:131-137) and `Theorem MEM_IMP_exp_size`
   (panLangScript.sml:198-208) are stated over them, so their exact equations
   are pinned here.

   This probe imports the real CakeML `panLangTheory` (compiled from
   `cakeml/pancake/panLangScript.sml`) and prints the generated equations
   directly from that theory, plus concrete `EVAL` rows.  It does not modify
   the CakeML submodule: it runs from a separately built `panLangTheory`
   obtained by a targeted `Holmake panLangTheory.ui` over the same source
   commit (857f0d98da8f8a3580f3442338e697809308ede).  Regenerate with:

     CAKEML=<built CakeML checkout> \
       HOL_PROBE_ONLY=pan_lang_size_probeScript.sml scripts/hol-probes/regenerate.sh

   The `print_thm` output is captured in `pan_lang_size_probe.out`. *)

load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_thm label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  );

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_thm "mlstring_size_def" mlstringTheory.mlstring_size_def;
val _ = print_thm "shape_size_def" panLangTheory.shape_size_def;
val _ = print_thm "exp_size_def" panLangTheory.exp_size_def;
val _ = print_thm "MEM_IMP_shape_size" panLangTheory.MEM_IMP_shape_size;
val _ = print_thm "MEM_IMP_exp_size" panLangTheory.MEM_IMP_exp_size;

val shape_one = ``(panLang$One : panLang$shape)``;
val shape_comb = ``panLang$Comb [panLang$One; panLang$One]``;
val shape_named = ``panLang$Named (strlit "A")``;
val e_const = ``(panLang$Const (7w : 8 word) : 8 panLang$exp)``;
val e_var = ``panLang$Var panLang$Local (strlit "x")``;
val e_rstruct =
  ``panLang$RStruct [panLang$Const (1w : 8 word); panLang$Const (2w : 8 word)]``;
val e_nstruct =
  ``panLang$NStruct (strlit "S")
     [(strlit "f", panLang$Const (3w : 8 word))]``;
val e_load = ``panLang$Load panLang$One (panLang$Const (7w : 8 word))``;
val e_load32 = ``panLang$Load32 (panLang$Const (7w : 8 word))``;
val e_op =
  ``panLang$Op asm$Add [panLang$Const (1w : 8 word); panLang$Const (2w : 8 word)]``;
val e_cmp =
  ``panLang$Cmp asm$Equal (panLang$Const (1w : 8 word))
     (panLang$Const (2w : 8 word))``;
val e_base = ``(panLang$BaseAddr : 8 panLang$exp)``;

val _ = print_eval "shape_size_one" ``shape_size ^shape_one``;
val _ = print_eval "shape_size_comb" ``shape_size ^shape_comb``;
val _ = print_eval "shape_size_named" ``shape_size ^shape_named``;
val _ = print_eval "exp_size_const" ``exp_size (K 0) ^e_const``;
val _ = print_eval "exp_size_var" ``exp_size (K 0) ^e_var``;
val _ = print_eval "exp_size_rstruct" ``exp_size (K 0) ^e_rstruct``;
val _ = print_eval "exp_size_nstruct" ``exp_size (K 0) ^e_nstruct``;
val _ = print_eval "exp_size_load" ``exp_size (K 0) ^e_load``;
val _ = print_eval "exp_size_load32" ``exp_size (K 0) ^e_load32``;
val _ = print_eval "exp_size_op" ``exp_size (K 0) ^e_op``;
val _ = print_eval "exp_size_cmp" ``exp_size (K 0) ^e_cmp``;
val _ = print_eval "exp_size_base" ``exp_size (K 0) ^e_base``;

val _ = print "DONE\n";
