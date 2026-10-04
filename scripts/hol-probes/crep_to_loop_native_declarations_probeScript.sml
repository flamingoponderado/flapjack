load "bossLib";
load "preamble";
load "pan_to_crepTheory";
load "crep_to_loopTheory";
open bossLib HolKernel Parse preamble;
fun emit label q = let val th = EVAL q in print (label ^ "="); print_term (rconc th); print "\n" end;
val declarations = ``[panLang$Function
  <| name := «f»; inline := F; export := F; params := [];
     body := panLang$Call NONE «g» []; return := panLang$One |>;
  panLang$Function
  <| name := «g»; inline := F; export := F; params := [];
     body := panLang$Return (panLang$Const (7w : 8 word)); return := panLang$One |>]``;
val _ = emit "native_crep" ``pan_to_crep$compile_prog ^declarations``;
val _ = emit "native_loop" ``crep_to_loop$compile_prog RISC_V (pan_to_crep$compile_prog ^declarations)``;
val _ = emit "done" ``T``;
