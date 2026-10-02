load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("sr_def=" ^ term_to_string (concl state_rel_def) ^ "\n");
val _ = print ("sr_type=" ^ type_to_string (type_of ``stack_removeProof$state_rel``) ^ "\n");
fun starShape t = let val (head,args) = strip_comb t in
  if same_const head ``set_sep$STAR`` andalso length args = 2 then
    "(" ^ starShape(hd args) ^ "*" ^ starShape(hd(tl args)) ^ ")"
  else "P" end;
val (_,equation) = strip_forall(concl state_rel_def);
val stars = find_terms (fn t => let val (head,args) = strip_comb t in
  same_const head ``set_sep$STAR`` andalso length args = 2 end) equation;
val outer = List.foldl (fn (t,best) => if String.size(starShape t) > String.size(starShape best) then t else best) (hd stars) (tl stars);
val _ = print("sr_star_shape=" ^ starShape outer ^ "\n");
fun check label q = let val th = prove(q,
  rpt gen_tac >> simp [state_rel_def,miscTheory.good_dimindex_def])
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
val _ = check "sr_width1" ``!j off k (s:(1,'c,'ffi)stackSem$state) t. ~state_rel j off k s t``;
val _ = check "sr_width8" ``!j off k (s:(8,'c,'ffi)stackSem$state) t. ~state_rel j off k s t``;
val _ = check "sr_width80" ``!j off k (s:(80,'c,'ffi)stackSem$state) t. ~state_rel j off k s t``;
val _ = check "sr_source_stack" ``!j off k s t. ~state_rel j off k (s with use_stack := F) t``;
val _ = check "sr_source_store" ``!j off k s t. ~state_rel j off k (s with use_store := F) t``;
val _ = check "sr_target_stack" ``!j off k s t. ~state_rel j off k s (t with use_stack := T)``;
val _ = check "sr_target_store" ``!j off k s t. ~state_rel j off k s (t with use_store := T)``;
val _ = check "sr_source_alloc" ``!j off k s t. ~state_rel j off k (s with use_alloc := T) t``;
val _ = check "sr_target_alloc" ``!j off k s t. ~state_rel j off k s (t with use_alloc := T)``;
fun checkGuard label q = let val th = prove(q,
  rpt gen_tac >> strip_tac >> fs [state_rel_def,is_SOME_Word_def])
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
val _ = checkGuard "sr_stack_space" ``!j off k s t. LENGTH s.stack < s.stack_space ==> ~state_rel j off k s t``;
val _ = checkGuard "sr_bitmap_none" ``!j off k s t. FLOOKUP s.store BitmapBase = NONE ==> ~state_rel j off k s t``;
val _ = checkGuard "sr_bitmap_loc" ``!j off k s t a b. FLOOKUP s.store BitmapBase = SOME(Loc a b) ==> ~state_rel j off k s t``;
val _ = checkGuard "sr_base_none" ``!j off k s t. FLOOKUP t.regs (k+1) = NONE ==> ~state_rel j off k s t``;
val _ = checkGuard "sr_base_loc" ``!j off k s t a b. FLOOKUP t.regs (k+1) = SOME(Loc a b) ==> ~state_rel j off k s t``;
