(* Typed statement captures for the [local] theorems of pan_to_crepProof
   (task 152 manual sweep). The first four statements (state_rel_structs,
   state_rel_globals, pair_map_I, decs_stcnames_lemma) are replayed and proved
   with the source proof's lemmas, so show_types prints the inferred carriers
   of the proved replays. The last two (evaluate_shape_invariant_ret_inst and
   evaluate_shape_invariant_ret_inst2) are only parsed typed statements: their
   replayed proofs fail on this tree's local locals_rel_wf_shape variant, so
   the script prints the typed statement text without proving it. *)
load "preamble"; load "pan_to_crepProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble pan_to_crepProofTheory pan_to_crepTheory panSemTheory crepSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show_thm label th =
  (print label; print "="; print_term (concl th); print "\n");

val state_rel_structs_replay = prove(
  ``∀(s :('a,'b) panSem$state) (t :('a,'b) crepSem$state).
      state_rel s t ⇒ s.structs = ([] :(mlstring # struct_info) list)``,
  simp [pan_to_crepProofTheory.state_rel_def]);
val _ = show_thm "state_rel_structs_typed" state_rel_structs_replay;

val state_rel_globals_replay = prove(
  ``∀(s :('a,'b) panSem$state) (t :('a,'b) crepSem$state).
      state_rel s t ⇒ s.globals = (FEMPTY :mlstring |-> 'a v)``,
  simp [pan_to_crepProofTheory.state_rel_def]);
val _ = show_thm "state_rel_globals_typed" state_rel_globals_replay;

val pair_map_I_replay = prove(
  ``(λ(x :'a, y :'b). (x,y)) = (I :'a # 'b -> 'a # 'b)``,
  rw [FUN_EQ_THM, ELIM_UNCURRY]);
val _ = show_thm "pair_map_I_typed" pair_map_I_replay;

val decs_stcnames_lemma_replay = prove(
  ``∀(code :'a decl list) (ctxt :(mlstring # struct_info) list).
      EVERY (λd. is_function d ∨ is_exn_decl d) code ⇒
      decs_stcnames ctxt code = SOME ctxt``,
  rw [] >> irule panPropsTheory.decs_stcnames_only_functions >>
  dxrule_at_then (Pos last) irule EVERY_MONOTONIC >> rw[] >> rw[]);
val _ = show_thm "decs_stcnames_lemma_typed" decs_stcnames_lemma_replay;

(* The two evaluate_shape_invariant_ret_inst statements depend on the local
   locals_rel_wf_shape variant; capture their typed statements. *)
val evaluate_shape_invariant_ret_inst_statement =
  ``∀(p :'a panLang$prog) (s :('a,'b) panSem$state) (v :'a panSem$result)
     (s' :('a,'b) panSem$state) (t :('a,'b) crepSem$state)
     (ctxt :'c context) (t_locs :num |-> 'a word_lab).
      panSem$evaluate (p,s) = (SOME v,s') ∧ state_rel s t ∧
      locals_rel ctxt s.locals t_locs ⇒
      case v of Return retv => is_wf_shape_v_nil retv
        | Exception eid exn => is_wf_shape_v_nil exn
        | _ => T``;
val _ = (print "evaluate_shape_invariant_ret_inst_typed=";
  print_term evaluate_shape_invariant_ret_inst_statement; print "\n");

val evaluate_shape_invariant_ret_inst2_statement =
  ``∀(s :('a,'b) panSem$state) (argexps :'a panLang$exp list)
     (args :'a v list) (fname :mlstring) (p :'a panLang$prog)
     (p2 :'a panLang$prog) (newlocals :mlstring |-> 'a v) (rsh :shape)
     (v :'a panSem$result) (s' :('a,'b) panSem$state)
     (t :('a,'b) crepSem$state) (ctxt :'c context)
     (t_locs :num |-> 'a word_lab).
      OPT_MMAP (panSem$eval s) argexps = SOME args ∧
      lookup_code s.code fname args = SOME (p2,newlocals,rsh) ∧
      panSem$evaluate (p, panSem$dec_clock s with locals := newlocals) =
        (SOME v,s') ∧
      state_rel s t ∧ locals_rel ctxt s.locals t_locs ⇒
      case v of Return retv => is_wf_shape_v_nil retv
        | Exception eid exn => is_wf_shape_v_nil exn
        | _ => T``;
val _ = (print "evaluate_shape_invariant_ret_inst2_typed=";
  print_term evaluate_shape_invariant_ret_inst2_statement; print "\n");
