load "preamble";
load "dataSemTheory";
open HolKernel Parse boolLib bossLib preamble;
open dataSemTheory dataLangTheory semanticPrimitivesTheory sptreeTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
(* Parse and generalize the original line-1349 equations separately: HOL's
   pattern variables in different equations are independently quantified. *)
val originalParts = [
``
(evaluate (Skip,(s:('c,'ffi) dataSem$state)) = (NONE,s))``,
``
(evaluate (Move dest src,s) =
     case get_var src s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME v => (NONE, set_var dest v s))``,
``
(evaluate (Assign dest op args names_opt,s) =
     if op_requires_names op = IS_NONE names_opt then
       (SOME (Rerr(Rabort Rtype_error)),s)
     else
       case get_vars args s.locals of
       | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
       | SOME xs =>
           case cut_state_opt names_opt s of
           | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME s =>
               case do_app op xs s of
               | Rerr e => (SOME (Rerr e),flush_state T (install_sfs op s))
               | Rval (v,s) =>
                   (NONE, set_var dest v (install_sfs op s)))``,
``
(evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),flush_state T s)
                    else (NONE,dec_clock s))``,
``
(evaluate (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME env => (NONE,add_space (s with locals := env) k))``,
``
(evaluate (Raise n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME s => (SOME (Rerr(Rraise x)),s)))``,
``
(evaluate (Return ns,s) =
     case get_vars ns s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME xs => (SOME (Rval xs),flush_state F s))``,
``
(evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1))``,
``
(evaluate (If n c1 c2,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
                        (* no time stamp *)
     | SOME x => if isBool T x then evaluate (c1,s) else
                 if isBool F x then evaluate (c2,s) else
                   (SOME (Rerr(Rabort Rtype_error)),s))``,
``
(evaluate (Force ret loc src,s) =
     case get_var src s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME thunk_v =>
       (case dest_thunk thunk_v s.refs of
        | BadRef => (SOME (Rerr (Rabort Rtype_error)),s)
        | NotThunk => (SOME (Rerr (Rabort Rtype_error)),s)
        | IsThunk Evaluated v =>
          (case ret of
           | NONE => (SOME (Rval [v]),flush_state F s)
           | SOME (dest,names) =>
             (case cut_env names s.locals of
              | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
              | SOME env => (NONE, set_var dest v (s with locals := env))))
        | IsThunk NotEvaluated f =>
           (case find_code (SOME loc) [thunk_v; f] s.code s.stack_frame_sizes of
            | NONE => (SOME (Rerr (Rabort Rtype_error)),s)
            | SOME (args1,prog,ss) =>
              (case ret of
               | NONE =>
                  (if s.clock = 0 then
                     (SOME (Rerr(Rabort Rtimeout_error)),
                           s with <| stack := [] ; locals := LN |>)
                   else
                     (case evaluate (prog, call_env args1 ss (dec_clock s)) of
                      | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                      | (SOME res,s) => (SOME res,s)))
               | SOME (dest,names) =>
                 (case cut_env names s.locals of
                  | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
                  | SOME env =>
                      let s1 = call_env args1 ss (push_env env F (dec_clock s)) in
                        if s.clock = 0 then
                          (SOME (Rerr(Rabort Rtimeout_error)),
                           s1 with <| stack := [] ; locals := LN |>)
                        else
                          (case fix_clock s1 (evaluate (prog, s1)) of
                           | (SOME (Rval xs),s2) =>
                             (if LENGTH xs = 1 then
                                case pop_env s2 of
                                | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                                | SOME s1 => (NONE, set_var dest (HD xs) s1)
                              else
                                (SOME (Rerr(Rabort Rtype_error)),s2))
                           | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                           | res => res))))))``,
``
(evaluate (Call ret dest args handler,s) =
     case get_vars args s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME xs =>
       (case find_code dest xs s.code s.stack_frame_sizes of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME (args1,prog,ss) =>
          (case ret of
           | NONE (* tail call *) =>
             if handler = NONE then
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     flush_state T s)
               else
                 (case evaluate (prog, call_env args1 ss (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME (ns,names) (* returning call, returns into var n *) =>
             if ¬ALL_DISTINCT ns then (SOME (Rerr(Rabort Rtype_error)),s) else
             (case cut_env names s.locals of
              | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
              | SOME env =>
                let s1 = call_env args1 ss
                        (push_env env (IS_SOME handler) (dec_clock s))
                in if s.clock = 0
                   then (SOME (Rerr(Rabort Rtimeout_error)),
                        s1 with <| stack := [] ; locals := LN |>)
                   else (case fix_clock s1 (evaluate (prog, s1)) of
                         | (SOME (Rval xs),s2) =>
                           (if LENGTH xs = LENGTH ns then
                              (case pop_env s2 of
                               | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                               | SOME s1 => (NONE, set_vars ns xs s1))
                            else
                              (SOME (Rerr(Rabort Rtype_error)),s2))
                         | (SOME (Rerr(Rraise x)),s2) =>
                           (* if handler is present, then handle exc *)
                           (case handler of
                            | NONE => (SOME (Rerr(Rraise x)),s2)
                            | SOME (n,h) => evaluate (h, set_var n x s2))
                         | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                         | res => res)))))``
];
val replayed = map (fn tm => GEN_ALL (prove (tm,
  simp [dataSemTheory.fix_clock_evaluate, dataSemTheory.evaluate_def]))) originalParts;
val _ = show "evaluate_original_typed_replay=" (LIST_CONJ replayed);
