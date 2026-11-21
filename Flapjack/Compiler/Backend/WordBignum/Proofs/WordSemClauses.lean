module

public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

@[expose] public section

/-! Flapjack-only named clause equations of the tagged `wordSem` evaluator,
projected from `evaluate_def_rebound`, for the bignum compiler proofs.  They
restate existing clauses and have no separate HOL name. -/

namespace Flapjack.WordSemStateFiniteExact.BignumClauses

open Flapjack

variable {width : Nat} [NeZero width] {C F : Type}

theorem evaluate_skip (s : WordSemStateFiniteExact width C F) :
    evaluate .skip s = (none, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).1 s

theorem evaluate_inst (s : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width)) :
    evaluate (.inst i) s =
      (match inst i s with
       | some s1 => (none, s1)
       | none => (some .error, s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.1 s i

theorem evaluate_assign (v : Nat) (s : WordSemStateFiniteExact width C F)
    (exp : WordLangExpHOL (BitVec width)) :
    evaluate (.assign v exp) s =
      (match wordExp s exp with
       | none => (some .error, s)
       | some w => (none, setVar v w s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.1 v s exp

theorem evaluate_get (v : Nat) (s : WordSemStateFiniteExact width C F) (name : WordStoreHOL) :
    evaluate (.get v name) s =
      (match getStore name s with
       | none => (some .error, s)
       | some x => (none, setVar v x s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.1 v s name

theorem evaluate_set (v : WordStoreHOL) (s : WordSemStateFiniteExact width C F)
    (exp : WordLangExpHOL (BitVec width)) :
    evaluate (.set v exp) s =
      (if v = .handler ∨ v = .bitmapBase then (some .error, s)
       else
         match wordExp s exp with
         | none => (some .error, s)
         | some w => (none, setStore v w s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.1 v s exp

theorem evaluate_store (v : Nat) (s : WordSemStateFiniteExact width C F)
    (exp : WordLangExpHOL (BitVec width)) :
    evaluate (.store exp v) s =
      (match wordExp s exp, WordSemStateFiniteExact.getVar v s with
       | some (.word a), some w =>
           match memStore a w s with
           | some s1 => (none, s1)
           | none => (some .error, s)
       | _, _ => (some .error, s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.1 v s exp

theorem evaluate_mustTerminate (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) :
    evaluate (.mustTerminate p) s =
      (if s.termdep = 0 then (some .error, s)
       else
         match evaluate p { s with clock := wordSemMustTerminateLimit width,
                                   termdep := s.termdep - 1 } with
         | (res, s1) =>
             match res with
             | some .timeOut => (some .error, s)
             | _ => (res, { s1 with clock := s.clock, termdep := s.termdep })) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1 s p

theorem evaluate_seq (s : WordSemStateFiniteExact width C F)
    (c1 c2 : WordLangProgHOL (BitVec width)) :
    evaluate (.seq c1 c2) s =
      (match evaluate c1 s with
       | (res, s1) =>
           match res with
           | none => evaluate c2 s1
           | _ => (res, s1)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1 s c2 c1

/-- A sequence whose first statement finishes normally continues with the
second statement. -/
theorem evaluate_seq_of_none (s s1 : WordSemStateFiniteExact width C F)
    (c1 c2 : WordLangProgHOL (BitVec width)) (h : evaluate c1 s = (none, s1)) :
    evaluate (.seq c1 c2) s = evaluate c2 s1 := by
  rw [evaluate_seq, h]

theorem evaluate_return (s : WordSemStateFiniteExact width C F) (n : Nat) (ms : List Nat) :
    evaluate (.return n ms) s =
      (match WordSemStateFiniteExact.getVar n s, WordSemStateFiniteExact.getVars ms s with
       | some (.loc l1 l2), some ys => (some (.result (.loc l1 l2) ys), flushState false s)
       | _, _ => (some .error, s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 s n ms

theorem evaluate_ite (s : WordSemStateFiniteExact width C F) (ri : WordRegImm (BitVec width))
    (r1 : Nat) (cmp : Cmp) (c1 c2 : WordLangProgHOL (BitVec width)) :
    evaluate (.ite cmp r1 ri c1 c2) s =
      (match WordSemStateFiniteExact.getVar r1 s, WordSemStateFiniteExact.getVarImm ri s with
       | some x, some y =>
           match wordSemWordCmp cmp x y with
           | some true => evaluate c1 s
           | some false => evaluate c2 s
           | none => (some .error, s)
       | _, _ => (some .error, s)) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    s ri r1 cmp c2 c1

theorem evaluate_call (s : WordSemStateFiniteExact width C F) ret handler dest args :
    evaluate (.call ret dest args handler) s =
      (match WordSemStateFiniteExact.getVars args s with
       | none => (some .error, s)
       | some xs =>
           if wordSemBadDestArgs dest args then (some .error, s)
           else
             match wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
             | none => (some .error, s)
             | some (args1, prog, ss) =>
                 match ret with
                 | none =>
                     match handler with
                     | none =>
                         if s.clock = 0 then (some .timeOut, flushState true s)
                         else
                           match evaluate prog (callEnv args1 ss (decClock s)) with
                           | (res, s) =>
                               if wordSemBadFunReturn res then (some .error, s) else (res, s)
                     | some _ => (some .error, s)
                 | some (n, names, retHandler, l1, l2) =>
                     if sptDomainEmpty names.1 ∨ ¬ n.Nodup then (some .error, s)
                     else
                       match wordSemCutEnvs names s.locals with
                       | none => (some .error, s)
                       | some envs =>
                           if s.clock = 0 then
                             (some .timeOut, flushState true
                               { s with stack := [],
                                        stackMax := (callEnv args1 ss (pushEnv envs handler s)).stackMax })
                           else
                             match evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
                             | (some (.result x ys), s2) =>
                                 if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                                 else
                                   match popEnv s2 with
                                   | none => (some .error, s2)
                                   | some s1 =>
                                       if sptDomainEqUnion s1.locals envs.1 envs.2 then
                                         evaluate retHandler (setVars n ys s1)
                                       else (some .error, s1)
                             | (some (.exception x y), s2) =>
                                 match handler with
                                 | none => (some (.exception x y), s2)
                                 | some (n, hprog, l1, l2) =>
                                     if x ≠ .loc l1 l2 then (some .error, s2)
                                     else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                                       evaluate hprog (setVar n y s2)
                                     else (some .error, s2)
                             | (none, s) => (some .error, s)
                             | (some (.break _), s) => (some .error, s)
                             | (some (.continue _), s) => (some .error, s)
                             | res => res) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    s ret handler dest args

end Flapjack.WordSemStateFiniteExact.BignumClauses
