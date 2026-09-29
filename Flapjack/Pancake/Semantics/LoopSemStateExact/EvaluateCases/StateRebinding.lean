import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Direct HOL case equations for the exact Loop evaluator

Source review of `cakeml/pancake/semantics/loopSemScript.sml:278-440` against
`LoopSemStateFiniteExact.evaluate`:

| HOL `evaluate_def` constructor | Lean constructor / generated equation |
| --- | --- |
| Skip, Fail, Assign, Primitive | `HolLoopProg.skip` … `primitive`; `evaluate.eq_1` … `eq_4` |
| Arith, Store, SetGlobal, Load32, LoadByte | `arith` … `loadByte`; `evaluate.eq_5` … `eq_9` |
| Store32, StoreByte, Seq, If, Mark | `store32` … `mark`; `evaluate.eq_10` … `eq_14` |
| Break, Continue, Loop, Raise, Return | `break` … `return`; `evaluate.eq_15` … `eq_19` |
| ShMem, Tick, LocValue, Call, FFI | `shMem` … `ffi`; `evaluate.eq_20` … `eq_24` |

The constructors and order are those of `loopLang$prog` at
`loopLangScript.sml:16-36`. The exact state is `LoopSemStateFiniteExact` from
`loopSemScript.sml:13-27`: the globals field uses the reviewed
`HolFiniteMapExact` finite-support representation; the word carrier is
`BitVec width` with `[NeZero width]`; code is `Spt (List Nat × HolLoopProg
width)` and the FFI host remains polymorphic. The evaluator uses the separately
tagged `eval_def`, `loop_arith_def`, memory operations, `sh_mem_op`/FFI helpers,
and state updates. In particular, `ShMem`'s `is_load` is `asm$is_load_def`
(`asmScript.sml:324-330`), exposed through `asmIsLoad`; it is not
`loop_call$is_load`.

The source-sensitive recursive cases are retained as direct case theorems
below, each with the exact `evaluate_def` source tag and no extra correctness
premises. HOL rebinds its pattern variable after `cut_res` in Loop and
non-tail Call and after `cut_state` in FFI. The Lean equations use the rebound
values `s1`/`s'` for subsequent work: Loop's body and recursive iteration use
`s1`/`s2`; Call's post-call locals restoration uses `s1.locals`; FFI reads and
updates use `s'`, while its outer lookup failure returns the original state.
These equations make the rebinding points kernel-visible.

The `If` clause writes `cut_res live_out (evaluate (if b then c1 else c2, s))`
in HOL. Lean's generated `evaluate.eq_13` distributes `cutRes` over the branch
test. The two forms reduce to the same selected branch; the main evaluator's
docstring records this presentational rewrite. HOL's `w2w` operations are
`BitVec.setWidth`, including the explicit 32-bit and 8-bit store operands.
This review is about the exact evaluator specification only; it does not claim
that the optional production `evaluateLoop` hook path is an evaluator adapter.
-/

namespace Flapjack.LoopSemStateFiniteExact.EvaluateCases

/-- Same-module checked witness for the exact globals finite-support qualifier
used by these tagged case equations. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Direct If case equation of HOL `loopSem$evaluate_def` (source line 278).
This keeps HOL's selected-program-before-`cut_res` presentation; Lean's
generated equation distributes the cut over the same Boolean test. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 278
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluateIfCase {width : Nat} [NeZero width] {F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : RegImm (BitVec width))
    (c1 c2 : HolLoopProg width) (liveOut : NumSet)
    (s : LoopSemStateFiniteExact width F) :
    evaluate (.ite cmp r1 ri c1 c2 liveOut) s =
      match sptLookup r1 s.locals, getVarImm ri s with
      | some (.word x), some (.word y) =>
          cutRes liveOut
            (evaluate (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y then c1 else c2) s)
      | _, _ => (some .error, s) := by
  rw [evaluate.eq_13]
  cases hlookup : sptLookup r1 s.locals with
  | none => simp
  | some value =>
      cases value with
      | loc label offset => simp
      | word x =>
          cases himm : getVarImm ri s with
          | none => simp
          | some value =>
              cases value with
              | loc label offset => simp
              | word y =>
                  cases hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y <;>
                    simp [hcmp]

/-- Direct Loop case equation of HOL `loopSem$evaluate_def` (source line 278;
the Loop clause is at line 350). The cut state is the state rebound by HOL's
`case cut_res ... of (NONE,s)`, and is used by the body and recursive Loop. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 278
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluateLoopCase {width : Nat} [NeZero width] {F : Type}
    (liveIn liveOut : NumSet) (body : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) :
    evaluate (.loop liveIn body liveOut) s =
      match _hc : cutRes liveIn (none, s) with
      | (none, s1) =>
          match _hb : fixClock s1 (evaluate body s1) with
          | (none, s2) => evaluate (.loop liveIn body liveOut) s2
          | (some (.continue 0), s2) => evaluate (.loop liveIn body liveOut) s2
          | (some (.break 0), s2) => cutRes liveOut (none, s2)
          | (res, s2) => (exitLoop res, s2)
      | res => res := by
  exact evaluate.eq_17 s liveIn body liveOut

/-- Direct non-tail Call case equation of HOL `loopSem$evaluate_def` (source
line 278; Call is at line 386). After the successful `cut_res`, the returned
locals and handler bodies use the state rebound by HOL's `(NONE,s)` pattern. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 278
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluateCallCase {width : Nat} [NeZero width] {F : Type}
    (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (argvars : List Nat)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
    (s : LoopSemStateFiniteExact width F) :
    evaluate (.call ret dest argvars handler) s =
      match getVars argvars s with
      | none => (some .error, s)
      | some argvals =>
          match findCode dest argvals s.code with
          | none => (some .error, s)
          | some (env, prog) =>
              match ret with
              | none =>
                  if handler.isSome then (some .error, s) else
                  if _hz : s.clock = 0 then (some .timeOut, { s with locals := .ln })
                  else
                    match evaluate prog { decClock s with locals := env } with
                    | (none, s') => (some .error, s')
                    | (some (.continue _), s') => (some .error, s')
                    | (some (.break _), s') => (some .error, s')
                    | (some res, s') => (some res, s')
              | some (ns, live) =>
                  if ¬ ns.Nodup then (some .error, s) else
                  match _hc : cutRes live (none, s) with
                  | (none, s1) =>
                      match _hf : fixClock { s1 with locals := env }
                          (evaluate prog { s1 with locals := env }) with
                      | (some (.result retvs), st) =>
                          if retvs.length ≠ ns.length then (some .error, st) else
                          match handler with
                          | none => (none, setVars ns retvs { st with locals := s1.locals })
                          | some (_, _, r, liveOut) =>
                              cutRes liveOut
                                (evaluate r (setVars ns retvs { st with locals := s1.locals }))
                      | (some (.exception exn), st) =>
                          match handler with
                          | none => (some (.exception exn), { st with locals := .ln })
                          | some (n, h, _, liveOut) =>
                              cutRes liveOut
                                (evaluate h (setVar n exn { st with locals := s1.locals }))
                      | (some (.continue _), st) => (some .error, st)
                      | (some (.break _), st) => (some .error, st)
                      | (none, st) => (some .error, st)
                      | res => res
                  | res => res := by
  exact evaluate.eq_23 s ret dest argvars handler

/-- Direct FFI case equation of HOL `loopSem$evaluate_def` (source line 278;
FFI is at line 426). Inputs are looked up in the original state, but byte-array
reads, `call_FFI`, memory/FFI updates and `call_env` use the state rebound by
HOL's successful `cut_state` pattern. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 278
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluateFFICase {width : Nat} [NeZero width] {F : Type}
    (idx : Flapjack.Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat) (cutset : NumSet)
    (s : LoopSemStateFiniteExact width F) :
    evaluate (.ffi idx ptr1 len1 ptr2 len2 cutset) s =
      match sptLookup len1 s.locals, sptLookup ptr1 s.locals,
          sptLookup len2 s.locals, sptLookup ptr2 s.locals, cutState cutset s with
      | some (.word w), some (.word w2), some (.word w3), some (.word w4), some s' =>
          match readBytearrayWordHOL w2 w.toNat
                  (memLoadByteAuxExact s'.memory s'.mdomain s'.be),
              readBytearrayWordHOL w4 w3.toNat
                  (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with
          | some bytes, some bytes2 =>
              match callFFIHOL s'.ffi (.extCall idx) bytes bytes2 with
              | .final outcome => (some (.finalFfi outcome), callEnv [] s')
              | .ret newFfi newBytes =>
                  (none, { s' with
                    memory := writeBytearrayExact w4 newBytes s'.memory s'.mdomain s'.be,
                    ffi := newFfi })
          | _, _ => (some .error, s')
      | _, _, _, _, _ => (some .error, s) := by
  exact evaluate.eq_24 s idx ptr1 len1 ptr2 len2 cutset

end Flapjack.LoopSemStateFiniteExact.EvaluateCases
