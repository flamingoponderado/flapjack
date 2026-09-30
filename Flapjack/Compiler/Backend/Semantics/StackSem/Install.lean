import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Misc.ShiftSeq

/-! Source-matched `evaluate_def` Install clause fragment over the exact
StackSem state/result carriers. It is deliberately untagged: this partial
dispatch helper is not the total HOL `evaluate_def` definition, and because no
total recursive `evaluate` exists yet the outer `NONE` means this module does not
handle the constructor, so it never substitutes `Error` for an unported clause.
The Install clause does not recurse, so no recursive-evaluation parameter is
needed. The assembled evaluator route is tracked by `flapjack-y19g`
(bead `flapjack-y19g.14.5`).

Counterpart of `cakeml/compiler/backend/semantics/stackSemScript.sml:893-921`.
The four word registers are read in HOL order (`ptr`, `len`, `dptr`, `dlen`;
the Lean constructor is `.install codeBuffer codeLength dataBuffer dataLength
returnAddress`), the compiler oracle is sampled at step 0 into `(cfg, progs, bm)`,
the code buffer is flushed with the exact `buffer_flush` port and the data buffer
is either flushed the same way (`use_stack`) or replaced by the oracle bitmap,
and the exact `compile` result is compared against the flushed bytes, the oracle
bitmap, and the shifted oracle's configuration. On success the state installs the
bitmap, both buffers, the `union` of the old code with `fromAList progs`, the
`DRESTRICT`/`FUPDATE` register update at `codeBuffer`, the emptied `fp_regs`, and
the shifted oracle. The `returnAddress` field is unused by the HOL clause. The
configuration comparison `FST (new_oracle 0) = cfg'` is HOL's total `=` on `'c`,
rendered as Lean equality under the `[DecidableEq C]` instance that the branch
requires; this is the only extra typeclass and it changes no clause. -/

namespace Flapjack.StackSemInstall

open StackSemStateOps Compiler.Backend.StackLang

/-- Flapjack-only helper for HOL `DRESTRICT fm keep`
(`finite_mapScript.sml:715`): `DRESTRICT` keeps exactly the keys in its set
argument, so a key survives when the membership predicate holds and is dropped
otherwise. This is not a tagged HOL declaration; it renders the finite-map
restriction `s.regs` uses to install HOL `DRESTRICT s.regs s.ffi_save_regs`. The
support of the result is a subset of the source support, so the original
witness still covers it. -/
def restrictIn {α β : Type} (m : HolFiniteMapExact α β) (keep : α → Bool) :
    HolFiniteMapExact α β where
  lookup key := if keep key then m.lookup key else none
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := m.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hkey
    apply hkeys key
    by_cases h : keep key
    · simpa [h] using hkey
    · simp [h] at hkey

/-- The HOL `evaluate (Install ptr len dptr dlen ret, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:893-921`; the Lean
constructor is `.install codeBuffer codeLength dataBuffer dataLength
returnAddress`). It reads `codeBuffer`, `codeLength`, `dataBuffer`, and
`dataLength` in that HOL order; all four must be `Word`, else `(SOME Error, s)`.
It samples `s.compile_oracle 0` into `(cfg, progs, bm)`, flushes the code buffer
with the exact `wordSemBufferFlush` port and flushes the data buffer the same way
when `s.use_stack` (otherwise the oracle bitmap `bm` and the unchanged buffer are
used as the `SOME` pair); any miss gives `(SOME Error, s)`. With
`new_oracle = shift_seq 1 s.compile_oracle`, a `SOME (bytes', cfg')` compile
result and a nonempty `progs` succeed only when `bytes = bytes'`,
`data = bm`, and `FST (new_oracle 0) = cfg'`; then the state installs
`bitmaps ++ bm`, both flushed buffers, `union s.code (fromAList progs)`,
`(DRESTRICT s.regs s.ffi_save_regs) |+ (codeBuffer, Loc k 0)`, `FEMPTY` for
`fp_regs`, and `new_oracle`. Every other shape is `(SOME Error, s)`. -/
def evaluateInstall {width : Nat} [NeZero width] {C F : Type} [DecidableEq C]
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .install codeBuffer codeLength dataBuffer dataLength _returnAddress =>
      some (match getVar codeBuffer s, getVar codeLength s,
                   getVar dataBuffer s, getVar dataLength s with
        | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
            let (cfg, progs, bm) := s.compileOracle 0
            match wordSemBufferFlush s.codeBuffer w1 w2,
                  (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4
                   else some (bm, s.dataBuffer)) with
            | some (bytes, cb), some (data, db) =>
                let newOracle := holShiftSeq 1 s.compileOracle
                match s.compile cfg progs, progs with
                | some (bytes', cfg'), (k, _prog) :: _ =>
                    if bytes = bytes' ∧ data = bm ∧ (newOracle 0).1 = cfg' then
                      (none, { s with
                        bitmaps := s.bitmaps ++ bm
                        codeBuffer := cb
                        dataBuffer := db
                        code := sptUnion s.code (sptFromAList progs)
                        regs := (restrictIn s.regs s.ffiSaveRegs).updateEq
                          (codeBuffer, .loc k 0)
                        fpRegs := HolFiniteMapExact.empty
                        compileOracle := newOracle })
                    else (some .error, s)
                | _, _ => (some .error, s)
            | _, _ => (some .error, s)
        | _, _, _, _ => (some .error, s))
  | _ => none

/-- Flapjack assembly equation for the source Install clause, exposing the four
register reads, the oracle sample, the two buffer branches, the compile/`progs`
shape test, and the successful state update. -/
theorem evaluateInstall_install {width : Nat} [NeZero width] {C F : Type} [DecidableEq C]
    (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateInstall (.install codeBuffer codeLength dataBuffer dataLength returnAddress) s =
      some (match getVar codeBuffer s, getVar codeLength s,
                   getVar dataBuffer s, getVar dataLength s with
        | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
            let (cfg, progs, bm) := s.compileOracle 0
            match wordSemBufferFlush s.codeBuffer w1 w2,
                  (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4
                   else some (bm, s.dataBuffer)) with
            | some (bytes, cb), some (data, db) =>
                let newOracle := holShiftSeq 1 s.compileOracle
                match s.compile cfg progs, progs with
                | some (bytes', cfg'), (k, _prog) :: _ =>
                    if bytes = bytes' ∧ data = bm ∧ (newOracle 0).1 = cfg' then
                      (none, { s with
                        bitmaps := s.bitmaps ++ bm
                        codeBuffer := cb
                        dataBuffer := db
                        code := sptUnion s.code (sptFromAList progs)
                        regs := (restrictIn s.regs s.ffiSaveRegs).updateEq
                          (codeBuffer, .loc k 0)
                        fpRegs := HolFiniteMapExact.empty
                        compileOracle := newOracle })
                    else (some .error, s)
                | _, _ => (some .error, s)
            | _, _ => (some .error, s)
        | _, _, _, _ => (some .error, s)) := rfl

end Flapjack.StackSemInstall
