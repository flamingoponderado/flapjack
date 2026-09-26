import Flapjack.Pancake.PanSimp

/-!
Flapjack-specific representation bridges for the exact HOL `pan_simp` pass.

These results connect the `ProgHOL` ports to the production `Prog` helpers.
They are not HOL declarations themselves and therefore carry no `@[hol]`
tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Decode of the exact HOL `SmartSeq_def` agrees with production `smartSeq`.
This is Flapjack-specific codec infrastructure: HOL defines `SmartSeq` on
`ProgHOL`, but has no separate theorem about the Lean `progOfHOL` decoder. -/
theorem progOfHOL_smartSeqHOL {width : Nat} [NeZero width]
    (pre program : ProgHOL width) :
    progOfHOL (smartSeqHOL pre program) =
      smartSeq (progOfHOL pre) (progOfHOL program) := by
  cases pre <;> simp [smartSeqHOL, smartSeq, progOfHOL]
  case call info name args =>
    cases info with
    | none => simp [progOfHOL.eq_13]
    | some info =>
      obtain ⟨kind, handler⟩ := info
      cases handler with
      | none => simp [progOfHOL.eq_14]
      | some handler =>
        obtain ⟨eid, vname, body⟩ := handler
        simp [progOfHOL.eq_15]

/-- `toStringOfBytes` is injective because `ofString` is its left inverse.
This local statement avoids an import of the downstream PanGlobals module. -/
theorem panSimpToStringOfBytes_injective : Function.Injective toStringOfBytes := by
  intro left right heq
  have := congrArg ofString heq
  simpa [ofString_toStringOfBytes] using this

@[simp] theorem panSimpToStringOfBytes_eq_iff (left right : MlS) :
    toStringOfBytes left = toStringOfBytes right ↔ left = right := by
  constructor
  · exact fun h => panSimpToStringOfBytes_injective h
  · intro h
    cases h
    rfl

/-- Flapjack-specific decoding of HOL `Prog.call` metadata to production
metadata. There is no separate HOL declaration for this codec helper. -/
def progCallInfoOfHOL {width : Nat} [NeZero width] :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)) →
      Option (Option (VarKind × String) × Option (String × String × Prog (BitVec width)))
  | none => none
  | some (kindOpt, none) =>
      some (kindOpt.map (fun entry => (entry.1, toStringOfBytes entry.2)), none)
  | some (kindOpt, some (eid, vname, body)) =>
      some (kindOpt.map (fun entry => (entry.1, toStringOfBytes entry.2)),
        some (toStringOfBytes eid, toStringOfBytes vname, progOfHOL body))

/-- Every exact HOL call decodes to the production call with decoded names,
arguments, and optional handler body. This is Flapjack-specific codec
infrastructure with no separate HOL original. -/
theorem progOfHOL_call {width : Nat} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (args : List (ExpHOL width)) :
    progOfHOL (.call info name args) =
      Prog.call (progCallInfoOfHOL info) (toStringOfBytes name) (args.map expOfHOL) := by
  cases info with
  | none => simp [progCallInfoOfHOL, progOfHOL.eq_13]
  | some info =>
      obtain ⟨kindOpt, handlerOpt⟩ := info
      cases handlerOpt with
      | none => simp [progCallInfoOfHOL, progOfHOL.eq_14]
      | some handler =>
          obtain ⟨eid, vname, body⟩ := handler
          simp [progCallInfoOfHOL, progOfHOL.eq_15]

/-- Flapjack-specific codec equation for the Call clause of HOL
`seq_assoc_def`. When a handler is present, the only recursive obligation is
that its body commutes with `seqAssocHOL`; the theorem has no separate HOL
original and therefore carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_call {width : Nat} [NeZero width]
    (pre : ProgHOL width)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (args : List (ExpHOL width))
    (handlerBridge : ∀ {returns eid vname body},
      info = some (returns, some (eid, vname, body)) →
        progOfHOL (seqAssocHOL .skip body) = seqAssoc .skip (progOfHOL body)) :
    progOfHOL (seqAssocHOL pre (.call info name args)) =
      seqAssoc (progOfHOL pre)
        (.call (progCallInfoOfHOL info) (toStringOfBytes name) (args.map expOfHOL)) := by
  cases info with
  | none =>
      simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
        progCallInfoOfHOL]
  | some info =>
      obtain ⟨returns, handler⟩ := info
      cases handler with
      | none =>
          simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
            progCallInfoOfHOL]
      | some handler =>
          obtain ⟨eid, vname, body⟩ := handler
          have hbody := handlerBridge (returns := returns) (eid := eid)
            (vname := vname) (body := body) rfl
          simp [seqAssocHOL, seqAssoc, progOfHOL_smartSeqHOL, progOfHOL_call,
            progCallInfoOfHOL, hbody]

/-- Flapjack-specific representation bridge for HOL `seq_call_ret_def`.
HOL has no separate theorem about the `ProgHOL` decoder. This proof compares
the exact MlString guard with production String equality through the codec
lemma above; it is not a tagged HOL declaration. -/
theorem progOfHOL_seqCallRetHOL {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    progOfHOL (seqCallRetHOL program) = seqCallRet (progOfHOL program) := by
  cases program with
  | seq first second =>
      cases first with
      | call info function arguments =>
          cases info with
          | none => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
          | some info =>
              obtain ⟨kindOpt, handlerOpt⟩ := info
              cases kindOpt with
              | none =>
                  cases handlerOpt with
                  | none => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                  | some handler =>
                      obtain ⟨eid, vname, body⟩ := handler
                      cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
              | some kindName =>
                  obtain ⟨kind, returnName⟩ := kindName
                  cases handlerOpt with
                  | some handler =>
                      obtain ⟨eid, vname, body⟩ := handler
                      cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                  | none =>
                      cases kind with
                      | global => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
                      | «local» =>
                          cases second with
                          | «return» value =>
                              cases value with
                              | var returnedKind returnedName =>
                                  cases returnedKind with
                                  | global =>
                                      simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL]
                                  | «local» =>
                                      by_cases h : returnName = returnedName
                                      · simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL, h]
                                      · simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL, h,
                                          panSimpToStringOfBytes_eq_iff]
                              | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL, expOfHOL]
                          | call info name args =>
                              simp [seqCallRetHOL, seqCallRet, progOfHOL, progOfHOL_call,
                                progCallInfoOfHOL]
                          | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL]
      | _ => cases second <;> simp [seqCallRetHOL, seqCallRet, progOfHOL]
  | call info name args =>
      cases info with
      | none => simp [seqCallRetHOL, seqCallRet, progOfHOL]
      | some info =>
          obtain ⟨kindOpt, handlerOpt⟩ := info
          cases handlerOpt with
          | none => simp [seqCallRetHOL, seqCallRet, progOfHOL]
          | some handler =>
              obtain ⟨eid, vname, body⟩ := handler
              simp [seqCallRetHOL, seqCallRet, progOfHOL]
  | _ => simp [seqCallRetHOL, seqCallRet, progOfHOL]

/-- Flapjack-specific codec equation for the Seq clause of HOL
`ret_to_tail_def`. It reuses the `seq_call_ret` bridge, whose exact MlString
equality guard is reflected by the codec; it has no separate HOL original and
therefore carries no `@[hol]` tag. -/
theorem progOfHOL_retToTailHOL_seq {width : Nat} [NeZero width]
    (first second : ProgHOL width)
    (hfirst : progOfHOL (retToTailHOL first) = retToTail (progOfHOL first))
    (hsecond : progOfHOL (retToTailHOL second) = retToTail (progOfHOL second)) :
    progOfHOL (retToTailHOL (.seq first second)) =
    seqCallRet (.seq (retToTail (progOfHOL first)) (retToTail (progOfHOL second))) := by
  simp [retToTailHOL, progOfHOL, progOfHOL_seqCallRetHOL, hfirst, hsecond]

/-- Flapjack-specific codec equation for the Dec clause of HOL
`ret_to_tail_def`. Its only recursive obligation is the body's codec equation;
HOL has no theorem about commuting `progOfHOL` with `retToTailHOL`, so this
declaration carries no `@[hol]` tag. -/
theorem progOfHOL_retToTailHOL_dec {width : Nat} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (value : ExpHOL width) (body : ProgHOL width)
    (hbody : progOfHOL (retToTailHOL body) = retToTail (progOfHOL body)) :
    progOfHOL (retToTailHOL (.dec name shape value body)) =
      retToTail (progOfHOL (.dec name shape value body)) := by
  simp only [retToTailHOL, retToTail, progOfHOL.eq_2, hbody]

/-- Flapjack-specific codec equation for the Call clause of HOL
`ret_to_tail_def`. A recursive equation is needed only for a present handler;
the helper has no separate HOL original and carries no `@[hol]` tag. -/
theorem progOfHOL_retToTailHOL_call {width : Nat} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (args : List (ExpHOL width))
    (handlerBridge : ∀ {returns eid vname body},
      info = some (returns, some (eid, vname, body)) →
        progOfHOL (retToTailHOL body) = retToTail (progOfHOL body)) :
    progOfHOL (retToTailHOL (.call info name args)) =
      retToTail (.call (progCallInfoOfHOL info) (toStringOfBytes name)
        (args.map expOfHOL)) := by
  cases info with
  | none =>
      simp [retToTailHOL, retToTail, progOfHOL_call, progCallInfoOfHOL]
  | some info =>
      obtain ⟨returns, handler⟩ := info
      cases handler with
      | none =>
          simp [retToTailHOL, retToTail, progOfHOL_call, progCallInfoOfHOL]
      | some handler =>
          obtain ⟨eid, vname, body⟩ := handler
          have hbody := handlerBridge (returns := returns) (eid := eid)
            (vname := vname) (body := body) rfl
          simp [retToTailHOL, retToTail, progOfHOL_call, progCallInfoOfHOL, hbody]

/-- Flapjack-specific codec equation for the Seq clause of HOL
`seq_assoc_def`. The only premises are the two recursive codec equations;
HOL has no theorem about commuting `progOfHOL` with `seqAssocHOL`, so this
declaration carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_seq {width : Nat} [NeZero width]
    (pre first second : ProgHOL width)
    (hfirst : ∀ pending,
      progOfHOL (seqAssocHOL pending first) =
        seqAssoc (progOfHOL pending) (progOfHOL first))
    (hsecond : ∀ pending,
      progOfHOL (seqAssocHOL pending second) =
        seqAssoc (progOfHOL pending) (progOfHOL second)) :
    progOfHOL (seqAssocHOL pre (.seq first second)) =
      seqAssoc (progOfHOL pre) (.seq (progOfHOL first) (progOfHOL second)) := by
  simp only [seqAssocHOL]
  rw [hsecond, hfirst]
  simp [seqAssoc]

/-- Flapjack-specific codec equation for the Dec clause of HOL
`seq_assoc_def`. It uses the recursive body equation at Skip and has no
separate HOL original, so it carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_dec {width : Nat} [NeZero width]
    (pre : ProgHOL width) (name : MlS) (shape : ShapeHOL)
    (value : ExpHOL width) (body : ProgHOL width)
    (hbody : progOfHOL (seqAssocHOL .skip body) =
      seqAssoc .skip (progOfHOL body)) :
    progOfHOL (seqAssocHOL pre (.dec name shape value body)) =
      seqAssoc (progOfHOL pre) (progOfHOL (.dec name shape value body)) := by
  simp only [seqAssocHOL]
  rw [progOfHOL_smartSeqHOL]
  simp [seqAssoc, progOfHOL, hbody]

/-- Flapjack-specific codec equation for the If clause of HOL
`seq_assoc_def`. The only recursive obligations are the then and else branch
equations at Skip. HOL has no theorem about commuting `progOfHOL` with
`seqAssocHOL`, so this declaration carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_ite {width : Nat} [NeZero width]
    (pre : ProgHOL width) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width)
    (hthen : progOfHOL (seqAssocHOL .skip thenBranch) =
      seqAssoc .skip (progOfHOL thenBranch))
    (helse : progOfHOL (seqAssocHOL .skip elseBranch) =
      seqAssoc .skip (progOfHOL elseBranch)) :
    progOfHOL (seqAssocHOL pre (.ite condition thenBranch elseBranch)) =
      seqAssoc (progOfHOL pre)
        (.ite (expOfHOL condition) (progOfHOL thenBranch) (progOfHOL elseBranch)) := by
  simp only [seqAssocHOL]
  rw [progOfHOL_smartSeqHOL]
  simp [seqAssoc, progOfHOL, hthen, helse]

/-- Flapjack-specific codec equation for the While clause of HOL
`seq_assoc_def`. Its only recursive obligation is the loop-body equation at
Skip. HOL has no theorem about commuting `progOfHOL` with `seqAssocHOL`, so
this declaration carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_while {width : Nat} [NeZero width]
    (pre : ProgHOL width) (condition : ExpHOL width) (body : ProgHOL width)
    (hbody : progOfHOL (seqAssocHOL .skip body) =
      seqAssoc .skip (progOfHOL body)) :
    progOfHOL (seqAssocHOL pre (.while condition body)) =
      seqAssoc (progOfHOL pre) (.while (expOfHOL condition) (progOfHOL body)) := by
  simp only [seqAssocHOL]
  rw [progOfHOL_smartSeqHOL]
  simp [seqAssoc, progOfHOL, hbody]

/-- Flapjack-specific codec equation for the DecCall clause of HOL
`seq_assoc_def`. Its only recursive obligation is the body equation at Skip.
HOL has no theorem about commuting `progOfHOL` with `seqAssocHOL`, so this
declaration carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_decCall {width : Nat} [NeZero width]
    (pre : ProgHOL width) (name : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (body : ProgHOL width)
    (hbody : progOfHOL (seqAssocHOL .skip body) =
      seqAssoc .skip (progOfHOL body)) :
    progOfHOL (seqAssocHOL pre (.decCall name shape function arguments body)) =
      seqAssoc (progOfHOL pre)
        (progOfHOL (.decCall name shape function arguments body)) := by
  simp only [seqAssocHOL]
  rw [progOfHOL_smartSeqHOL]
  simp [seqAssoc, progOfHOL, hbody]

/-- Flapjack-specific codec equation for the annotation clause of HOL
`seq_assoc_def`. HOL erases annotations to the pending prefix, and no
recursive obligation is needed. HOL has no theorem about commuting `progOfHOL`
with `seqAssocHOL`, so this declaration carries no `@[hol]` tag. -/
theorem progOfHOL_seqAssocHOL_annot {width : Nat} [NeZero width]
    (pre : ProgHOL width) (tag text : MlS) :
    progOfHOL (seqAssocHOL pre (.annot tag text)) =
      seqAssoc (progOfHOL pre) (progOfHOL (.annot tag text)) := by
  simp [seqAssocHOL, seqAssoc, progOfHOL]

/-- Flapjack-specific codec equation for the Tick fallback clause of HOL
`seq_assoc_def`. This case needs no recursive obligation. HOL has no theorem
about commuting `progOfHOL` with `seqAssocHOL`, so it carries no `@[hol]` tag.
-/
theorem progOfHOL_seqAssocHOL_tick {width : Nat} [NeZero width]
    (pre : ProgHOL width) :
    progOfHOL (seqAssocHOL pre .tick) =
      seqAssoc (progOfHOL pre) (progOfHOL (.tick : ProgHOL width)) := by
  have hhol : seqAssocHOL pre (.tick : ProgHOL width) = smartSeqHOL pre .tick :=
    seqAssocHOL.eq_11 pre .tick
      (by intro h; cases h)
      (by intro name shape value body h; cases h)
      (by intro first second h; cases h)
      (by intro condition thenBranch elseBranch h; cases h)
      (by intro condition body h; cases h)
      (by intro info function arguments h; cases h)
      (by intro name shape function arguments body h; cases h)
      (by intro tag text h; cases h)
  rw [hhol, progOfHOL_smartSeqHOL, progOfHOL.eq_22]
  exact (seqAssoc.eq_11 (progOfHOL pre) Prog.tick
      (by intro h; cases h)
      (by intro name shape value body h; cases h)
      (by intro first second h; cases h)
      (by intro condition thenBranch elseBranch h; cases h)
      (by intro condition body h; cases h)
      (by intro info function arguments h; cases h)
      (by intro name shape function arguments body h; cases h)
      (by intro tag text h; cases h)).symm

end Flapjack
