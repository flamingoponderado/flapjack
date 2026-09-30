import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.CompHOLImage

namespace Flapjack

/-- Flapjack carrier encoder for the exact instruction subset. The separate
five-register Pancake AddCarry primitive has no single HOL asm counterpart. -/
def wordLangArithToHOL {width : Nat} :
    WordArith (BitVec width) → Option (WordLangArith (BitVec width))
  | .longMul a b c d => some (.longMul a b c d)
  | .longDiv a b c d e => some (.longDiv a b c d e)
  | .addCarry _ _ _ _ _ => none
  | .cakeAddCarry a b c d => some (.addCarry a b c d)
  | .div a b c => some (.div a b c)
  | .binOp op a b c => some (.binop op a b c)
  | .shift op a b c => some (.shift op a b c)

/-- Flapjack instruction encoder; zero-offset memory has two production forms
but one exact HOL address. This function retains every operand and offset. -/
def wordLangInstToHOL {width : Nat} :
    WordInst (BitVec width) → Option (WordLangInst (BitVec width))
  | .const a b => some (.const a b)
  | .arith a => (wordLangArithToHOL a).map .arith
  | .mem op a b => some (.mem op a (.addr b 0))
  | .memOffset op a b offset => some (.mem op a (.addr b offset))

/-- Decoder-image arithmetic inverse, including all four AddCarry positions.
This is a relation between Flapjack carriers, with no HOL theorem original. -/
theorem wordLangArithToHOL_of_fromHOL {width : Nat}
    (a : WordLangArith (BitVec width)) (b : WordArith (BitVec width))
    (h : wordLangArithFromHOL a = some b) : wordLangArithToHOL b = some a := by
  cases a <;> simp [wordLangArithFromHOL] at h <;>
    subst b <;> rfl

/-- Every accepted exact instruction survives projection and re-encoding.
No successful target evaluation is assumed. -/
theorem wordLangInstToHOL_of_fromHOL {width : Nat}
    (a : WordLangInst (BitVec width)) (b : WordInst (BitVec width))
    (h : wordLangInstFromHOL a = some b) : wordLangInstToHOL b = some a := by
  cases a with
  | skip => simp [wordLangInstFromHOL] at h
  | fp _ => simp [wordLangInstFromHOL] at h
  | const dest value =>
      simp [wordLangInstFromHOL] at h
      subst b
      rfl
  | arith operation =>
      cases hd : wordLangArithFromHOL operation with
      | none => simp [wordLangInstFromHOL, hd] at h
      | some projected =>
          simp [wordLangInstFromHOL, hd] at h
          subst b
          simp [wordLangInstToHOL, wordLangArithToHOL_of_fromHOL operation projected hd]
  | mem op dest address =>
      cases address with
      | addr base offset =>
          by_cases hz : offset = 0
          · simp only [wordLangInstFromHOL, if_pos hz, Option.some.injEq] at h
            subst b
            simp [wordLangInstToHOL, hz]
          · simp only [wordLangInstFromHOL, if_neg hz, Option.some.injEq] at h
            subst b
            rfl

/-- Unit-valued list encoding used by production cutsets is the same insertion
order as the exact Spt association-list reconstruction. -/
private theorem toNumSetMapFst (entries : List (Nat × Unit)) :
    LoopToWord.toNumSetHOL (entries.map Prod.fst) = sptFromAList entries := by
  induction entries with
  | nil => rfl
  | cons pair tail ih =>
      rcases pair with ⟨key, value⟩
      cases value
      simp only [List.map_cons, LoopToWord.toNumSetHOL, sptFromAList, ih]

/-- Re-encoding an enumerated exact cutset preserves every lookup. Spt tree
shape may normalize, so this states its actual finite-map semantics rather
than an unjustified syntactic tree equality. Flapjack carrier infrastructure. -/
theorem toNumSet_fromNumSet_lookup (tree : Spt Unit) (key : Nat) :
    sptLookup key (LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL tree)) =
      sptLookup key tree := by
  rw [LoopToWord.fromNumSetHOL, toNumSetMapFst,
    sptLookup_sptFromAList_sptToAList]

/-- Production cutset lists encode as exact unit Spt maps. This is Flapjack
carrier infrastructure; the roundtrip below must compare their lookups. -/
def wordCutsetsToHOL (sets : List Nat × List Nat) : WordLangCutsetsHOL :=
  (LoopToWord.toNumSetHOL sets.1, LoopToWord.toNumSetHOL sets.2)

/-- Partial production-program encoder into the exact HOL carrier. Rejection
is limited to the distinct five-register AddCarry operation or nested uses of
it. This is a carrier adapter, not an executable-semantics refinement theorem. -/
def wordLangProgToHOL {width : Nat} :
    WordProg (BitVec width) → Option (WordLangProgHOL (BitVec width))
  | .skip => some .skip
  | .move priority moves => some (.move priority moves)
  | .inst instruction => (wordLangInstToHOL instruction).map .inst
  | .assign name value => some (.assign name (wordExpToHOL value))
  | .get destination store => some (.get destination (wordStoreToHOL store))
  | .set store value => some (.set (wordStoreToHOL store) (wordExpToHOL value))
  | .store address value => some (.store (wordExpToHOL address) value)
  | .mustTerminate body => (wordLangProgToHOL body).map .mustTerminate
  | .call returns target arguments handler => do
      let returns ← match returns with
        | none => pure none
        | some (values, sets, returnBody, firstLabel, secondLabel) => do
            let returnBody ← wordLangProgToHOL returnBody
            pure (some (values, wordCutsetsToHOL sets, returnBody,
              firstLabel, secondLabel))
      let handler ← match handler with
        | none => pure none
        | some (exception, handlerBody, firstLabel, secondLabel) => do
            let handlerBody ← wordLangProgToHOL handlerBody
            pure (some (exception, handlerBody, firstLabel, secondLabel))
      pure (.call returns target arguments handler)
  | .seq first second => do
      let first ← wordLangProgToHOL first
      let second ← wordLangProgToHOL second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let thenBranch ← wordLangProgToHOL thenBranch
      let elseBranch ← wordLangProgToHOL elseBranch
      pure (.ite operator condition right thenBranch elseBranch)
  | .loop liveIn body liveOut => do
      let body ← wordLangProgToHOL body
      pure (.loop (Flapjack.LoopToWord.toNumSetHOL liveIn) body
        (Flapjack.LoopToWord.toNumSetHOL liveOut))
  | .alloc destination sets => some (.alloc destination (wordCutsetsToHOL sets))
  | .storeConsts source bitmap codeLength dataLength constants =>
      some (.storeConsts source bitmap codeLength dataLength constants)
  | .raise exception => some (.raise exception)
  | .return label values => some (.return label values)
  | .break label => some (.break label)
  | .continue label => some (.continue label)
  | .tick => some .tick
  | .opCurrHeap operator destination source =>
      some (.opCurrHeap operator destination source)
  | .locValue destination source => some (.locValue destination source)
  | .install codeBuffer codeLength dataBuffer dataLength sets =>
      some (.install codeBuffer codeLength dataBuffer dataLength
        (wordCutsetsToHOL sets))
  | .codeBufferWrite address value => some (.codeBufferWrite address value)
  | .dataBufferWrite address value => some (.dataBufferWrite address value)
  | .ffi function configuration configurationLength array arrayLength sets =>
      some (.ffi (Flapjack.Basis.Pure.MlString.ofString function) configuration configurationLength
        array arrayLength (wordCutsetsToHOL sets))
  | .shareInst operator name address =>
      some (.shareInst operator name (wordExpToHOL address))

/-- Independent exact-program normalization induced by cutset list carriers.
Instructions, expressions, names, control flow and labels remain identical;
only unit Spt cutsets are reconstructed from their original enumeration. -/
def wordLangProgNormalizeCutsets {width : Nat} :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .skip => .skip
  | .move priority moves => .move priority moves
  | .inst instruction => .inst instruction
  | .assign name value => .assign name value
  | .get destination store => .get destination store
  | .set store value => .set store value
  | .store address value => .store address value
  | .mustTerminate body => .mustTerminate (wordLangProgNormalizeCutsets body)
  | .call returns target arguments handler =>
      .call (match returns with
        | none => none
        | some (values, sets, body, l1, l2) =>
          some (values, wordCutsetsToHOL (wordCutsetsFromHOL sets),
            wordLangProgNormalizeCutsets body, l1, l2)) target arguments
        (match handler with
        | none => none
        | some (exception, body, l1, l2) =>
          some (exception, wordLangProgNormalizeCutsets body, l1, l2))
  | .seq first second =>
      .seq (wordLangProgNormalizeCutsets first) (wordLangProgNormalizeCutsets second)
  | .ite op condition right first second =>
      .ite op condition right (wordLangProgNormalizeCutsets first)
        (wordLangProgNormalizeCutsets second)
  | .loop liveIn body liveOut =>
      .loop (LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL liveIn))
        (wordLangProgNormalizeCutsets body)
        (LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL liveOut))
  | .alloc destination sets => .alloc destination (wordCutsetsToHOL (wordCutsetsFromHOL sets))
  | .storeConsts a b c d constants => .storeConsts a b c d constants
  | .raise exception => .raise exception
  | .return label values => .return label values
  | .break label => .break label
  | .continue label => .continue label
  | .tick => .tick
  | .opCurrHeap op destination source => .opCurrHeap op destination source
  | .locValue destination source => .locValue destination source
  | .install a b c d sets => .install a b c d (wordCutsetsToHOL (wordCutsetsFromHOL sets))
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .ffi function a b c d sets => .ffi function a b c d (wordCutsetsToHOL (wordCutsetsFromHOL sets))
  | .shareInst op name address => .shareInst op name address

/-- Every accepted exact program re-encodes with identical instructions,
expressions, names and control flow, up to the explicit cutset normalization.
This is Flapjack carrier infrastructure, not a HOL evaluator theorem. -/
theorem wordLangProgToHOL_of_fromHOL {width : Nat}
    (a : WordLangProgHOL (BitVec width)) (b : WordProg (BitVec width))
    (h : wordLangProgFromHOL a = some b) :
    wordLangProgToHOL b = some (wordLangProgNormalizeCutsets a) := by
  cases a with
  | inst instruction =>
      cases hd : wordLangInstFromHOL instruction with
      | none => simp [wordLangProgFromHOL, hd] at h
      | some projected =>
          simp [wordLangProgFromHOL, hd] at h
          subst b
          simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
            wordLangInstToHOL_of_fromHOL instruction projected hd]
  | mustTerminate body =>
      cases hd : wordLangProgFromHOL body with
      | none => simp [wordLangProgFromHOL, hd] at h
      | some projected =>
          simp [wordLangProgFromHOL, hd] at h
          subst b
          simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
            wordLangProgToHOL_of_fromHOL body projected hd]
  | seq first second =>
      cases h1 : wordLangProgFromHOL first <;>
        cases h2 : wordLangProgFromHOL second <;>
        simp [wordLangProgFromHOL, h1, h2] at h
      subst b
      simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
        wordLangProgToHOL_of_fromHOL first _ h1,
        wordLangProgToHOL_of_fromHOL second _ h2]
  | ite op cond right first second =>
      cases h1 : wordLangProgFromHOL first <;>
        cases h2 : wordLangProgFromHOL second <;>
        simp [wordLangProgFromHOL, h1, h2] at h
      subst b
      simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
        wordLangProgToHOL_of_fromHOL first _ h1,
        wordLangProgToHOL_of_fromHOL second _ h2]
  | loop liveIn body liveOut =>
      cases hd : wordLangProgFromHOL body with
      | none => simp [wordLangProgFromHOL, hd] at h
      | some projected =>
          simp [wordLangProgFromHOL, hd] at h
          subst b
          simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
            wordLangProgToHOL_of_fromHOL body projected hd]
  | call returns target arguments handler =>
      cases hReturnsCase : returns with
      | none =>
          cases hHandlerCase : handler with
          | none =>
              simp [wordLangProgFromHOL, hReturnsCase, hHandlerCase] at h
              subst b
              rfl
          | some handler =>
              rcases handler with ⟨exception, body, l1, l2⟩
              cases hd : wordLangProgFromHOL body <;>
                simp [wordLangProgFromHOL, hReturnsCase, hHandlerCase, hd] at h
              subst b
              simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
                wordLangProgToHOL_of_fromHOL body _ hd]
      | some returns =>
          rcases returns with ⟨values, sets, body, l1, l2⟩
          cases hd : wordLangProgFromHOL body <;>
            simp [wordLangProgFromHOL, hReturnsCase, hd] at h
          cases hHandlerCase : handler with
          | none =>
              simp [hHandlerCase] at h
              subst b
              simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
                wordLangProgToHOL_of_fromHOL body _ hd]
          | some handler =>
              rcases handler with ⟨exception, handlerBody, h1, h2⟩
              cases hh : wordLangProgFromHOL handlerBody <;> simp [hHandlerCase, hh] at h
              subst b
              simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
                wordLangProgToHOL_of_fromHOL body _ hd,
                wordLangProgToHOL_of_fromHOL handlerBody _ hh]
  | _ =>
      simp [wordLangProgFromHOL] at h
      subst b
      simp [wordLangProgToHOL, wordLangProgNormalizeCutsets,
        wordExpToHOL_fromHOL, wordStoreToHOL_fromHOL,
        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
  termination_by sizeOf a
  decreasing_by
    all_goals
      simp_wf
      subst a
      try rw [hReturnsCase]
      try rw [hHandlerCase]
      simp <;> omega

/-- Both cutset maps retain their entire lookup semantics after projection
and re-encoding; this applies to arbitrary exact cutsets, including empty ones. -/
theorem wordCutsetsToHOL_fromHOL_lookup (sets : WordLangCutsetsHOL) (key : Nat) :
    sptLookup key (wordCutsetsToHOL (wordCutsetsFromHOL sets)).1 =
        sptLookup key sets.1 ∧
      sptLookup key (wordCutsetsToHOL (wordCutsetsFromHOL sets)).2 =
        sptLookup key sets.2 :=
  ⟨toNumSet_fromNumSet_lookup sets.1 key, toNumSet_fromNumSet_lookup sets.2 key⟩

/-- Every exact compiler output has a production projection that re-encodes
as the same program up to the explicitly defined cutset normalization. There
is no target-run or caller-supplied decoder-success assumption. This proves a
carrier boundary, not refinement of the production evaluator by WordSem. -/
theorem wordLangProgToHOL_compHOL_image {width : Nat} [NeZero width]
    (context : Spt Nat) (source : HolLoopProg width) (labels : Nat × Nat) :
    ∃ projected : WordProg (BitVec width),
      wordLangProgFromHOL (LoopToWord.compHOL context source labels).1 = some projected ∧
      wordLangProgToHOL projected =
        some (wordLangProgNormalizeCutsets (LoopToWord.compHOL context source labels).1) := by
  cases hd : wordLangProgFromHOL (LoopToWord.compHOL context source labels).1 with
  | none => exact False.elim (wordLangProgFromHOL_compHOL_ne_none context source labels hd)
  | some projected => exact ⟨projected, rfl, wordLangProgToHOL_of_fromHOL _ projected hd⟩

end Flapjack

