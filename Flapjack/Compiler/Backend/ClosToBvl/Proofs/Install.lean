import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply

/-! Value decoding needed by the dynamic-installation simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- A source byte list and a related target value decode to identical bytes. -/
theorem install_valueToBytes_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (bytes : List (BitVec 8))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToBytes source = some bytes) :
    BvlSem.valueToBytes target = some bytes := by
  have sourceList := (ClosSem.valueToBytes_eq_some source bytes).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = bytes.map (fun b => BvlSem.Value.number b.toNat) := by
    clear decoded sourceList targetList related
    induction bytes generalizing values with
    | nil => cases valuesRel; rfl
    | cons byte rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_number_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToBytes_eq_some target bytes).2
  simpa [valuesEq] using targetList

/-- A source word list and a related target value decode to identical words. -/
theorem install_valueToWords_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (words : List (BitVec 64))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToWords source = some words) :
    BvlSem.valueToWords target = some words := by
  have sourceList := (ClosSem.valueToWords_eq_some source words).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = words.map BvlSem.Value.word64 := by
    clear decoded sourceList targetList related
    induction words generalizing values with
    | nil => cases valuesRel; rfl
    | cons word rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_word64_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToWords_eq_some target words).2
  simpa [valuesEq] using targetList

/-- Compiling a program whose first entry has arity zero preserves its first
location, shifted past the generated closure-call stubs. -/
theorem compileProgExps_head_zero (maxApp start : Nat) (expression : ClosLang.Exp)
    (rest : List (Nat × Nat × ClosLang.Exp)) :
    ∃ body tail, compileProgExpsHOL maxApp ((start, 0, expression) :: rest) =
      (start + numStubs maxApp, 0, body) :: tail := by
  cases first : compileExpHOL maxApp expression [] with
  | mk body aux =>
    cases remaining : compileExpListHOL maxApp (rest.map (fun (_, _, exp) => exp)) aux with
    | mk bodies finalAux =>
      refine ⟨body, (rest.zip bodies).map (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp)) ++ finalAux, ?_⟩
      simp [compileProgExpsHOL, compileExps_eq_list, compileExpListHOL, first, remaining]

/-- Every incremental compilation has a zero-arity entry for the extracted
main location, even when the expression list is empty. -/
theorem compileInc_head (maxApp : Nat) (program : ClosSem.Program) :
    ∃ start body tail, (extractName program.1).1 = start ∧
      compileInc maxApp program = (start + numStubs maxApp, 0, body) :: tail := by
  cases extract : extractName program.1 with
  | mk start expressions =>
    have chain : ∃ expression rest, chainExps start expressions ++ program.2 =
        (start, 0, expression) :: rest := by
      cases expressions with
      | nil => simp [chainExps]
      | cons first remaining =>
        cases remaining with
        | nil => simp [chainExps]
        | cons second tail => simp [chainExps]
    obtain ⟨expression, rest, chainEq⟩ := chain
    obtain ⟨body, tail, compiled⟩ := compileProgExps_head_zero maxApp start expression rest
    refine ⟨start, body, tail, ?_, ?_⟩
    · rfl
    · simpa [compileInc, extract, chainEq] using compiled

/-- A source compiler result accepted by the installation oracle is also
accepted by the target installer, with the incremental main entry returned. -/
theorem install_target_run {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourceBytes sourceWords : ClosSem.Value)
    (targetBytes targetWords : BvlSem.Value) (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (config nextConfig : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (bytesRel : vRel s.maxApp f t.refs t.code sourceBytes targetBytes)
    (wordsRel : vRel s.maxApp f t.refs t.code sourceWords targetWords)
    (bytesDecoded : ClosSem.valueToBytes sourceBytes = some bytes)
    (wordsDecoded : ClosSem.valueToWords sourceWords = some words)
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (sourceNext : (s.compileOracle 1).1 = nextConfig)
    (compiled : s.compile config (expressions, auxiliary) = some (bytes, words, nextConfig))
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    ∃ start body tail,
      (extractName expressions).1 = start ∧
      compileInc s.maxApp (expressions, auxiliary) = (start + numStubs s.maxApp, 0, body) :: tail ∧
      BvlSem.doInstall (R := BvlSem.Value) [targetBytes, targetWords] t =
        .val (.codePtr (start + numStubs s.maxApp), { t with
          code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
          compileOracle := fun n => t.compileOracle (n + 1) }) := by
  obtain ⟨start, body, tail, extracted, program⟩ := compileInc_head s.maxApp (expressions, auxiliary)
  have targetBytesDecoded := install_valueToBytes_related sourceBytes targetBytes bytes bytesRel bytesDecoded
  have targetWordsDecoded := install_valueToWords_related sourceWords targetWords words wordsRel wordsDecoded
  obtain ⟨headEq, compileEq, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have targetCompile : t.compile config (compileInc s.maxApp (expressions, auxiliary)) = some (bytes, words, nextConfig) := by
    simpa [compileEq] using compiled
  have targetNext : (t.compileOracle 1).1 = nextConfig := by
    have oracleEq := oracle.2.1
    have atOne := congrFun oracleEq 1
    simpa [BackendProps.pureCo, sourceNext] using congrArg Prod.fst atOne
  have fresh' : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa only [targetHead] using fresh
  have nodup' : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa only [targetHead] using nodup
  rw [program] at fresh' nodup' targetCompile
  refine ⟨start, body, tail, extracted, program, ?_⟩
  simp [BvlSem.doInstall, targetBytesDecoded, targetWordsDecoded, targetHead, program, targetCompile, targetNext]
  simpa [and_assoc] using And.intro fresh' nodup'

end Flapjack.Compiler.Backend.ClosToBvl
