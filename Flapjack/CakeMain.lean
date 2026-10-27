import Flapjack.Compiler.Backend.SourceToFlat.FromText
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.RiscV.CakeArtifactFormat
import Flapjack.Compiler.Inference.Infer.Diagnostics
import Flapjack.Compiler.Inference.Infer.TypesOutput
import Flapjack.CakeParser.Diagnostics
import Flapjack.CakeHelp
import Flapjack.CakeFeatures
import Flapjack.CakeParser.FromSexp.Ast

/-! Experimental CakeML source-to-RISC-V command. The frontend and backend
are still bounded ports, the original diagnostics and full CLI are incomplete,
and final output parity with CakeML has not been established. -/
namespace Flapjack.CakeMain
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.Basis.Pure.MlString

structure Options where
  excludePrelude : Bool := false
  skipTypeInference : Bool := false
  mainReturn : Bool := false
  onlyTypes : Bool := false
  seenTarget : Bool := false
  otherTarget : Option String := none
  seenExcludePrelude : Bool := false
  seenSkipTypeInference : Bool := false
  seenMainReturn : Bool := false
  seenSexp : Bool := false
  inputSexp : Bool := false
  multi : Option Bool := none
  known : Option Bool := none
  call : Option Bool := none
  inlineFactor : Option Nat := none
  maxApp : Option Nat := none
  maxBodySize : Option String := none
  inlineSize : Option Nat := none
  expCut : Option Nat := none
  splitMain : Option Bool := none
  tmc : Option Bool := none
  tailrec : Option Bool := none
  tagBits : Option Nat := none
  lenBits : Option Nat := none
  padBits : Option Nat := none
  lenSize : Option Nat := none
  emitEmptyFfi : Option Bool := none
  jump : Option Bool := none
  perfCallgraph : Option Bool := none
  hashSize : Option Nat := none
  regAlg : Option Nat := none
  gcKind : Option Flapjack.Compiler.Backend.DataToWord.GcKind := none

private def usage : String :=
  "Usage: cake [--target=riscv] [--sexp=true|false] [--exclude_prelude=true|false] " ++
  "[--types] " ++
  "[--skip_type_inference=true|false] [--main_return=true|false] " ++
  "[--multi=true|false] [--known=true|false] [--call=true|false] " ++
  "[--inline_factor=N] [--max_app=N] [--max_body_size=N] " ++
  "[--tmc=true|false] [--tailrec=true|false] [--split=true|false] " ++
  "[--inline_size=N] [--exp_cut=N] [--reg_alg=N] [--gc=G] " ++
  "[--tag_bits=N] [--len_bits=N] [--pad_bits=N] [--len_size=N] " ++
  "[--emit_empty_ffi=true|false] [--jump=true|false] [--perf_callgraph=true|false] " ++
  "[--hash_size=N] < input_file\n" ++
  "Experimental CakeML to RISC-V port; complete CakeML output parity is not yet established."

private def parseBool (text : String) : Option Bool :=
  if text == "true" then some true else if text == "false" then some false else none

private def findFlag (args : List String) (flagPrefix : String) : Option String :=
  (args.find? (fun arg => arg.startsWith flagPrefix)).map
    (fun arg => (arg.drop flagPrefix.length).toString)

private def parseNum (text : String) : Option Nat :=
  if text.toList.all (fun c => c ≥ '0' && c ≤ '9') then some (text.toNat?.getD 0) else none

private def configError (message : String) : String :=
  "### ERROR: config error\n" ++ message ++ "\n\n\n\nProgram exited with nonzero exit code.\n"

/-- The original driver validates the first occurrence of each top-level flag
before parsing backend options, collecting errors in declaration order. -/
private def topConfigErrors (args : List String) : List String := Id.run do
  let first := findFlag args
  let mut errors := []
  if let some target := first "--target=" then
    if !(target == "riscv" || target == "x64" || target == "arm8" || target == "mips") then
      errors := errors ++ [s!"Unrecognized 64-bit target option: {target}"]
  for flag in ["--sexp=", "--exclude_prelude=", "--skip_type_inference=", "--main_return="] do
    if let some value := first flag then
      if (parseBool value).isNone then
        errors := errors ++ [s!"Unable to parse as bool: {value} for flag: {flag}"]
  return errors

private def topConfigError (errors : List String) : String :=
  let separator := match errors with
    | [error] => if error.startsWith "Unrecognized 64-bit target option: " then "\n\n" else "\n\n\n"
    | _ => "\n\n\n"
  "### ERROR: config error\n" ++ String.intercalate "\n" errors ++
    separator ++ "Program exited with nonzero exit code.\n"

/-- Original backend configuration groups report errors in pass order, with
errors within the BVL group in the order used by `parse_bvl_conf`. -/
private def backendConfigErrors (args : List String) : List String := Id.run do
  let first := findFlag args
  let mut clos := []
  for (flag, isBool) in [("--multi=", true), ("--known=", true),
      ("--inline_factor=", false), ("--call=", true), ("--max_app=", false)] do
    if let some value := first flag then
      let valid := if isBool then (parseBool value).isSome else (parseNum value).isSome
      if !valid then
        clos := clos ++ [s!"Unable to parse as {if isBool then "bool" else "num"}: {value} for flag: {flag}"]
  if clos.isEmpty && ((first "--known=").bind parseBool).getD true then
    if let some value := first "--max_body_size=" then
      if (parseNum value).isNone then
        clos := clos ++ [s!"Unable to parse as num: {value} for flag: --max_body_size="]
  let mut bvl := []
  for (flag, isBool) in [("--inline_size=", false), ("--exp_cut=", false),
      ("--split=", true), ("--tmc=", true), ("--tailrec=", true)] do
    if let some value := first flag then
      let valid := if isBool then (parseBool value).isSome else (parseNum value).isSome
      if !valid then
        bvl := bvl ++ [s!"Unable to parse as {if isBool then "bool" else "num"}: {value} for flag: {flag}"]
  let mut groups := []
  if !clos.isEmpty then groups := groups ++ [String.intercalate "\n" clos ++ "\n\n"]
  if !bvl.isEmpty then groups := groups ++ [String.intercalate "\n" bvl ++ "\n\n"]
  if let some value := first "--reg_alg=" then
    if (parseNum value).isNone then
      groups := groups ++ [s!"Unable to parse as num: {value} for flag: --reg_alg=\n\n"]
  let mut data := []
  for flag in ["--tag_bits=", "--len_bits=", "--pad_bits=", "--len_size="] do
    if let some value := first flag then
      if (parseNum value).isNone then
        data := data ++ [s!"Unable to parse as num: {value} for flag: {flag}"]
  if let some value := first "--gc=" then
    if value != "none" && value != "simple" then
      if value.startsWith "gen" then
        let parts := (value.drop 3).toString.splitOn "," |>.filter (fun s => !s.isEmpty)
        if let some bad := parts.find? (fun s => (parseNum s).isNone) then
          data := data ++ [s!"Error parsing GenGC argument: Unable to parse as num: {bad}"]
      else data := data ++ [s!"Unrecognized GC option: {value}"]
  if let some value := first "--emit_empty_ffi=" then
    if (parseBool value).isNone then
      data := data ++ [s!"Unable to parse as bool: {value} for flag: --emit_empty_ffi="]
  if !data.isEmpty then groups := groups ++ [String.intercalate "\n" data ++ "\n\n"]
  let mut stackError : Option String := none
  for flag in ["--jump=", "--perf_callgraph="] do
    if stackError.isNone then
      if let some value := first flag then
        if (parseBool value).isNone then
          stackError := some s!"Unable to parse as bool: {value} for flag: {flag}"
  if let some error := stackError then groups := groups ++ [error ++ "\n"]
  if let some value := first "--hash_size=" then
    if (parseNum value).isNone then
      groups := groups ++ [s!"Unable to parse as num: {value} for flag: --hash_size=\n"]
  return groups

private def parseArgs : List String → Options → Except String Options
  | [], options => .ok options
  | arg :: args, options =>
      if arg.startsWith "--target=" then
        if options.seenTarget then parseArgs args options
        else if arg == "--target=riscv" then parseArgs args { options with seenTarget := true }
        else parseArgs args { options with seenTarget := true, otherTarget := some arg }
      else if arg == "--no_warn" then parseArgs args options
      else if arg == "--types" then parseArgs args { options with onlyTypes := true }
      else if arg.startsWith "--sexp=" then
        if options.seenSexp then parseArgs args options
        else match parseBool (arg.drop "--sexp=".length |>.toString) with
        | some value => parseArgs args { options with seenSexp := true, inputSexp := value }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--multi=" then
        if options.multi.isSome then parseArgs args options else
        match parseBool (arg.drop "--multi=".length |>.toString) with
        | some b => parseArgs args { options with multi := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--known=" then
        if options.known.isSome then parseArgs args options else
        match parseBool (arg.drop "--known=".length |>.toString) with
        | some b => parseArgs args { options with known := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--call=" then
        if options.call.isSome then parseArgs args options else
        match parseBool (arg.drop "--call=".length |>.toString) with
        | some b => parseArgs args { options with call := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--inline_factor=" then
        if options.inlineFactor.isSome then parseArgs args options else
        match parseNum (arg.drop "--inline_factor=".length |>.toString) with
        | some n => parseArgs args { options with inlineFactor := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--max_app=" then
        if options.maxApp.isSome then parseArgs args options else
        match parseNum (arg.drop "--max_app=".length |>.toString) with
        | some n => parseArgs args { options with maxApp := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--max_body_size=" then
        if options.maxBodySize.isSome then parseArgs args options else
        parseArgs args { options with maxBodySize := some (arg.drop "--max_body_size=".length |>.toString) }
      else if arg.startsWith "--tag_bits=" then
        if options.tagBits.isSome then parseArgs args options else
        match parseNum (arg.drop "--tag_bits=".length |>.toString) with
        | some n => parseArgs args { options with tagBits := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--len_bits=" then
        if options.lenBits.isSome then parseArgs args options else
        match parseNum (arg.drop "--len_bits=".length |>.toString) with
        | some n => parseArgs args { options with lenBits := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--pad_bits=" then
        if options.padBits.isSome then parseArgs args options else
        match parseNum (arg.drop "--pad_bits=".length |>.toString) with
        | some n => parseArgs args { options with padBits := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--len_size=" then
        if options.lenSize.isSome then parseArgs args options else
        match parseNum (arg.drop "--len_size=".length |>.toString) with
        | some n => parseArgs args { options with lenSize := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--emit_empty_ffi=" then
        if options.emitEmptyFfi.isSome then parseArgs args options else
        match parseBool (arg.drop "--emit_empty_ffi=".length |>.toString) with
        | some b => parseArgs args { options with emitEmptyFfi := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--jump=" then
        if options.jump.isSome then parseArgs args options else
        match parseBool (arg.drop "--jump=".length |>.toString) with
        | some b => parseArgs args { options with jump := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--perf_callgraph=" then
        if options.perfCallgraph.isSome then parseArgs args options else
        match parseBool (arg.drop "--perf_callgraph=".length |>.toString) with
        | some b => parseArgs args { options with perfCallgraph := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--hash_size=" then
        if options.hashSize.isSome then parseArgs args options else
        match parseNum (arg.drop "--hash_size=".length |>.toString) with
        | some n => parseArgs args { options with hashSize := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--inline_size=" then
        if options.inlineSize.isSome then parseArgs args options else
        match parseNum (arg.drop "--inline_size=".length |>.toString) with
        | some n => parseArgs args { options with inlineSize := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--exp_cut=" then
        if options.expCut.isSome then parseArgs args options else
        match parseNum (arg.drop "--exp_cut=".length |>.toString) with
        | some n => parseArgs args { options with expCut := some n }
        | none => .error s!"invalid numeric option: {arg}"
      else if arg.startsWith "--split=" then
        if options.splitMain.isSome then parseArgs args options else
        match parseBool (arg.drop "--split=".length |>.toString) with
        | some b => parseArgs args { options with splitMain := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--tmc=" then
        if options.tmc.isSome then parseArgs args options else
        match parseBool (arg.drop "--tmc=".length |>.toString) with
        | some b => parseArgs args { options with tmc := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--tailrec=" then
        if options.tailrec.isSome then parseArgs args options else
        match parseBool (arg.drop "--tailrec=".length |>.toString) with
        | some b => parseArgs args { options with tailrec := some b }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--reg_alg=" then
        let digits := (arg.drop "--reg_alg=".length).toString
        if options.regAlg.isSome then parseArgs args options
        else if digits.toList.all (fun c => c ≥ '0' && c ≤ '9') then
          let n := digits.toNat?.getD 0
          parseArgs args { options with regAlg := some n }
        else .error (configError s!"Unable to parse as num: {digits} for flag: --reg_alg=")
      else if arg.startsWith "--gc=" then
        let value := (arg.drop "--gc=".length).toString
        if options.gcKind.isSome then parseArgs args options
        else if value == "none" then parseArgs args { options with gcKind := some .none }
        else if value == "simple" then parseArgs args { options with gcKind := some .simple }
        else if value.startsWith "gen" then
          let parts := (value.drop 3).toString.splitOn "," |>.filter (fun s => !s.isEmpty)
          match parts.find? (fun s => !s.toList.all (fun c => c ≥ '0' && c ≤ '9')) with
          | some bad => .error (configError s!"Error parsing GenGC argument: Unable to parse as num: {bad}")
          | none => parseArgs args { options with gcKind := some (.generational (parts.map (fun s => s.toNat?.getD 0))) }
        else .error (configError s!"Unrecognized GC option: {value}")
      else if arg.startsWith "--exclude_prelude=" then
        if options.seenExcludePrelude then parseArgs args options else
        match parseBool (arg.drop "--exclude_prelude=".length |>.toString) with
        | some b => parseArgs args { options with excludePrelude := b, seenExcludePrelude := true }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--skip_type_inference=" then
        if options.seenSkipTypeInference then parseArgs args options else
        match parseBool (arg.drop "--skip_type_inference=".length |>.toString) with
        | some b => parseArgs args { options with skipTypeInference := b, seenSkipTypeInference := true }
        | none => .error s!"invalid Boolean option: {arg}"
      else if arg.startsWith "--main_return=" then
        if options.seenMainReturn then parseArgs args options else
        match parseBool (arg.drop "--main_return=".length |>.toString) with
        | some b => parseArgs args { options with mainReturn := b, seenMainReturn := true }
        | none => .error s!"invalid Boolean option: {arg}"
      else if (arg == "--print_sexp" || arg == "--explore") && options.onlyTypes then
        parseArgs args options
      else if arg == "--print_sexp" || arg == "--explore" || arg == "--pancake" ||
          arg == "--help" || arg == "--version" || arg == "--repl" || arg == "--candle" ||
          arg.startsWith "--pancake_feature=" then
        .error s!"unsupported option: {arg}"
      -- The original driver's flag lookups ignore arguments they do not recognize.
      else parseArgs args options

private def errorMessage : PrimitiveCheckedSourceResult → Option String
  | .parseExhausted => some "parser or lexer exhausted its execution bound"
  | .parseRejected => some "parsing failed"
  | .inferenceError e => some s!"type inference failed: {repr e}"
  | .backendRejected => some "compiler backend could not compile this program"
  | .success _ _ _ => none

/-- Scale the execution bound with the source size. The compiler remains a
bounded port; no general sufficiency theorem is claimed for this bound. -/
private def sourceFuel (source : List HolChar) : Nat :=
  10000 + 16 * source.length

/-- Parse ordinary CakeML text or the bootstrap S-expression encoding. Both
paths are bounded and the S-expression decoder's correspondence is not yet
proved. -/
private def parseInput (options : Options) (fuel : Nat) (source : List HolChar) :
    Flapjack.CakeParser.Frontend.ParseResult :=
  if options.inputSexp then
    match Flapjack.CakeParser.Sexp.parseFuel fuel source with
    | none => .rejected
    | some sexp => match Flapjack.CakeParser.FromSexp.decodeProgramFuel fuel sexp with
      | none => .rejected
      | some decls => .success decls
  else Flapjack.CakeParser.Frontend.parseSourceFuel fuel fuel source

/-- Run the currently supported CakeML frontend and backend options. This is
Flapjack CLI infrastructure, not a port of the full HOL compiler driver. -/
def compileBytes (options : Options) (source : List HolChar) : PrimitiveCheckedSourceResult := Id.run do
  let base := RiscVConfig.riscvBackendConfigExecutable
  let maxApp := options.maxApp.getD base.closConf.maxApp
  let inlineFactor := options.inlineFactor.getD ClosKnown.defaultInlineFactor
  let maxBodySize := (options.maxBodySize.bind parseNum).getD
    (ClosKnown.defaultMaxBodySize maxApp inlineFactor)
  let knownConf := if options.known.getD base.closConf.knownConf.isSome then
    some (ClosKnown.mkConfig maxBodySize inlineFactor) else none
  let config := { base with
    closConf := { base.closConf with
      doMti := options.multi.getD base.closConf.doMti
      doCall := options.call.getD base.closConf.doCall
      maxApp := maxApp
      knownConf := knownConf }
    bvlConf := { base.bvlConf with
      inlineSizeLimit := options.inlineSize.getD base.bvlConf.inlineSizeLimit
      expCut := options.expCut.getD base.bvlConf.expCut
      splitMainAtSeq := options.splitMain.getD base.bvlConf.splitMainAtSeq
      doTmc := options.tmc.getD base.bvlConf.doTmc
      doTailrec := options.tailrec.getD base.bvlConf.doTailrec }
    wordToWordConf := { base.wordToWordConf with regAlg := options.regAlg.getD base.wordToWordConf.regAlg }
    dataConf := { base.dataConf with
      tagBits := options.tagBits.getD base.dataConf.tagBits
      lenBits := options.lenBits.getD base.dataConf.lenBits
      padBits := options.padBits.getD base.dataConf.padBits
      lenSize := options.lenSize.getD base.dataConf.lenSize
      callEmptyFfi := options.emitEmptyFfi.getD base.dataConf.callEmptyFfi
      gcKind := options.gcKind.getD base.dataConf.gcKind }
    stackConf := { base.stackConf with
      jump := options.jump.getD base.stackConf.jump
      perfCalls := options.perfCallgraph.getD base.stackConf.perfCalls }
    labConf := { base.labConf with hashSize := options.hashSize.getD base.labConf.hashSize } }
  let fuel := sourceFuel source
  match parseInput options fuel source with
  | .exhausted => return .parseExhausted
  | .rejected => return .parseRejected
  | .success decls =>
    let full := if options.excludePrelude then decls else Flapjack.Basis.BasisProg.basis ++ decls
    if !options.skipTypeInference then
      match Flapjack.Compiler.Inference.Infer.Core.inferProgramFuel fuel fuel full with
      | .error e => return .inferenceError e
      | .ok _ => pure ()
    match compileCakeToRiscVConfiguredFuel fuel config full with
    | none => return .backendRejected
    | some (bytes, bitmaps, config) => return .success bytes bitmaps config

/-- Parse and infer the input for the driver's `--types` mode. Errors follow
the same path as ordinary compilation; no backend pass is run on success. -/
private def inferTypesBytes (options : Options) (source : List HolChar) :
    Except PrimitiveCheckedSourceResult (List HolChar) := do
  let fuel := sourceFuel source
  let decls ← match parseInput options fuel source with
    | .exhausted => .error .parseExhausted
    | .rejected => .error .parseRejected
    | .success ds => .ok ds
  let full := if options.excludePrelude then decls else Flapjack.Basis.BasisProg.basis ++ decls
  let env ← if options.skipTypeInference then
    .ok Flapjack.Compiler.Inference.Infer.initConfig
  else match Flapjack.Compiler.Inference.Infer.Core.inferProgramFuel fuel fuel full with
    | .error e => .error (.inferenceError e)
    | .ok env => .ok env
  return Flapjack.Compiler.Inference.Infer.TypesOutput.render env

def main (args : List String) : IO UInt32 := do
  if args.contains "--repl" || args.contains "--candle" then
    IO.eprintln s!"cake: interactive mode is not supported\n{usage}"
    return 2
  if args.contains "--help" then
    IO.print Flapjack.CakeHelp.text
    return 0
  if args.contains "--version" then
    IO.eprintln s!"cake: unsupported option: --version\n{usage}"
    return 2
  if let some feature := findFlag args "--pancake_feature=" then
    IO.print (if Flapjack.CakeFeatures.enabled feature then "true" else "false")
    return 0
  let errors := topConfigErrors args
  if !errors.isEmpty then
    IO.eprint (topConfigError errors)
    return 1
  let errors := backendConfigErrors args
  if !errors.isEmpty then
    IO.eprint ("### ERROR: config error\n" ++ String.join errors ++
      "\n\nProgram exited with nonzero exit code.\n")
    return 1
  -- The original driver checks these flags by membership, independent of order.
  match parseArgs args { onlyTypes := args.contains "--types" } with
  | .error message =>
    if message.startsWith "### ERROR: config error\n" then
      IO.eprint message
      return 1
    IO.eprintln s!"cake: {message}\n{usage}"
    return 2
  | .ok options =>
    if !options.onlyTypes then
      if let some target := options.otherTarget then
        IO.eprintln s!"cake: unsupported option: {target}\n{usage}"
        return 2
    let input ← (← IO.getStdin).readBinToEnd
    let chars := input.data.toList.map (fun c => BitVec.ofNat 8 c.toNat)
    let typeOutput := if options.onlyTypes then some (inferTypesBytes options chars) else none
    if let some (.ok bytes) := typeOutput then
      let stderr ← IO.getStderr
      stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
      return 0
    let result := match typeOutput with
      | some (.error result) => result
      | _ => compileBytes options chars
    if let .parseRejected := result then
      if options.inputSexp then
        IO.eprint "### ERROR: parse error\nParsing of sexp syntax failed\nProgram exited with nonzero exit code.\n"
        return 1
      if let some bytes := Flapjack.CakeParser.Diagnostics.renderUnconsumedToken (sourceFuel chars) chars then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
    if let .inferenceError error := result then
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderUnsupportedPrimitive chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderUndefinedVariable chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderUndefinedConstructor chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderTypeMismatch chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderBindingError chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderUnboundTypeVariable chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderValueRestriction chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
      if let some bytes := Flapjack.Compiler.Inference.Infer.Diagnostics.renderDatatypeError chars error then
        let stderr ← IO.getStderr
        stderr.write (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
        return 1
    if let some message := errorMessage result then
      IO.eprintln s!"cake: {message}"
      return 1
    match result with
    | .success bytes bitmaps config =>
      IO.print (Flapjack.RiscV.CakeArtifactFormat.assembly bytes bitmaps config options.mainReturn)
      return 0
    | _ => return 1

end Flapjack.CakeMain

def main (args : List String) : IO UInt32 := Flapjack.CakeMain.main args
