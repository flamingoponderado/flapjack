import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192
private def base {width : Nat} [NeZero width] : WordSemStateFiniteExact width Unit Unit where
  locals := .ln
  localsSize := none
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := none
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ i => i
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 0
  code := .ln
  be := false
  ffi := { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }
-- cl_read_1_0_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (some [], some [none, none, none, none, none, none], [none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_0_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [none, none, none, none, none, none], [some (.word 1), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 1), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [.word 1], some [some (.word 1), none, none, none, none, none, none, none], [some (.word 1), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_1_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 1), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, none, none]) := by decide +kernel

-- cl_read_1_2_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_2_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 1], some [some (.word 1), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_2_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12], some [some (.loc 101 102), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 1, .loc 11 12], some [some (.word 1), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12, .word 1], some [some (.loc 101 102), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 1, .loc 11 12, .word 1], some [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none], [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_2_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 1), none, some (.loc 11 12), none, some (.word 1), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [none, none, none, none, none, none], [some (.word 1), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 1), none, none, none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_3_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [.word 1], some [some (.word 1), none, none, none, none, none, none, none], [some (.word 1), none, none, none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_3_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_3_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 1), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_4_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [none, none, none, none, none, none], [none, none, some (.loc 21 22), none, none, none]) := by decide +kernel

-- cl_read_1_4_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_4_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_4_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22], some [some (.loc 101 102), none, some (.loc 21 22), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_4_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_4_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_1_4_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_1_4_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0, .word 1], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_4_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_4_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_1_5_0_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), none, none]) := by decide +kernel

-- cl_read_1_5_0_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_5_1_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91], some [some (.loc 90 91), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_5_1_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 0], some [some (.loc 101 102), none, some (.word 0), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_5_2_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 0], some [some (.loc 90 91), none, some (.word 0), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_5_2_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 0, .word 1], some [some (.loc 101 102), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_5_3_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 0, .word 1], some [some (.loc 90 91), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_1_5_3_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 0, .word 1, .word 0], some [some (.loc 101 102), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_1_5_6_0
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 0, .word 1, .word 0, .word 1, .word 0], some [some (.loc 90 91), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, some (.word 1), none, none, none, none, none]) := by decide +kernel

-- cl_read_1_5_6_1
example : (fun s : WordSemStateFiniteExact 1 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 1 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 0, .word 1, .word 0, .word 1, .word 0, .word 1], some [some (.loc 101 102), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 0), some (.word 1), some (.word 1), none, some (.word 0), none, some (.word 1), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (some [], some [none, none, none, none, none, none], [none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_0_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [none, none, none, none, none, none], [some (.word 3), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 3), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [.word 3], some [some (.word 3), none, none, none, none, none, none, none], [some (.word 3), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_1_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 3), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, none, none]) := by decide +kernel

-- cl_read_2_2_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_2_2_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 3], some [some (.word 3), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_2_2_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12], some [some (.loc 101 102), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 3, .loc 11 12], some [some (.word 3), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12, .word 3], some [some (.loc 101 102), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 3, .loc 11 12, .word 3], some [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none], [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_2_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 3), none, some (.loc 11 12), none, some (.word 3), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [none, none, none, none, none, none], [some (.word 3), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 3), none, none, none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_3_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [.word 3], some [some (.word 3), none, none, none, none, none, none, none], [some (.word 3), none, none, none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_3_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_3_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 3), none, none, none, some (.word 0), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_4_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [none, none, none, none, none, none], [none, none, some (.loc 21 22), none, none, none]) := by decide +kernel

-- cl_read_2_4_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_4_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_4_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22], some [some (.loc 101 102), none, some (.loc 21 22), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_2_4_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_2_4_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_2_4_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_2_4_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0, .word 1], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_4_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_4_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 1), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_2_5_0_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), none, none]) := by decide +kernel

-- cl_read_2_5_0_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_2_5_1_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91], some [some (.loc 90 91), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_2_5_1_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2], some [some (.loc 101 102), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_5_2_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2], some [some (.loc 90 91), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_2_5_2_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_2_5_3_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, some (.word 1), none, none, none]) := by decide +kernel

-- cl_read_2_5_3_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 0], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 0), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, some (.word 1), none, some (.word 2), none, none, none]) := by decide +kernel

-- cl_read_2_5_6_0
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3, .word 0, .word 1, .word 2], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, some (.word 0), none, some (.word 1), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, some (.word 1), none, some (.word 2), none, some (.word 3), none, none, none, none, none]) := by decide +kernel

-- cl_read_2_5_6_1
example : (fun s : WordSemStateFiniteExact 2 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 2 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 0, .word 1, .word 2, .word 3], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 0), none, some (.word 1), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 3), some (.word 3), none, some (.word 0), none, some (.word 1), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (some [], some [none, none, none, none, none, none], [none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_0_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_1_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, none, none]) := by decide +kernel

-- cl_read_8_2_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_8_2_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_8_2_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12], some [some (.loc 101 102), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12], some [some (.word 7), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12, .word 255], some [some (.loc 101 102), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12, .word 255], some [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_2_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_8_3_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_8_3_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_3_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_4_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [none, none, none, none, none, none], [none, none, some (.loc 21 22), none, none, none]) := by decide +kernel

-- cl_read_8_4_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_8_4_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, none, none]) := by decide +kernel

-- cl_read_8_4_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22], some [some (.loc 101 102), none, some (.loc 21 22), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_8_4_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_8_4_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_8_4_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_8_4_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 0, .word 9], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_4_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_4_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 0), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_8_5_0_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), none, none]) := by decide +kernel

-- cl_read_8_5_0_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_8_5_1_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91], some [some (.loc 90 91), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_8_5_1_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2], some [some (.loc 101 102), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_8_5_2_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2], some [some (.loc 90 91), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_8_5_2_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_8_5_3_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_8_5_3_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none]) := by decide +kernel

-- cl_read_8_5_6_0
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3, .word 4, .word 5, .word 6], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_8_5_6_1
example : (fun s : WordSemStateFiniteExact 8 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 8 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4, .word 5, .word 6, .word 7], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (some [], some [none, none, none, none, none, none], [none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_0_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_1_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, none, none]) := by decide +kernel

-- cl_read_64_2_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_64_2_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_64_2_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12], some [some (.loc 101 102), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12], some [some (.word 7), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12, .word 255], some [some (.loc 101 102), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12, .word 255], some [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_2_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_64_3_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_64_3_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_3_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_4_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [none, none, none, none, none, none], [none, none, some (.loc 21 22), none, none, none]) := by decide +kernel

-- cl_read_64_4_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, none, none]) := by decide +kernel

-- cl_read_64_4_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, none, none]) := by decide +kernel

-- cl_read_64_4_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22], some [some (.loc 101 102), none, some (.loc 21 22), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_64_4_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_64_4_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 256], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 256), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_64_4_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_64_4_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 256, .word 9], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_4_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_4_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_64_5_0_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), none, none]) := by decide +kernel

-- cl_read_64_5_0_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_64_5_1_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91], some [some (.loc 90 91), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_64_5_1_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2], some [some (.loc 101 102), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_64_5_2_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2], some [some (.loc 90 91), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_64_5_2_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_64_5_3_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_64_5_3_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none]) := by decide +kernel

-- cl_read_64_5_6_0
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3, .word 4, .word 5, .word 6], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_64_5_6_1
example : (fun s : WordSemStateFiniteExact 64 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 64 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4, .word 5, .word 6, .word 7], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (some [], some [none, none, none, none, none, none], [none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_0_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := .ln }) = (none, none, [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_1_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 0 (.word 7) (.ln) }) = (none, none, [some (.word 7), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, none, none]) := by decide +kernel

-- cl_read_80_2_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_80_2_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none]) := by decide +kernel

-- cl_read_80_2_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12], some [some (.loc 101 102), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12], some [some (.word 7), none, some (.loc 11 12), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.loc 11 12, .word 255], some [some (.loc 101 102), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (some [.word 7, .loc 11 12, .word 255], some [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none], [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_2_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 255) (sptInsert 2 (.loc 11 12) (sptInsert 0 (.word 7) (.ln))) }) = (none, none, [some (.word 7), none, some (.loc 11 12), none, some (.word 255), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [none, none, none, none, none, none], [some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_80_3_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (some [.word 7], some [some (.word 7), none, none, none, none, none, none, none], [some (.word 7), none, none, none, some (.word 8), none, none, none]) := by decide +kernel

-- cl_read_80_3_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_3_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 4 (.word 8) (sptInsert 0 (.word 7) (.ln)) }) = (none, none, [some (.word 7), none, none, none, some (.word 8), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_4_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [none, none, none, none, none, none], [none, none, some (.loc 21 22), none, none, none]) := by decide +kernel

-- cl_read_80_4_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, none, none]) := by decide +kernel

-- cl_read_80_4_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, none, none]) := by decide +kernel

-- cl_read_80_4_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22], some [some (.loc 101 102), none, some (.loc 21 22), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_80_4_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none]) := by decide +kernel

-- cl_read_80_4_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 256], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 256), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_80_4_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none]) := by decide +kernel

-- cl_read_80_4_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (some [.loc 21 22, .word 256, .word 9], some [some (.loc 101 102), none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, none, none, none, none, none, none], [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_4_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_4_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 8 (.loc 31 32) (sptInsert 6 (.word 9) (sptInsert 4 (.word 256) (sptInsert 2 (.loc 21 22) (.ln)))) }) = (none, none, [none, none, some (.loc 21 22), none, some (.word 256), none, some (.word 9), none, some (.loc 31 32), none, none, none, none, none, none, none, none, none, none, none]) := by decide +kernel

-- cl_read_80_5_0_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), none, none]) := by decide +kernel

-- cl_read_80_5_0_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [] s, (WordSemStateFiniteExact.getVars [] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [], some [some (.loc 101 102), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_80_5_1_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0] s, (WordSemStateFiniteExact.getVars [0] s).map (fun xs => [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91], some [some (.loc 90 91), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, none, none]) := by decide +kernel

-- cl_read_80_5_1_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2] s, (WordSemStateFiniteExact.getVars [2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2], some [some (.loc 101 102), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_80_5_2_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2] s, (WordSemStateFiniteExact.getVars [0, 2] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2], some [some (.loc 90 91), none, some (.word 2), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, none, none]) := by decide +kernel

-- cl_read_80_5_2_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4] s, (WordSemStateFiniteExact.getVars [2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_80_5_3_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4] s, (WordSemStateFiniteExact.getVars [0, 2, 4] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, none, none]) := by decide +kernel

-- cl_read_80_5_3_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6] s, (WordSemStateFiniteExact.getVars [2, 4, 6] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none]) := by decide +kernel

-- cl_read_80_5_6_0
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s, (WordSemStateFiniteExact.getVars [0, 2, 4, 6, 8, 10] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n (sptFromList2 xs))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.loc 90 91, .word 2, .word 3, .word 4, .word 5, .word 6], some [some (.loc 90 91), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none]) := by decide +kernel

-- cl_read_80_5_6_1
example : (fun s : WordSemStateFiniteExact 80 Unit Unit => (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s, (WordSemStateFiniteExact.getVars [2, 4, 6, 8, 10, 12] s).map (fun xs => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n (sptFromList2 (.loc 101 102 :: xs)))), [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 99, 900].map (fun n => sptLookup n s.locals))) ({ (base : WordSemStateFiniteExact 80 Unit Unit) with locals := sptInsert 12 (.word 7) (sptInsert 10 (.word 6) (sptInsert 8 (.word 5) (sptInsert 6 (.word 4) (sptInsert 4 (.word 3) (sptInsert 3 (.word 99) (sptInsert 0 (.loc 90 91) (sptInsert 2 (.word 2) (sptInsert 0 (.word 1) (.ln))))))))) }) = (some [.word 2, .word 3, .word 4, .word 5, .word 6, .word 7], some [some (.loc 101 102), none, some (.word 2), none, some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none], [some (.loc 90 91), none, some (.word 2), some (.word 99), some (.word 3), none, some (.word 4), none, some (.word 5), none, some (.word 6), none, some (.word 7), none, none, none, none, none, none, none]) := by decide +kernel

-- cl_prefix_Nat_0_0_0
example : (sptLookup 0 (sptFromList2 ([]: List Nat)), sptLookup 0 (sptFromList2 ([]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_0_1
example : (sptLookup 1 (sptFromList2 ([]: List Nat)), sptLookup 1 (sptFromList2 ([]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_0_2
example : (sptLookup 2 (sptFromList2 ([]: List Nat)), sptLookup 2 (sptFromList2 ([]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_0_99
example : (sptLookup 99 (sptFromList2 ([]: List Nat)), sptLookup 99 (sptFromList2 ([]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_0_900
example : (sptLookup 900 (sptFromList2 ([]: List Nat)), sptLookup 900 (sptFromList2 ([]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_1_0
example : (sptLookup 0 (sptFromList2 ([]: List Nat)), sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_0_1_1
example : (sptLookup 1 (sptFromList2 ([]: List Nat)), sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_1_2
example : (sptLookup 2 (sptFromList2 ([]: List Nat)), sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 1) := by decide +kernel

-- cl_prefix_Nat_0_1_16
example : (sptLookup 16 (sptFromList2 ([]: List Nat)), sptLookup 16 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_1_99
example : (sptLookup 99 (sptFromList2 ([]: List Nat)), sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_1_900
example : (sptLookup 900 (sptFromList2 ([]: List Nat)), sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_2_0
example : (sptLookup 0 (sptFromList2 ([]: List Nat)), sptLookup 0 (sptFromList2 ([0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_0_2_1
example : (sptLookup 1 (sptFromList2 ([]: List Nat)), sptLookup 1 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_2_2
example : (sptLookup 2 (sptFromList2 ([]: List Nat)), sptLookup 2 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_2_4
example : (sptLookup 4 (sptFromList2 ([]: List Nat)), sptLookup 4 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_2_99
example : (sptLookup 99 (sptFromList2 ([]: List Nat)), sptLookup 99 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_0_2_900
example : (sptLookup 900 (sptFromList2 ([]: List Nat)), sptLookup 900 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_0
example : (sptLookup 0 (sptFromList2 ([0]: List Nat)), sptLookup 0 (sptFromList2 ([0]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_1_0_1
example : (sptLookup 1 (sptFromList2 ([0]: List Nat)), sptLookup 1 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_2
example : (sptLookup 2 (sptFromList2 ([0]: List Nat)), sptLookup 2 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_3
example : (sptLookup 3 (sptFromList2 ([0]: List Nat)), sptLookup 3 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_4
example : (sptLookup 4 (sptFromList2 ([0]: List Nat)), sptLookup 4 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_99
example : (sptLookup 99 (sptFromList2 ([0]: List Nat)), sptLookup 99 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_0_900
example : (sptLookup 900 (sptFromList2 ([0]: List Nat)), sptLookup 900 (sptFromList2 ([0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_1_0
example : (sptLookup 0 (sptFromList2 ([0]: List Nat)), sptLookup 0 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_1_1_1
example : (sptLookup 1 (sptFromList2 ([0]: List Nat)), sptLookup 1 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_1_2
example : (sptLookup 2 (sptFromList2 ([0]: List Nat)), sptLookup 2 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_1_1_3
example : (sptLookup 3 (sptFromList2 ([0]: List Nat)), sptLookup 3 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_1_18
example : (sptLookup 18 (sptFromList2 ([0]: List Nat)), sptLookup 18 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_1_99
example : (sptLookup 99 (sptFromList2 ([0]: List Nat)), sptLookup 99 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_1_900
example : (sptLookup 900 (sptFromList2 ([0]: List Nat)), sptLookup 900 (sptFromList2 ([0, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_2_0
example : (sptLookup 0 (sptFromList2 ([0]: List Nat)), sptLookup 0 (sptFromList2 ([0, 0]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_1_2_1
example : (sptLookup 1 (sptFromList2 ([0]: List Nat)), sptLookup 1 (sptFromList2 ([0, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_2_2
example : (sptLookup 2 (sptFromList2 ([0]: List Nat)), sptLookup 2 (sptFromList2 ([0, 0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_1_2_3
example : (sptLookup 3 (sptFromList2 ([0]: List Nat)), sptLookup 3 (sptFromList2 ([0, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_2_6
example : (sptLookup 6 (sptFromList2 ([0]: List Nat)), sptLookup 6 (sptFromList2 ([0, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_2_99
example : (sptLookup 99 (sptFromList2 ([0]: List Nat)), sptLookup 99 (sptFromList2 ([0, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_1_2_900
example : (sptLookup 900 (sptFromList2 ([0]: List Nat)), sptLookup 900 (sptFromList2 ([0, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_0
example : (sptLookup 0 (sptFromList2 ([9]: List Nat)), sptLookup 0 (sptFromList2 ([9]: List Nat))) = (some 9, some 9) := by decide +kernel

-- cl_prefix_Nat_2_0_1
example : (sptLookup 1 (sptFromList2 ([9]: List Nat)), sptLookup 1 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_2
example : (sptLookup 2 (sptFromList2 ([9]: List Nat)), sptLookup 2 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_3
example : (sptLookup 3 (sptFromList2 ([9]: List Nat)), sptLookup 3 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_4
example : (sptLookup 4 (sptFromList2 ([9]: List Nat)), sptLookup 4 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_99
example : (sptLookup 99 (sptFromList2 ([9]: List Nat)), sptLookup 99 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_0_900
example : (sptLookup 900 (sptFromList2 ([9]: List Nat)), sptLookup 900 (sptFromList2 ([9]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_1_0
example : (sptLookup 0 (sptFromList2 ([9]: List Nat)), sptLookup 0 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 9, some 9) := by decide +kernel

-- cl_prefix_Nat_2_1_1
example : (sptLookup 1 (sptFromList2 ([9]: List Nat)), sptLookup 1 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_1_2
example : (sptLookup 2 (sptFromList2 ([9]: List Nat)), sptLookup 2 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_2_1_3
example : (sptLookup 3 (sptFromList2 ([9]: List Nat)), sptLookup 3 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_1_18
example : (sptLookup 18 (sptFromList2 ([9]: List Nat)), sptLookup 18 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_1_99
example : (sptLookup 99 (sptFromList2 ([9]: List Nat)), sptLookup 99 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_1_900
example : (sptLookup 900 (sptFromList2 ([9]: List Nat)), sptLookup 900 (sptFromList2 ([9, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_2_0
example : (sptLookup 0 (sptFromList2 ([9]: List Nat)), sptLookup 0 (sptFromList2 ([9, 0]: List Nat))) = (some 9, some 9) := by decide +kernel

-- cl_prefix_Nat_2_2_1
example : (sptLookup 1 (sptFromList2 ([9]: List Nat)), sptLookup 1 (sptFromList2 ([9, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_2_2
example : (sptLookup 2 (sptFromList2 ([9]: List Nat)), sptLookup 2 (sptFromList2 ([9, 0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_2_2_3
example : (sptLookup 3 (sptFromList2 ([9]: List Nat)), sptLookup 3 (sptFromList2 ([9, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_2_6
example : (sptLookup 6 (sptFromList2 ([9]: List Nat)), sptLookup 6 (sptFromList2 ([9, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_2_99
example : (sptLookup 99 (sptFromList2 ([9]: List Nat)), sptLookup 99 (sptFromList2 ([9, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_2_2_900
example : (sptLookup 900 (sptFromList2 ([9]: List Nat)), sptLookup 900 (sptFromList2 ([9, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_0
example : (sptLookup 0 (sptFromList2 ([2, 2]: List Nat)), sptLookup 0 (sptFromList2 ([2, 2]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_0_1
example : (sptLookup 1 (sptFromList2 ([2, 2]: List Nat)), sptLookup 1 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_2
example : (sptLookup 2 (sptFromList2 ([2, 2]: List Nat)), sptLookup 2 (sptFromList2 ([2, 2]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_0_4
example : (sptLookup 4 (sptFromList2 ([2, 2]: List Nat)), sptLookup 4 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_5
example : (sptLookup 5 (sptFromList2 ([2, 2]: List Nat)), sptLookup 5 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_6
example : (sptLookup 6 (sptFromList2 ([2, 2]: List Nat)), sptLookup 6 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_99
example : (sptLookup 99 (sptFromList2 ([2, 2]: List Nat)), sptLookup 99 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_0_900
example : (sptLookup 900 (sptFromList2 ([2, 2]: List Nat)), sptLookup 900 (sptFromList2 ([2, 2]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_1_0
example : (sptLookup 0 (sptFromList2 ([2, 2]: List Nat)), sptLookup 0 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_1_1
example : (sptLookup 1 (sptFromList2 ([2, 2]: List Nat)), sptLookup 1 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_1_2
example : (sptLookup 2 (sptFromList2 ([2, 2]: List Nat)), sptLookup 2 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_1_4
example : (sptLookup 4 (sptFromList2 ([2, 2]: List Nat)), sptLookup 4 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_3_1_5
example : (sptLookup 5 (sptFromList2 ([2, 2]: List Nat)), sptLookup 5 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_1_20
example : (sptLookup 20 (sptFromList2 ([2, 2]: List Nat)), sptLookup 20 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_1_99
example : (sptLookup 99 (sptFromList2 ([2, 2]: List Nat)), sptLookup 99 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_1_900
example : (sptLookup 900 (sptFromList2 ([2, 2]: List Nat)), sptLookup 900 (sptFromList2 ([2, 2, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_2_0
example : (sptLookup 0 (sptFromList2 ([2, 2]: List Nat)), sptLookup 0 (sptFromList2 ([2, 2, 0]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_2_1
example : (sptLookup 1 (sptFromList2 ([2, 2]: List Nat)), sptLookup 1 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_2_2
example : (sptLookup 2 (sptFromList2 ([2, 2]: List Nat)), sptLookup 2 (sptFromList2 ([2, 2, 0]: List Nat))) = (some 2, some 2) := by decide +kernel

-- cl_prefix_Nat_3_2_4
example : (sptLookup 4 (sptFromList2 ([2, 2]: List Nat)), sptLookup 4 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_3_2_5
example : (sptLookup 5 (sptFromList2 ([2, 2]: List Nat)), sptLookup 5 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_2_8
example : (sptLookup 8 (sptFromList2 ([2, 2]: List Nat)), sptLookup 8 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_2_99
example : (sptLookup 99 (sptFromList2 ([2, 2]: List Nat)), sptLookup 99 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_3_2_900
example : (sptLookup 900 (sptFromList2 ([2, 2]: List Nat)), sptLookup 900 (sptFromList2 ([2, 2, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_0
example : (sptLookup 0 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 0 (sptFromList2 ([8, 7, 6]: List Nat))) = (some 8, some 8) := by decide +kernel

-- cl_prefix_Nat_4_0_1
example : (sptLookup 1 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 1 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_2
example : (sptLookup 2 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 2 (sptFromList2 ([8, 7, 6]: List Nat))) = (some 7, some 7) := by decide +kernel

-- cl_prefix_Nat_4_0_6
example : (sptLookup 6 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 6 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_7
example : (sptLookup 7 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 7 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_8
example : (sptLookup 8 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 8 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_99
example : (sptLookup 99 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 99 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_0_900
example : (sptLookup 900 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 900 (sptFromList2 ([8, 7, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_1_0
example : (sptLookup 0 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 0 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 8, some 8) := by decide +kernel

-- cl_prefix_Nat_4_1_1
example : (sptLookup 1 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 1 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_1_2
example : (sptLookup 2 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 2 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 7, some 7) := by decide +kernel

-- cl_prefix_Nat_4_1_6
example : (sptLookup 6 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 6 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_4_1_7
example : (sptLookup 7 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 7 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_1_22
example : (sptLookup 22 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 22 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_1_99
example : (sptLookup 99 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 99 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_1_900
example : (sptLookup 900 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 900 (sptFromList2 ([8, 7, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_2_0
example : (sptLookup 0 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 0 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (some 8, some 8) := by decide +kernel

-- cl_prefix_Nat_4_2_1
example : (sptLookup 1 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 1 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_2_2
example : (sptLookup 2 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 2 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (some 7, some 7) := by decide +kernel

-- cl_prefix_Nat_4_2_6
example : (sptLookup 6 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 6 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_4_2_7
example : (sptLookup 7 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 7 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_2_10
example : (sptLookup 10 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 10 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_2_99
example : (sptLookup 99 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 99 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_4_2_900
example : (sptLookup 900 (sptFromList2 ([8, 7, 6]: List Nat)), sptLookup 900 (sptFromList2 ([8, 7, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_0
example : (sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_5_0_1
example : (sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_2
example : (sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 1, some 1) := by decide +kernel

-- cl_prefix_Nat_5_0_14
example : (sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_15
example : (sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_16
example : (sptLookup 16 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 16 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_99
example : (sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_0_900
example : (sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_1_0
example : (sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_5_1_1
example : (sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_1_2
example : (sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (some 1, some 1) := by decide +kernel

-- cl_prefix_Nat_5_1_14
example : (sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_5_1_15
example : (sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_1_30
example : (sptLookup 30 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 30 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_1_99
example : (sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_1_900
example : (sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_2_0
example : (sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 0 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (some 0, some 0) := by decide +kernel

-- cl_prefix_Nat_5_2_1
example : (sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 1 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_2_2
example : (sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 2 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (some 1, some 1) := by decide +kernel

-- cl_prefix_Nat_5_2_14
example : (sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 14 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, some 0) := by decide +kernel

-- cl_prefix_Nat_5_2_15
example : (sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 15 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_2_18
example : (sptLookup 18 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 18 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_2_99
example : (sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 99 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Nat_5_2_900
example : (sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6]: List Nat)), sptLookup 900 (sptFromList2 ([0, 1, 2, 3, 4, 5, 6, 0]: List Nat))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_0_0
example : (sptLookup 0 (sptFromList2 ([]: List Bool)), sptLookup 0 (sptFromList2 ([]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_0_1
example : (sptLookup 1 (sptFromList2 ([]: List Bool)), sptLookup 1 (sptFromList2 ([]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_0_2
example : (sptLookup 2 (sptFromList2 ([]: List Bool)), sptLookup 2 (sptFromList2 ([]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_0_99
example : (sptLookup 99 (sptFromList2 ([]: List Bool)), sptLookup 99 (sptFromList2 ([]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_0_900
example : (sptLookup 900 (sptFromList2 ([]: List Bool)), sptLookup 900 (sptFromList2 ([]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_1_0
example : (sptLookup 0 (sptFromList2 ([]: List Bool)), sptLookup 0 (sptFromList2 ([false, true, false]: List Bool))) = (none, some false) := by decide +kernel

-- cl_prefix_Bool_0_1_1
example : (sptLookup 1 (sptFromList2 ([]: List Bool)), sptLookup 1 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_1_2
example : (sptLookup 2 (sptFromList2 ([]: List Bool)), sptLookup 2 (sptFromList2 ([false, true, false]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_0_1_8
example : (sptLookup 8 (sptFromList2 ([]: List Bool)), sptLookup 8 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_1_99
example : (sptLookup 99 (sptFromList2 ([]: List Bool)), sptLookup 99 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_1_900
example : (sptLookup 900 (sptFromList2 ([]: List Bool)), sptLookup 900 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_2_0
example : (sptLookup 0 (sptFromList2 ([]: List Bool)), sptLookup 0 (sptFromList2 ([true]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_0_2_1
example : (sptLookup 1 (sptFromList2 ([]: List Bool)), sptLookup 1 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_2_2
example : (sptLookup 2 (sptFromList2 ([]: List Bool)), sptLookup 2 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_2_4
example : (sptLookup 4 (sptFromList2 ([]: List Bool)), sptLookup 4 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_2_99
example : (sptLookup 99 (sptFromList2 ([]: List Bool)), sptLookup 99 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_0_2_900
example : (sptLookup 900 (sptFromList2 ([]: List Bool)), sptLookup 900 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_0
example : (sptLookup 0 (sptFromList2 ([true]: List Bool)), sptLookup 0 (sptFromList2 ([true]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_1_0_1
example : (sptLookup 1 (sptFromList2 ([true]: List Bool)), sptLookup 1 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_2
example : (sptLookup 2 (sptFromList2 ([true]: List Bool)), sptLookup 2 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_3
example : (sptLookup 3 (sptFromList2 ([true]: List Bool)), sptLookup 3 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_4
example : (sptLookup 4 (sptFromList2 ([true]: List Bool)), sptLookup 4 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_99
example : (sptLookup 99 (sptFromList2 ([true]: List Bool)), sptLookup 99 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_0_900
example : (sptLookup 900 (sptFromList2 ([true]: List Bool)), sptLookup 900 (sptFromList2 ([true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_1_0
example : (sptLookup 0 (sptFromList2 ([true]: List Bool)), sptLookup 0 (sptFromList2 ([true, false, true, false]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_1_1_1
example : (sptLookup 1 (sptFromList2 ([true]: List Bool)), sptLookup 1 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_1_2
example : (sptLookup 2 (sptFromList2 ([true]: List Bool)), sptLookup 2 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, some false) := by decide +kernel

-- cl_prefix_Bool_1_1_3
example : (sptLookup 3 (sptFromList2 ([true]: List Bool)), sptLookup 3 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_1_10
example : (sptLookup 10 (sptFromList2 ([true]: List Bool)), sptLookup 10 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_1_99
example : (sptLookup 99 (sptFromList2 ([true]: List Bool)), sptLookup 99 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_1_900
example : (sptLookup 900 (sptFromList2 ([true]: List Bool)), sptLookup 900 (sptFromList2 ([true, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_2_0
example : (sptLookup 0 (sptFromList2 ([true]: List Bool)), sptLookup 0 (sptFromList2 ([true, true]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_1_2_1
example : (sptLookup 1 (sptFromList2 ([true]: List Bool)), sptLookup 1 (sptFromList2 ([true, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_2_2
example : (sptLookup 2 (sptFromList2 ([true]: List Bool)), sptLookup 2 (sptFromList2 ([true, true]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_1_2_3
example : (sptLookup 3 (sptFromList2 ([true]: List Bool)), sptLookup 3 (sptFromList2 ([true, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_2_6
example : (sptLookup 6 (sptFromList2 ([true]: List Bool)), sptLookup 6 (sptFromList2 ([true, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_2_99
example : (sptLookup 99 (sptFromList2 ([true]: List Bool)), sptLookup 99 (sptFromList2 ([true, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_1_2_900
example : (sptLookup 900 (sptFromList2 ([true]: List Bool)), sptLookup 900 (sptFromList2 ([true, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_0
example : (sptLookup 0 (sptFromList2 ([false]: List Bool)), sptLookup 0 (sptFromList2 ([false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_2_0_1
example : (sptLookup 1 (sptFromList2 ([false]: List Bool)), sptLookup 1 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_2
example : (sptLookup 2 (sptFromList2 ([false]: List Bool)), sptLookup 2 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_3
example : (sptLookup 3 (sptFromList2 ([false]: List Bool)), sptLookup 3 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_4
example : (sptLookup 4 (sptFromList2 ([false]: List Bool)), sptLookup 4 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_99
example : (sptLookup 99 (sptFromList2 ([false]: List Bool)), sptLookup 99 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_0_900
example : (sptLookup 900 (sptFromList2 ([false]: List Bool)), sptLookup 900 (sptFromList2 ([false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_1_0
example : (sptLookup 0 (sptFromList2 ([false]: List Bool)), sptLookup 0 (sptFromList2 ([false, false, true, false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_2_1_1
example : (sptLookup 1 (sptFromList2 ([false]: List Bool)), sptLookup 1 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_1_2
example : (sptLookup 2 (sptFromList2 ([false]: List Bool)), sptLookup 2 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, some false) := by decide +kernel

-- cl_prefix_Bool_2_1_3
example : (sptLookup 3 (sptFromList2 ([false]: List Bool)), sptLookup 3 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_1_10
example : (sptLookup 10 (sptFromList2 ([false]: List Bool)), sptLookup 10 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_1_99
example : (sptLookup 99 (sptFromList2 ([false]: List Bool)), sptLookup 99 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_1_900
example : (sptLookup 900 (sptFromList2 ([false]: List Bool)), sptLookup 900 (sptFromList2 ([false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_2_0
example : (sptLookup 0 (sptFromList2 ([false]: List Bool)), sptLookup 0 (sptFromList2 ([false, true]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_2_2_1
example : (sptLookup 1 (sptFromList2 ([false]: List Bool)), sptLookup 1 (sptFromList2 ([false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_2_2
example : (sptLookup 2 (sptFromList2 ([false]: List Bool)), sptLookup 2 (sptFromList2 ([false, true]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_2_2_3
example : (sptLookup 3 (sptFromList2 ([false]: List Bool)), sptLookup 3 (sptFromList2 ([false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_2_6
example : (sptLookup 6 (sptFromList2 ([false]: List Bool)), sptLookup 6 (sptFromList2 ([false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_2_99
example : (sptLookup 99 (sptFromList2 ([false]: List Bool)), sptLookup 99 (sptFromList2 ([false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_2_2_900
example : (sptLookup 900 (sptFromList2 ([false]: List Bool)), sptLookup 900 (sptFromList2 ([false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_0
example : (sptLookup 0 (sptFromList2 ([true, false]: List Bool)), sptLookup 0 (sptFromList2 ([true, false]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_3_0_1
example : (sptLookup 1 (sptFromList2 ([true, false]: List Bool)), sptLookup 1 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_2
example : (sptLookup 2 (sptFromList2 ([true, false]: List Bool)), sptLookup 2 (sptFromList2 ([true, false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_3_0_4
example : (sptLookup 4 (sptFromList2 ([true, false]: List Bool)), sptLookup 4 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_5
example : (sptLookup 5 (sptFromList2 ([true, false]: List Bool)), sptLookup 5 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_6
example : (sptLookup 6 (sptFromList2 ([true, false]: List Bool)), sptLookup 6 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_99
example : (sptLookup 99 (sptFromList2 ([true, false]: List Bool)), sptLookup 99 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_0_900
example : (sptLookup 900 (sptFromList2 ([true, false]: List Bool)), sptLookup 900 (sptFromList2 ([true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_1_0
example : (sptLookup 0 (sptFromList2 ([true, false]: List Bool)), sptLookup 0 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_3_1_1
example : (sptLookup 1 (sptFromList2 ([true, false]: List Bool)), sptLookup 1 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_1_2
example : (sptLookup 2 (sptFromList2 ([true, false]: List Bool)), sptLookup 2 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_3_1_4
example : (sptLookup 4 (sptFromList2 ([true, false]: List Bool)), sptLookup 4 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, some false) := by decide +kernel

-- cl_prefix_Bool_3_1_5
example : (sptLookup 5 (sptFromList2 ([true, false]: List Bool)), sptLookup 5 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_1_12
example : (sptLookup 12 (sptFromList2 ([true, false]: List Bool)), sptLookup 12 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_1_99
example : (sptLookup 99 (sptFromList2 ([true, false]: List Bool)), sptLookup 99 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_1_900
example : (sptLookup 900 (sptFromList2 ([true, false]: List Bool)), sptLookup 900 (sptFromList2 ([true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_2_0
example : (sptLookup 0 (sptFromList2 ([true, false]: List Bool)), sptLookup 0 (sptFromList2 ([true, false, true]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_3_2_1
example : (sptLookup 1 (sptFromList2 ([true, false]: List Bool)), sptLookup 1 (sptFromList2 ([true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_2_2
example : (sptLookup 2 (sptFromList2 ([true, false]: List Bool)), sptLookup 2 (sptFromList2 ([true, false, true]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_3_2_4
example : (sptLookup 4 (sptFromList2 ([true, false]: List Bool)), sptLookup 4 (sptFromList2 ([true, false, true]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_3_2_5
example : (sptLookup 5 (sptFromList2 ([true, false]: List Bool)), sptLookup 5 (sptFromList2 ([true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_2_8
example : (sptLookup 8 (sptFromList2 ([true, false]: List Bool)), sptLookup 8 (sptFromList2 ([true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_2_99
example : (sptLookup 99 (sptFromList2 ([true, false]: List Bool)), sptLookup 99 (sptFromList2 ([true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_3_2_900
example : (sptLookup 900 (sptFromList2 ([true, false]: List Bool)), sptLookup 900 (sptFromList2 ([true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_0
example : (sptLookup 0 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 0 (sptFromList2 ([false, true, false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_4_0_1
example : (sptLookup 1 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 1 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_2
example : (sptLookup 2 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 2 (sptFromList2 ([false, true, false]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_4_0_6
example : (sptLookup 6 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 6 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_7
example : (sptLookup 7 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 7 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_8
example : (sptLookup 8 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 8 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_99
example : (sptLookup 99 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 99 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_0_900
example : (sptLookup 900 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 900 (sptFromList2 ([false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_1_0
example : (sptLookup 0 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 0 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_4_1_1
example : (sptLookup 1 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 1 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_1_2
example : (sptLookup 2 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 2 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_4_1_6
example : (sptLookup 6 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 6 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, some false) := by decide +kernel

-- cl_prefix_Bool_4_1_7
example : (sptLookup 7 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 7 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_1_14
example : (sptLookup 14 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 14 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_1_99
example : (sptLookup 99 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 99 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_1_900
example : (sptLookup 900 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 900 (sptFromList2 ([false, true, false, false, true, false]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_2_0
example : (sptLookup 0 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 0 (sptFromList2 ([false, true, false, true]: List Bool))) = (some false, some false) := by decide +kernel

-- cl_prefix_Bool_4_2_1
example : (sptLookup 1 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 1 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_2_2
example : (sptLookup 2 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 2 (sptFromList2 ([false, true, false, true]: List Bool))) = (some true, some true) := by decide +kernel

-- cl_prefix_Bool_4_2_6
example : (sptLookup 6 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 6 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, some true) := by decide +kernel

-- cl_prefix_Bool_4_2_7
example : (sptLookup 7 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 7 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_2_10
example : (sptLookup 10 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 10 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_2_99
example : (sptLookup 99 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 99 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, none) := by decide +kernel

-- cl_prefix_Bool_4_2_900
example : (sptLookup 900 (sptFromList2 ([false, true, false]: List Bool)), sptLookup 900 (sptFromList2 ([false, true, false, true]: List Bool))) = (none, none) := by decide +kernel
