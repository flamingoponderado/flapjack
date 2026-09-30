(* Original stackSem evaluate_def size/bitmap clauses. *)
load "bossLib"; load "preamble"; load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "size_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (7,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackSetSize 7,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "size_success" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (7,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackSetSize 7,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "size_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (7,Word 2w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackSetSize 7,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "size_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (7,Loc 3 4); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackSetSize 7,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "size_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY; clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackSetSize 7,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (8,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 7 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_success" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (8,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 7 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (8,Word 2w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 7 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (8,Loc 3 4); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 7 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY; clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 7 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;

val _ = observe "bitmap_alias" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; bitmaps := [13w;29w];
 stack_space := 5; regs := FEMPTY |+ (8,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (BitmapLoad 8 8,s) in
 (r,FLOOKUP s1.regs 7,FLOOKUP s1.regs 8,s1.stack,s1.stack_space,s1.clock,s1.memory 0w,s1.bitmaps)``;
