import Zkc.Realization.InstructionSequence

set_option autoImplicit false

namespace Zkc.Realization.InstructionSequence
-- A generic list-append law with the necessary no-incomplete-halt premise.
def resume {S E : Type} (f : S → Terminal S E) (out : Terminal S E) : Terminal S E :=
 if out.outcome = .incomplete then
   let next := f out.state
   ⟨next.outcome,next.state,out.events ++ next.events⟩
 else out

theorem run_append {Op S E : Type} (step : Op → S → Step S E)
 (noFalloffHalt : ∀ op s es t, step op s ≠ .halt .incomplete t es)
 (xs ys : List Op) (s : S) :
 run step (xs ++ ys) s = resume (run step ys) (run step xs s) := by
 induction xs generalizing s with
 | nil => simp [run,resume]
 | cons x xs ih =>
   simp only [List.cons_append,run]
   cases h : step x s with
   | halt why t es =>
     have hn : why ≠ .incomplete := by
       intro he; subst why; exact noFalloffHalt x s es t h
     simp [resume,hn]
   | next t es =>
     dsimp only
     rw [ih]
     by_cases hc : (run step xs t).outcome = .incomplete <;>
       simp [resume,hc,List.append_assoc]

/-- Run successive blocks by resuming `.incomplete` outcomes. This represents
ordinary list falloff only when primitives cannot halt with `.incomplete`;
`flatten_run_blocks` requires precisely that restriction. -/
def runBlocks {Op S E : Type} (step : Op → S → Step S E) :
    List (List Op) → S → Terminal S E
  | [], s => ⟨.incomplete,s,[]⟩
  | block :: rest, s => resume (runBlocks step rest) (run step block s)

theorem flatten_run_blocks {Op S E : Type} (step : Op → S → Step S E)
    (noFalloffHalt : ∀ op s es t, step op s ≠ .halt .incomplete t es)
    (blocks : List (List Op)) (s : S) :
    run step blocks.flatten s = runBlocks step blocks s := by
  induction blocks generalizing s with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.flatten_cons, runBlocks]
    rw [run_append step noFalloffHalt]
    rw [show run step rest.flatten = runBlocks step rest from funext ih]

end Zkc.Realization.InstructionSequence
