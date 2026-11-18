module

public import Zkc.Core.World.Runs
public import Zkc.Core.Scheme.Deployed

@[expose] public section

/-!
How a run of the executor ends, the executor, and the prover's and verifier's runs.
-/

namespace Zkc.Core

/-! ## How a run of the executor ends -/

/-- What the executor reports of the run of one role: how it ended (a return has the results
and what the role's handlers give), that the budget of steps ran out, or a defect of the
harness of the run. -/
inductive Outcome (A G : Type) where
  | ended (ending : Ending (A × G) Stop)
  | limit
  | failed (defect : String)


/-! ## Running a deployed scheme -/

/-- An executor: one role of a deployed scheme in a world, to a limit of steps. It reports
how the run ended and what the role did. -/
abbrev Executor (V : Vocabulary) : Type 1 :=
  ∀ (d : Deployed V) (M : Model V) (r : Role), HList (RV M r) d.entry.ins →
    HList M.Val (Stack.Takes (d.stack r)) → Source M → Nat →
      Outcome (HList (RV M r) d.entry.outs) (HList M.Val (Stack.Gives (d.stack r))) ×
        List (Happened M)

section
variable {V : Vocabulary} (execute : Executor V)

/-- The prover's run of a deployed scheme: from its part of the inputs, to the proof, which
is what its handlers give. -/
def prove (d : Deployed V) (M : Model V) (prover : Role) (ins : HList (RV M prover) d.entry.ins)
    (first : Stack.Takes (d.stack prover) = []) (source : Source M) (limit : Nat) :
    Option (HList M.Val (Stack.Gives (d.stack prover))) :=
  match (execute d M prover ins (cast (congrArg (HList M.Val) first.symm) .nil) source
      limit).1 with
  | .ended (.returned (_, proof)) => some proof
  | _ => none

/-- The verifier's run: from its part of the inputs and a proof, which its handlers take, to
its results when it accepts. A reduction's results are its reduced statement. -/
def verify (d : Deployed V) (M : Model V) (verifier : Role)
    (ins : HList (RV M verifier) d.entry.ins) (proof : HList M.Val (Stack.Takes (d.stack verifier)))
    (source : Source M) (limit : Nat) : Option (HList (RV M verifier) d.entry.outs) :=
  match (execute d M verifier ins proof source limit).1 with
  | .ended (.returned (results, _)) => some results
  | _ => none

end

end Zkc.Core
