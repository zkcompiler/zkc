module

public import Zkc.Core.Transform.FunctionReporting

@[expose] public section

namespace Zkc.Core
variable {V : Vocabulary}

section
variable {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- Check a typed function under its stored header and report its loop bounds. -/
def TypedFn.check (f : TypedFn V fns hdr) : Except (List (ProgramRefusal V)) (List (Place × Nat)) :=
  BodyAnalysis.checkStored f

/-- Compare a typed candidate with a source under their common header. -/
def TypedFn.follows (source candidate : TypedFn V fns hdr) :
    Except (List (ProgramRefusal V) × List Place) (List (Place × Nat)) :=
  BodyAnalysis.compareStored source candidate

end

/-- Why a step is not accepted: its target does not elaborate (no place: it was not walked) or
is refused by the analysis while it follows, with the places where it differs, if any; or,
with no refusal, the places where it differs. -/
inductive StepRefusal (V : Vocabulary) where
  | target (refusals : List (ProgramRefusal V)) (differs : List Place)
  | differs (places : List Place)

end Zkc.Core
