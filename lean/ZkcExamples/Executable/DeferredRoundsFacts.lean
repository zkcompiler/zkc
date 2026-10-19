module

public import ZkcExamples.Executable.DeferredRoundsProgramData
public import ZkcExamples.Construction.DeferredRounds
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Installed

@[expose] public section

/-! Generated facts of the executable validator `DeferredRoundsProgramData`.
Regenerate with `lean/bridges/subject.py --write`. The per-compile lowering
rule accepts the validator against the constructed validator (`accepted`);
each fact below is checked by the kernel. -/

namespace ZkcExamples.Executable.DeferredRoundsFacts
open Zkc.Construction Zkc.Executable

abbrev validator : Validator := ZkcExamples.Executable.DeferredRoundsProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed ZkcExamples.Construction.DeferredRounds.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed ZkcExamples.Construction.DeferredRounds.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- The helpers the constructed validator calls. -/
theorem helpers : Instruction.helpers ZkcExamples.Construction.DeferredRounds.participant.instructions = [] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

/-- The constructed validator has no helper call. -/
theorem calls : Instruction.callList ZkcExamples.Construction.DeferredRounds.participant.instructions = [] := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- A complete run charges 35 instructions. -/
theorem total : lowered.total? = some 35 := by decide +kernel

/-- The message types, in order. -/
abbrev receives : List PhysicalType :=
  [{ sort := Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"), representation := "arkworks.fr/0" }, { sort := Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"), representation := "arkworks.fr/0" }]

set_option maxRecDepth 20000 in
theorem plan_static : Plan.static lowered.plan = some receives := by decide +kernel

theorem plan_types {F G : Type} (data : List (Value F G)) : Plan.types data lowered.plan = receives :=
  Plan.types_static data plan_static

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted (x : F) : validator.admits (ZkcExamples.Construction.DeferredRounds.inputs (F := F) (G := G) x) = true := by
  rfl

end ZkcExamples.Executable.DeferredRoundsFacts
