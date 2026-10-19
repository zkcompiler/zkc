module

public import ZkcExamples.Executable.SchnorrProofProgramData
public import ZkcExamples.Construction.SchnorrProof
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Installed

@[expose] public section

/-! Generated facts of the executable validator `SchnorrProofProgramData`.
Regenerate with `lean/bridges/subject.py --write`. The per-compile lowering
rule accepts the validator against the constructed validator (`accepted`);
each fact below is checked by the kernel. -/

namespace ZkcExamples.Executable.SchnorrProof
open Zkc.Construction Zkc.Executable

abbrev validator : Validator := ZkcExamples.Executable.SchnorrProofProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed ZkcExamples.Construction.SchnorrProof.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed ZkcExamples.Construction.SchnorrProof.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- The helpers the constructed validator calls. -/
theorem helpers : Instruction.helpers ZkcExamples.Construction.SchnorrProof.participant.instructions = [] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

/-- The constructed validator has no helper call. -/
theorem calls : Instruction.callList ZkcExamples.Construction.SchnorrProof.participant.instructions = [] := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- A complete run charges 25 instructions. -/
theorem total : lowered.total? = some 25 := by decide +kernel

/-- The message types, in order. -/
abbrev receives : List PhysicalType :=
  [{ sort := Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.group "bls12-381.g1"), representation := "arkworks.g1/0" }, { sort := Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"), representation := "arkworks.fr/0" }]

set_option maxRecDepth 20000 in
theorem plan_static : Plan.static lowered.plan = some receives := by decide +kernel

theorem plan_types {F G : Type} (data : List (Value F G)) : Plan.types data lowered.plan = receives :=
  Plan.types_static data plan_static

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted (base point : G) : validator.admits ((ZkcExamples.Construction.SchnorrProof.inputs (F := F) (G := G) base point).map .data) = true := by
  rfl

end ZkcExamples.Executable.SchnorrProof
