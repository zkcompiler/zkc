module

public import ZkcExamples.Executable.SumcheckProofProgramData
public import ZkcExamples.Construction.SumcheckProof
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Installed

@[expose] public section

/-! Generated facts of the executable validator `SumcheckProofProgramData`.
Regenerate with `lean/bridges/subject.py --write`. The per-compile lowering
rule accepts the validator against the constructed validator (`accepted`);
each fact below is checked by the kernel. -/

namespace ZkcExamples.Executable.SumcheckProof
open Zkc.Construction Zkc.Executable

abbrev validator : Validator := ZkcExamples.Executable.SumcheckProofProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed ZkcExamples.Construction.SumcheckProof.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed ZkcExamples.Construction.SumcheckProof.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- The helpers the constructed validator calls. -/
theorem helpers : Instruction.helpers ZkcExamples.Construction.SumcheckProof.participant.instructions = ["zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted (valuesValue : List F) (claim : F) (rounds : Nat) : validator.admits (ZkcExamples.Construction.SumcheckProof.inputs (F := F) (G := G) valuesValue claim rounds) = true := by
  rfl

end ZkcExamples.Executable.SumcheckProof
