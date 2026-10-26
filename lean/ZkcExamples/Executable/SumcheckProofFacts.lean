module

public import ZkcExamples.Executable.SumcheckProofProgramData
public import ZkcExamples.Construction.SumcheckArtifact
public import Zkc.Executable.Reading
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
theorem helpers : Instruction.helpers ZkcExamples.Construction.SumcheckProof.participant.instructions = ["zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted (valuesValue : List F) (claim : F) (rounds : Nat) : validator.admits (ZkcExamples.Construction.SumcheckProof.inputs (F := F) (G := G) valuesValue claim rounds) = true := by
  rfl

end ZkcExamples.Executable.SumcheckProof
