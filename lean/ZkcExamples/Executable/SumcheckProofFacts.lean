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
theorem helpers : Instruction.helpers ZkcExamples.Construction.SumcheckProof.participant.instructions = ["zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted (valuesValue : List F) (claim : F) (rounds : Nat) : validator.admits (ZkcExamples.Construction.SumcheckProof.inputs (F := F) (G := G) valuesValue claim rounds) = true := by
  rfl

end ZkcExamples.Executable.SumcheckProof
