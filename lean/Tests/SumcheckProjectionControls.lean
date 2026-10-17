import ZkcExamples.Construction.SumcheckProof

/-! Controls for the composed per-compile check on the actual compiled Sumcheck
validator, whose original has a protocol application and a repeat. Every
mutation below keeps the transcript wiring, so the transcript-construction rule
alone accepts it; the participant projection rule refuses it for the named
obligation. -/

namespace Tests.SumcheckProjectionControls
open Zkc.Construction ZkcExamples.Construction

abbrev original := ZkcExamples.Structured.SumcheckSourceData.snapshot
abbrev program := SumcheckProof.program
abbrev actual := SumcheckProof.participant

/-- Change one top-level instruction. -/
def changeAt (participant : Participant) (index : Nat) (edit : Instruction → Instruction) : Participant :=
  { participant with instructions := participant.instructions.mapIdx fun position instruction =>
      if position = index then edit instruction else instruction }

def editList (instructions : List Instruction) (index : Nat) (edit : Instruction → Instruction) :
    List Instruction :=
  instructions.mapIdx fun position instruction => if position = index then edit instruction else instruction

/-- Change one instruction of the round loop's body. -/
def changeBody (participant : Participant) (index : Nat) (edit : Instruction → Instruction) : Participant :=
  changeAt participant 1 fun loop => { loop with body := editList loop.body index edit }

/-- Accepted by the construction rule and refused by the composed check with
`code`. -/
def RefusedByProjection (participant : Participant) (code : String) : Prop :=
  checkExport original participant = .ok () ∧ checkCompiled original program participant = .error code

instance (participant : Participant) (code : String) : Decidable (RefusedByProjection participant code) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! Exported positions: inputs `0` table values, `1` claim, `2` round count;
`4` is the initial point; the loop (instruction `1`) carries the point `6`, the
claim `7` and the transcript, receives the round messages `9` and `13`,
compares the claim with their sum `17` (`18`), guards on it (body instruction
`10`), draws the challenge `21`, appends it to the point (`26`) and updates the
claim (`27` … `31`). After the loop `5` is the point and `6` the claim; the
terminal check (instruction `2`) reads `0`, `5` and `6`. -/

/-- The round check is dropped. -/
theorem roundCheckDropped_refused :
    RefusedByProjection (changeAt actual 1 fun loop => { loop with body := loop.body.eraseIdx 10 })
      "projection-guard" := by
  decide +kernel

/-- The round check compares the sum with the claim: equal in algebra, but not the
original comparison, so the guard's condition is not held. -/
theorem roundCheckSwapped_refused :
    RefusedByProjection (changeBody actual 9 fun instruction => { instruction with operands := [17, 7] })
      "projection-guard-operand" := by
  decide +kernel

/-- The updated claim adds the low term twice. -/
theorem claimUpdateMutated_refused :
    RefusedByProjection (changeBody actual 22 fun instruction => { instruction with operands := [29, 29] })
      "projection-unexplained" := by
  decide +kernel

/-- The challenge term scales the low message instead of the high one. -/
theorem challengeTermMutated_refused :
    RefusedByProjection (changeBody actual 21 fun instruction => { instruction with operands := [21, 9] })
      "projection-unexplained" := by
  decide +kernel

/-- The loop yields the claim it started the iteration with. -/
theorem staleClaimYielded_refused :
    RefusedByProjection (changeAt actual 1 fun loop =>
        { loop with operation := .loop "apply_18_label_726564756365_s15" 2 [26, 7, 25] })
      "projection-repeat-yield" := by
  decide +kernel

/-- The loop admits three rounds where the source repeat admits two. -/
theorem loopBoundChanged_refused :
    RefusedByProjection (changeAt actual 1 fun loop =>
        { loop with operation := .loop "apply_18_label_726564756365_s15" 3 [26, 31, 25] })
      "projection-repeat" := by
  decide +kernel

/-- The loop names the repeat site without its application path. -/
theorem loopSiteUnqualified_refused :
    RefusedByProjection (changeAt actual 1 fun loop => { loop with operation := .loop "s15" 2 [26, 31, 25] })
      "projection-repeat" := by
  decide +kernel

/-- The loop starts from the table values instead of the empty point. -/
theorem loopStartsFromTable_refused :
    RefusedByProjection (changeAt actual 1 fun loop => { loop with operands := [2, 0, 1, 3] })
      "projection-repeat" := by
  decide +kernel

/-- The terminal check reads the final claim and point in the other order. -/
theorem terminalOperandsSwapped_refused :
    RefusedByProjection (changeAt actual 2 fun call => { call with operands := [0, 6, 5] }) "projection-call" := by
  decide +kernel

/-- Premise satisfiability: the actual export is accepted. -/
theorem actual_accepted : checkCompiled original program actual = .ok () := SumcheckProof.compiled

end Tests.SumcheckProjectionControls
