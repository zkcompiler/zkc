import ZkcExamples.Construction.SumcheckProof

/-! Controls for the composed per-compile check on the actual compiled Sumcheck
validator, whose original has a protocol application and a repeat. Each
mutation in the first group keeps the transcript wiring, so the
transcript-construction rule alone accepts it; the participant projection rule
refuses it for the named obligation. The second group exercises the
transcript-construction rule's deployment checks inside the loop. -/

namespace Tests.SumcheckProjectionControls
open Zkc.Construction ZkcExamples.Construction

abbrev original := ZkcExamples.Structured.SumcheckSourceData.snapshot
abbrev program := SumcheckProof.program
abbrev imported := SumcheckProof.imported
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
  changeAt participant 2 fun loop => { loop with body := editList loop.body index edit }

/-- Accepted by the construction rule and refused by the composed check with
`code`. -/
def RefusedByProjection (participant : Participant) (code : String) : Prop :=
  checkExport original participant = .ok () ∧ checkCompiled imported participant = .error code

instance (participant : Participant) (code : String) : Decidable (RefusedByProjection participant code) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! The first two instructions construct and open Pending at slots 4--7.
The loop at instruction 2 captures eight values, carries point/claim/transcript,
and yields [29,34,28]. The suffix consumes [8,9] through atPrefix; the terminal
check at instruction 4 then reads [0,11,12]. -/

/-- The round check is dropped. -/
theorem roundCheckDropped_refused :
    RefusedByProjection (changeAt actual 2 fun loop => { loop with body := loop.body.eraseIdx 10 })
      "projection-guard" := by
  decide +kernel

/-- The round check compares the sum with the claim: equal in algebra, but not the
original comparison, so the guard's condition is not held. -/
theorem roundCheckSwapped_refused :
    RefusedByProjection (changeBody actual 9 fun instruction => { instruction with operands := [20, 10] })
      "projection-guard-operand" := by
  decide +kernel

/-- The updated claim adds the low term twice. -/
theorem claimUpdateMutated_refused :
    RefusedByProjection (changeBody actual 22 fun instruction => { instruction with operands := [32, 32] })
      "projection-unexplained" := by
  decide +kernel

/-- The challenge term scales the low message instead of the high one. -/
theorem challengeTermMutated_refused :
    RefusedByProjection (changeBody actual 21 fun instruction => { instruction with operands := [24, 12] })
      "projection-unexplained" := by
  decide +kernel

/-- The loop yields the claim it started the iteration with. -/
theorem staleClaimYielded_refused :
    RefusedByProjection (changeAt actual 2 fun loop =>
        { loop with operation := .loop "apply_18_label_726564756365_s18" 2 [29, 10, 28] })
      "projection-repeat-yield" := by
  decide +kernel

/-- The loop admits three rounds where the source repeat admits two. -/
theorem loopBoundChanged_refused :
    RefusedByProjection (changeAt actual 2 fun loop =>
        { loop with operation := .loop "apply_18_label_726564756365_s18" 3 [29, 34, 28] })
      "projection-repeat" := by
  decide +kernel

/-- The loop names the repeat site without its application path. -/
theorem loopSiteUnqualified_refused :
    RefusedByProjection (changeAt actual 2 fun loop => { loop with operation := .loop "s18" 2 [29, 34, 28] })
      "projection-repeat" := by
  decide +kernel

/-- The loop starts from the table values instead of the empty point. -/
theorem loopStartsFromTable_refused :
    RefusedByProjection (changeAt actual 2 fun loop => { loop with operands := [2, 0, 7, 3] })
      "projection-repeat" := by
  decide +kernel

/-- The terminal check reads the final claim and point in the other order. -/
theorem terminalOperandsSwapped_refused :
    RefusedByProjection (changeAt actual 4 fun call => { call with operands := [0, 12, 11] }) "projection-call" := by
  decide +kernel

/-! Deployment checks of the transcript-construction rule inside the loop, which
`check_sound` does not use. -/

/-- Refused by the transcript-construction rule alone with `code`. -/
def RefusedByConstruction (participant : Participant) (code : String) : Prop :=
  checkExport original participant = .error code

instance (participant : Participant) (code : String) : Decidable (RefusedByConstruction participant code) :=
  inferInstanceAs (Decidable (_ = _))

/-- The first round observation reads coordinates built without the induction
index; the observation's coordinate condition fails. -/
theorem coordinatesWithoutIndex_refused :
    RefusedByConstruction (changeBody actual 3 fun instruction => { instruction with operands := [11, 12, 13] })
      "construction-observe" := by
  decide +kernel

/-- The first coordinate vector appends the carried point instead of the
induction index. -/
theorem coordinatesFromPoint_refused :
    RefusedByConstruction (changeBody actual 2 fun instruction => { instruction with operands := [13, 9] })
      "construction-coordinates" := by
  decide +kernel

/-- Drop the repeat step from an observation's template. -/
def withoutRepeatStep : Operation → Operation
  | .observe suite template => .observe suite { template with steps := template.steps.take 1 }
  | operation => operation

/-- The first round observation's template omits its repeat step, so it has no
coordinate for the enclosing loop. -/
theorem templateWithoutRepeat_refused :
    RefusedByConstruction (changeBody actual 3 fun instruction =>
        { instruction with operation := withoutRepeatStep instruction.operation })
      "construction-observe" := by
  decide +kernel

/-- The loop count reads the claim. -/
theorem loopCountFromClaim_refused :
    RefusedByConstruction (changeAt actual 2 fun loop => { loop with operands := [1, 6, 7, 3] })
      "construction-loop" := by
  decide +kernel

/-- The round check guards on the transcript. -/
theorem guardOnTranscript_refused :
    RefusedByConstruction (changeBody actual 10 fun instruction => { instruction with operands := [11] })
      "construction-guard" := by
  decide +kernel

/-- The terminal check reads the final transcript. -/
theorem callOnTranscript_refused :
    RefusedByConstruction (changeAt actual 4 fun call => { call with operands := [0, 11, 10] }) "construction-call" := by
  decide +kernel

/-- Premise satisfiability: the actual export is accepted. -/
theorem actual_accepted : checkCompiled imported actual = .ok () := by decide +kernel

end Tests.SumcheckProjectionControls
