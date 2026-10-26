module

public import Zkc.Executable.HelperCosts
public import Zkc.Executable.DomainFitsRules
public import Zkc.Executable.DomainSuccess
public import ZkcExamples.Executable.SumcheckProofFacts
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Executable.SumcheckShape
public import ZkcExamples.Construction.SumcheckDomainVerifier
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section

/-! Canonical budgets for the retained Sumcheck round and arbitrary loop bounds.
Only the final specialization selects the retained Entry's static maximum.
The helpers are the admitted program's Domain helpers; their charges are the
actual executable local-function costs at the reached arguments. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckDomainFamily
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Structured
open SumcheckShape

abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩
def maximum : Nat := maximumOf ZkcExamples.Construction.SumcheckProof.participant.instructions

/-- Names read from the actual retained participant. -/
def names : Names := Names.of ZkcExamples.Construction.SumcheckProof.participant.instructions

def lowered (maximum : Nat) : Lowered :=
  ⟨code names maximum, [8, 7], [.loop 2 maximum [.receive coordinate, .receive coordinate]]⟩

-- The generated facts expose the same executable reading, including returns.
theorem lowered_eq : ZkcExamples.Executable.SumcheckProof.lowered = lowered maximum := by kernel_rfl

def roundPrefix : List Code := (roundCode names).take 27
def roundSuffix : List Code := (roundCode names).drop 28

theorem round_split : roundCode names = roundPrefix ++
    [.helper ⟨.call names.appendHelper, [6, 21], [.data (.vector names.scalar)], []⟩] ++ roundSuffix := by
  decide +kernel

theorem roundPrefix_static : Code.static roundPrefix = some 28 := by decide +kernel
theorem roundSuffix_static : Code.static roundSuffix = some 7 := by decide +kernel

theorem round_charge : Code.charges (helperBound ZkcExamples.Executable.SumcheckProof.validator) (roundCode names) = some 38 := by decide +kernel

def roundCharge : Nat :=
  (Code.charges (helperBound ZkcExamples.Executable.SumcheckProof.validator) (roundCode names)).getD 0

def charge (rounds : Nat) : Nat :=
  1 + 2 + 1 + rounds * (roundCharge + 1) + 1 + (62 + 20 * rounds) + 1

theorem charge_eq (rounds : Nat) : charge rounds = 68 + 59 * rounds := by
  simp only [charge, roundCharge, round_charge, Option.getD_some]
  omega

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev cost : String → List (Value F G) → Nat := helperCost installed ZkcExamples.Executable.SumcheckProof.validator

def Carried (count : Nat) (values : DomainVM.Environment F G) (_ : Proof F G) : Prop :=
  ∃ point scalar history, values = ZkcExamples.Construction.SumcheckDomainConnection.carried point scalar history ∧ point.length = count

/-- A round's charge and the runtime point-length invariant hold for all typed
replies, independently of the public table, current claim and proof stream. -/
theorem round_fits (a b c d e : Domain.Value (Structured.uniformCarriers F G))
    (index : Nat) (point : List F) (scalar : F) (history : Domain.History (Structured.uniformCarriers F G))
    (proof : Proof F G) (used budget : Nat) (within : used + 38 ≤ budget) :
    DomainVM.FitsK ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context cost budget (roundCode names)
      (ZkcExamples.Construction.SumcheckDomainConnection.roundInputs [a,b,c,d,e] index point scalar history) proof used
      (fun final unread charged => charged ≤ used + 38 ∧ ∀ values,
        Domain.read final yielded = some values →
          Domain.sortsMatch (carriedSorts names) values = true → Carried (point.length + 1) values unread) := by
  rw [round_split, DomainVM.FitsK.append]
  apply DomainVM.FitsK.of_static ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context cost budget roundPrefix roundPrefix_static _ _ used _ (by omega)
  have lowResolved := ZkcExamples.Construction.SumcheckDomainConnection.low_origin index
  have highResolved := ZkcExamples.Construction.SumcheckDomainConnection.high_origin index
  have drawResolved := ZkcExamples.Construction.SumcheckDomainConnection.draw_origin index
  have deliveryResolved := ZkcExamples.Construction.SumcheckDomainConnection.delivery_origin index
  have requests := ZkcExamples.Construction.SumcheckDomainConnection.message_requests index
  have drawRequest := ZkcExamples.Construction.SumcheckDomainConnection.draw_request index
  simp only [ZkcExamples.Construction.SumcheckDomainConnection.lowTemplate, ZkcExamples.Construction.SumcheckDomainConnection.highTemplate, ZkcExamples.Construction.SumcheckDomainConnection.drawTemplate, ZkcExamples.Construction.SumcheckDomainConnection.deliveryTemplate, ZkcExamples.Construction.SumcheckDomainConnection.roundBody, ZkcExamples.Construction.SumcheckDomainConnection.roundInstruction,
    ZkcExamples.Construction.SumcheckProof.participant, ZkcExamples.Construction.SumcheckProofParticipant.participant,
    List.getElem_cons_zero, List.getElem_cons_succ] at lowResolved highResolved drawResolved deliveryResolved requests drawRequest
  simp only [ZkcExamples.Construction.SumcheckDomainConnection.context_suite] at drawResolved
  apply DomainVM.Continues.of_yields_all_proofs
  normalize_artifact_operations [Domain.Calculations.fieldAdd (F := F) (G := G),
      Domain.Calculations.fieldEqual (F := F) (G := G), lowResolved, highResolved, drawResolved, deliveryResolved, requests.1,
      requests.2.1, requests.2.2, drawRequest, ZkcExamples.Construction.SumcheckDomainConnection.context_suite]
    unfolding [roundPrefix, List.take, Code.instructions, roundCode, roundBody, names, Names.of, operationAt, loopBody,
      ZkcExamples.Construction.SumcheckProof.participant, ZkcExamples.Construction.SumcheckProofParticipant.participant,
      ZkcExamples.Construction.SumcheckDomainConnection.roundInputs, Domain.evaluate, Domain.step, PIR.Yields,
      Structured.Ty.isService, Bool.not_false, Bool.not_true]

  intros ignored low ignored1 ignored2 ignored3 ignored4 ignored5 ignored6 ignored7 ignored8 ignored9 high
    ignored10 ignored11 ignored12 ignored13 ignored14 ignored15 ignored16 ignored17 ignored18 ignored19 ignored20 ignored21 ignored22
  by_cases valid : scalar = low + high
  all_goals simp only [valid, decide_true, decide_false]
  all_goals normalize_artifact_operations [lowResolved, highResolved, drawResolved, deliveryResolved,
      requests.1, requests.2.1, requests.2.2, drawRequest,
      ZkcExamples.Construction.SumcheckDomainConnection.context_suite]
    unfolding [PIR.Yields, Structured.Ty.isService, Bool.not_false, Bool.not_true]

  intro ignored24 ignored25 ignored26 ignored27 ignored28 ignored29 answer
  change F at answer
  intros
  have bound : helperBound ZkcExamples.Executable.SumcheckProof.validator names.appendHelper = some 2 := by kernel_rfl
  have price : cost names.appendHelper [(.vector "bls12-381.fr" point : Value F G), .data (.field "bls12-381.fr" answer)] ≤ 2 :=
    helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator bound _
  simp only [names, Names.of, operationAt, loopBody,
    ZkcExamples.Construction.SumcheckProof.participant, ZkcExamples.Construction.SumcheckProofParticipant.participant,
    List.getD_cons_zero, List.getD_cons_succ] at price
  simp only [DomainVM.FitsStep]
  normalize_artifact_operations [] unfolding [DomainVM.arguments, Uniform.DomainAdapter.readbackData,
    Uniform.DomainAdapter.readbackPayload]
  simp only [Eq.mp]
  refine ⟨by omega, _, rfl, ?_, ?_⟩
  · omega
  · apply DomainVM.Continues.of_yields_all_proofs
    normalize_artifact_operations [ZkcExamples.Construction.SumcheckDomainConnection.append_helper (G := G)]
      unfolding [Domain.step, PIR.Yields]
    intros
    simp only [DomainVM.FitsK]
    apply DomainVM.FitsK.of_static ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context cost budget roundSuffix roundSuffix_static
    · omega
    · apply DomainVM.Continues.of_yields_all_proofs
      normalize_artifact_operations [Domain.Calculations.fieldConstant (F := F) (G := G),
        Domain.Calculations.fieldSubtract (F := F) (G := G),
        Domain.Calculations.fieldMultiply (F := F) (G := G),
        Domain.Calculations.fieldAdd (F := F) (G := G)] unfolding [roundSuffix, List.drop, Code.instructions, roundCode, roundBody, names, Names.of, operationAt, loopBody,
        ZkcExamples.Construction.SumcheckProof.participant, ZkcExamples.Construction.SumcheckProofParticipant.participant,
        Domain.evaluate, Domain.step, PIR.Yields]

      intros
      refine ⟨by omega, ?_⟩
      intro values readEq sorted
      simp only [Option.some.injEq] at readEq
      subst values
      exact ⟨point ++ [answer], _, _, rfl, by simp⟩

/-- The retained schedule generalized only in its static maximum. All typed
public claims, proof streams and query replies are covered; a refused loop
bound has no post-entry charge obligation. -/
theorem sufficient_family (maximum : Nat) (small : maximum < 64) (budget : Nat)
    (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    DomainVM.Sufficient ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context cost budget (lowered maximum)
      (ZkcExamples.Construction.SumcheckDomainConnection.frame values claim rounds history) proof := by
  have emptyBound : helperBound ZkcExamples.Executable.SumcheckProof.validator names.emptyHelper = some 2 := by kernel_rfl
  have emptyPrice : cost names.emptyHelper ([] : List (Value F G)) ≤ 2 :=
    helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator emptyBound []
  have emptyPriceActual : cost "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f" ([] : List (Value F G)) ≤ 2 := emptyPrice
  have bound : 68 + 59 * rounds ≤ budget := by simpa only [charge_eq] using fits
  unfold DomainVM.Sufficient lowered code emptyCall
  apply DomainVM.FitsK.helper _ _ _ _ names.emptyHelper [] [.data (.vector names.scalar)] _ _ proof 0 _ [] [] rfl rfl
  · omega
  · normalize_artifact_operations [ZkcExamples.Construction.SumcheckDomainConnection.empty_helper (F := F) (G := G)]
      unfolding [Domain.step, DomainVM.Continues, names, Names.of, operationAt, loopBody,
        ZkcExamples.Construction.SumcheckProof.participant, ZkcExamples.Construction.SumcheckProofParticipant.participant]
    apply DomainVM.FitsK.loop_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      Carried 38 ⟨[], claim, history, rfl, rfl⟩
    · intro index carried unread charged valid within
      obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
      apply DomainVM.FitsK.mono _ _ _ _ _ _ _ _ _ _ ?_
        (round_fits (.data (.vector "bls12-381.fr" values)) (.data (.field "bls12-381.fr" claim))
          (.data (.index rounds)) (.transcript ZkcExamples.Construction.SumcheckProof.context.suite history)
          (.data (.vector "bls12-381.fr" [])) index point scalar suffix unread charged budget (by omega))
      intro final unread charged found
      refine ⟨found.1, ?_⟩
      intro result readEq sorted
      simpa only [length] using found.2 result readEq sorted
    · intro admitted
      omega
    · intro admitted carried unread charged valid smaller sorted
      obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
      have pointSmall : point.length < 64 := by omega
      have checkPrice := SumcheckHelpers.check_cost (G := G) (xs := values) (point := point) (claim := scalar) pointSmall
        (by rw [length]; exact shaped)
      apply DomainVM.FitsK.helper _ _ _ _ names.checkHelper [0,5,6] [.data .boolean] [] _ unread charged _
        [.data (.vector "bls12-381.fr" values), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar)]
        [.vector "bls12-381.fr" values, .vector "bls12-381.fr" point, .data (.field "bls12-381.fr" scalar)] rfl rfl
      · change charged + 1 + helperCost installed ZkcExamples.Executable.SumcheckProof.validator
          ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name _ ≤ budget
        rw [checkPrice, length]
        omega
      · apply DomainVM.Continues.of_forall
        intro final unread
        change charged + 1 + helperCost installed ZkcExamples.Executable.SumcheckProof.validator
          ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name _ + 1 ≤ budget
        rw [checkPrice, length]
        omega

/-- Canonical sufficiency for the exact retained Entry, with the same input
shape and budget assumptions as the old native-facing charge contract. -/
theorem sufficient (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    DomainVM.Sufficient ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context cost budget ZkcExamples.Executable.SumcheckProof.lowered
      (ZkcExamples.Construction.SumcheckDomainConnection.frame values claim rounds history) proof := by
  rw [lowered_eq]
  exact sufficient_family maximum (by decide +kernel) budget values claim rounds history proof shaped fits

end ZkcExamples.Executable.SumcheckDomainFamily
