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
namespace ZkcExamples.Executable.SumcheckFamily
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

/-! A parameterized replacement for the retired Artifact interface. The local
round certificate is about actual Code/Domain continuations; it is independent
of oracle answers, honesty and whole-program execution equations. -/
namespace ProgramShape

structure Description where
  program : Structured.Program
  context : Context
  names : Names
  maximum : Nat
  small : maximum < 64
  suite : context.suite = names.suite

def inputs (shape : Description) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  [.data (.vector shape.names.scalar values), .data (.field shape.names.scalar claim),
    .data (.index rounds), .transcript shape.names.suite history]

def carried (shape : Description) (point : List F) (claim : F)
    (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim),
    .transcript shape.names.suite history]

def Invariant (shape : Description) (count : Nat) (env : DomainVM.Environment F G) (_ : Proof F G) : Prop :=
  ∃ point claim history, env = carried shape point claim history ∧ point.length = count

/-- Obligations at the actual program/helper boundary, replacing the former
Artifact's independent interpreter contracts. No whole-run equality is a field. -/
structure Contract (shape : Description) (cost : String → List (Value F G) → Nat) (roundCost : Nat) : Prop where
  empty : Domain.callHelper (Structured.ringModel F G) shape.program shape.names.emptyHelper
    [.data (.vector shape.names.scalar)] [] = .returned [.data (.vector shape.names.scalar [])]
  emptyCost : cost shape.names.emptyHelper [] ≤ 2
  checkCost : ∀ (values point : List F) (claim : F), point.length < 64 → values.length = 2 ^ point.length →
    cost shape.names.checkHelper [.vector shape.names.scalar values, .vector shape.names.scalar point,
      .data (.field shape.names.scalar claim)] = 62 + 20 * point.length
  round : ∀ (a b c d e : Domain.Value (Structured.uniformCarriers F G)) (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G) (used budget : Nat),
    used + roundCost ≤ budget →
    DomainVM.FitsK shape.program shape.context cost budget (roundCode shape.names)
      ([a,b,c,d,e] ++ .data (.index index) :: carried shape point claim history) proof used
      (fun final unread charged => charged ≤ used + roundCost ∧ ∀ values,
        Domain.read final yielded = some values → Domain.sortsMatch (carriedSorts shape.names) values = true →
          Invariant shape (point.length + 1) values unread)

def reading (shape : Description) : Lowered :=
  ⟨code shape.names shape.maximum, [8,7], []⟩

/-- Arbitrary programs, contexts, nominal names, helper implementations and
static maxima satisfying the local actual-program contract share this bound.
The receive plan is irrelevant to typed Code sufficiency. -/
theorem sufficient (shape : Description) (price : String → List (Value F G) → Nat)
    (roundCost : Nat) (contract : Contract shape price roundCost) (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : 68 + (roundCost + 21) * rounds ≤ budget) :
    DomainVM.Sufficient shape.program shape.context price budget (reading shape)
      (inputs shape values claim rounds history) proof := by
  have costIdentity : (roundCost + 21) * rounds = rounds * (roundCost + 1) + 20 * rounds := by ring
  rw [costIdentity] at fits
  have emptyPrice := contract.emptyCost
  unfold DomainVM.Sufficient reading code emptyCall
  apply DomainVM.FitsK.helper _ _ _ _ shape.names.emptyHelper [] [.data (.vector shape.names.scalar)] _ _ proof 0 _ [] [] rfl rfl
  · omega
  · simp only [Domain.step, Domain.read, List.mapM_nil, Option.pure_def, contract.empty]
    simp only [Domain.sortsMatch, List.map_cons, List.map_nil, Domain.Value.sort, beq_self_eq_true,
      ite_true, DomainVM.Continues]
    apply DomainVM.FitsK.loop_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (Invariant shape) roundCost ⟨[], claim, history, rfl, rfl⟩
    · intro index carried unread charged valid within
      obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
      apply DomainVM.FitsK.mono _ _ _ _ _ _ _ _ _ _ ?_
        (contract.round (.data (.vector shape.names.scalar values)) (.data (.field shape.names.scalar claim))
          (.data (.index rounds)) (.transcript shape.names.suite history) (.data (.vector shape.names.scalar []))
          index point scalar suffix unread charged budget (by omega))
      intro final unread charged found
      refine ⟨found.1, ?_⟩
      intro result readEq sorted
      simpa only [length] using found.2 result readEq sorted
    · intro admitted
      omega
    · intro admitted carried unread charged valid smaller sorted
      obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
      have pointSmall : point.length < 64 := by have := shape.small; omega
      have checkPrice := contract.checkCost values point scalar pointSmall (by rw [length]; exact shaped)
      apply DomainVM.FitsK.helper _ _ _ _ shape.names.checkHelper [0,5,6] [.data .boolean] [] _ unread charged _
        [.data (.vector shape.names.scalar values), .data (.vector shape.names.scalar point),
          .data (.field shape.names.scalar scalar)]
        [.vector shape.names.scalar values, .vector shape.names.scalar point,
          .data (.field shape.names.scalar scalar)] rfl rfl
      · rw [checkPrice, length]; omega
      · apply DomainVM.Continues.of_forall
        intro final unread
        simp only [DomainVM.FitsK]
        rw [checkPrice, length]; omega

/-- Honest completeness interface for an arbitrary actual program of the
shape. Mathematical success is an independent canonical Process obligation;
resource bounds alone cannot establish this hypothesis. -/
theorem honest_success (shape : Description) (price : String → List (Value F G) → Nat)
    (roundCost : Nat) (contract : Contract shape price roundCost) (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : 68 + (roundCost + 21) * rounds ≤ budget)
    (initial : History F G) (oracle : History F G → F)
    (holds : DomainVM.Environment F G → Proof F G → Prop)
    (passes : DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation shape.program shape.context (Code.instructions (reading shape).code)
        (reading shape).returned (inputs shape values claim rounds history)) proof holds) :
    ∃ returned unread, holds returned unread ∧
      DomainVM.metered (m := Id) shape.program shape.context Origin.withoutCoordinates initial oracle
        price budget (reading shape) (inputs shape values claim rounds history) proof = (.returned returned, unread) :=
  DomainVM.metered_success shape.program shape.context Origin.withoutCoordinates initial oracle price budget
    (reading shape) (inputs shape values claim rounds history) proof holds
    (sufficient shape price roundCost contract budget values claim rounds history proof shaped fits) passes

end ProgramShape

/-- Actual program instance of the parameterized canonical family. -/
def programShape (maximum : Nat) (small : maximum < 64) : ProgramShape.Description :=
  ⟨ZkcExamples.Construction.SumcheckProof.program, ZkcExamples.Construction.SumcheckProof.context,
    names, maximum, small, rfl⟩

theorem programContract (maximum : Nat) (small : maximum < 64) :
    ProgramShape.Contract (programShape maximum small) (cost (F := F) (G := G)) 38 where
  empty := ZkcExamples.Construction.SumcheckDomainConnection.empty_helper
  emptyCost := helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator
    (show helperBound ZkcExamples.Executable.SumcheckProof.validator names.emptyHelper = some 2 by kernel_rfl) []
  checkCost := fun _ _ _ small shaped => SumcheckHelpers.check_cost small shaped
  round := round_fits

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
  exact ProgramShape.sufficient (programShape maximum small) cost 38 (programContract maximum small)
    budget values claim rounds history proof shaped (by simpa only [charge_eq] using fits)

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



end ZkcExamples.Executable.SumcheckFamily
