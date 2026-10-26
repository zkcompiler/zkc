module

public import Zkc.Construction.Uniform.DomainExecution
public import ZkcExamples.Construction.SumcheckArtifact
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.SumcheckSourceContracts

@[expose] public section

/-! The exact retained Sumcheck artifact at the nominal instruction meaning.
Legacy keys are a boundary projection of actual-coordinate occurrences. The
arbitrary legacy initialization is never serialized as a nominal public row. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Structured

theorem artifact_identity : ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact = SumcheckProof.participant := rfl

theorem source_identity :
    Generated.Bindings.SmallSumcheckInputs.imported.program = SumcheckProof.program := by kernel_rfl

/-- Erase the explicitly delimited actual-coordinate suffix at the legacy
boundary. Query fields, including the validator role, remain intact. -/
def legacyOrigin (origin : Origin) : Origin :=
  { origin with event := origin.event.takeWhile (· != "indices") }

abbrev roundInstruction : Construction.Instruction := SumcheckProof.participant.instructions[1]'(by decide +kernel)
abbrev roundBody : List Construction.Instruction := roundInstruction.body
abbrev lowTemplate : Template :=
  match (roundBody[3]'(by decide +kernel)).operation with
  | .observe _ template => template
  | _ => ⟨"", [], []⟩

abbrev highTemplate : Template :=
  match (roundBody[7]'(by decide +kernel)).operation with
  | .observe _ template => template
  | _ => ⟨"", [], []⟩

abbrev drawTemplate : Template :=
  match (roundBody[13]'(by decide +kernel)).operation with
  | .challenge _ _ template => template
  | _ => ⟨"", [], []⟩

abbrev deliveryTemplate : Template :=
  match (roundBody[16]'(by decide +kernel)).operation with
  | .observe _ template => template
  | _ => ⟨"", [], []⟩

def staticOrigin (template : Template) : Origin :=
  (template.origin SumcheckProof.context).getD ⟨"", [], none⟩

theorem low_origin (index : Nat) :
    Domain.templateOrigin SumcheckProof.context lowTemplate [index] =
      some (Domain.atCoordinates (staticOrigin lowTemplate) [index]) := by kernel_rfl

theorem high_origin (index : Nat) :
    Domain.templateOrigin SumcheckProof.context highTemplate [index] =
      some (Domain.atCoordinates (staticOrigin highTemplate) [index]) := by kernel_rfl

theorem draw_origin (index : Nat) :
    Domain.queryOrigin SumcheckProof.context SumcheckProof.context.suite "bls12-381.fr" drawTemplate [index] =
      some (Domain.atCoordinates (staticOrigin drawTemplate) [index]) := by kernel_rfl

theorem draw_request (index : Nat) :
    (Domain.atCoordinates (staticOrigin drawTemplate) [index]).request = some (.draw "bls12-381.fr") := by
  kernel_rfl

theorem delivery_origin (index : Nat) :
    Domain.templateOrigin SumcheckProof.context deliveryTemplate [index] =
      some (Domain.atCoordinates (staticOrigin deliveryTemplate) [index]) := by kernel_rfl

theorem message_requests (index : Nat) :
    (Domain.atCoordinates (staticOrigin lowTemplate) [index]).request = none ∧
    (Domain.atCoordinates (staticOrigin highTemplate) [index]).request = none ∧
    (Domain.atCoordinates (staticOrigin deliveryTemplate) [index]).request = none := by
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

theorem legacy_origins (index : Nat) :
    legacyOrigin (Domain.atCoordinates (staticOrigin lowTemplate) [index]) = staticOrigin lowTemplate ∧
    legacyOrigin (Domain.atCoordinates (staticOrigin highTemplate) [index]) = staticOrigin highTemplate ∧
    legacyOrigin (Domain.atCoordinates (staticOrigin drawTemplate) [index]) = staticOrigin drawTemplate ∧
    legacyOrigin (Domain.atCoordinates (staticOrigin deliveryTemplate) [index]) = staticOrigin deliveryTemplate := by
  constructor
  · kernel_rfl
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def inputs (values : List F) (claim : F) (rounds : Nat) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim), .data (.index rounds),
    .transcript SumcheckProof.context.suite []]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem input_sorts (values : List F) (claim : F) (rounds : Nat) :
    Domain.sortsMatch SumcheckProof.participant.inputs (inputs (G := G) values claim rounds) = true := by
  rfl

/-- The actual generated all-reply view is usable at the retained artifact and
the retained admitted source, not merely an Entry with an equal name. -/
theorem participant_equation (values : List F) (claim : F) (rounds : Nat) :
    Domain.participant (ringModel F G) SumcheckProof.program SumcheckProof.context SumcheckProof.participant
        (inputs values claim rounds) =
      ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.view (ringModel F G) SumcheckProof.program SumcheckProof.context (inputs values claim rounds) := by
  rw [← artifact_identity]
  exact ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.participant_eq _ _ _ _

theorem helper_outcome (helper : Helper)
    (present : helper ∈ SumcheckProof.program.payload.definitions.map CheckedDefinition.helper)
    (arguments : Values (assignment F G) helper.inputs)
    (encoded : Domain.Environment (uniformCarriers F G))
    (encoding : Domain.encodeValues arguments = some encoded) :
    Domain.callHelper (ringModel F G) SumcheckProof.program helper.name
        (helper.outputs.map ValueSort.data) encoded =
      match Domain.closedOutcome (invoke (Zkc.Construction.Uniform.helperTable SumcheckProof.program F G) helper arguments) with
      | .stopped reason => .stopped reason
      | .returned results =>
          match Domain.encodeValues results with
          | some values => .returned values
          | none => .stopped .refused := by
  obtain ⟨entry, found, same⟩ := Zkc.Construction.Uniform.helperTable_lookup (F := F) (G := G) SumcheckProof.program helper present
  subst helper
  have lookup : (Domain.helperTable (ringModel F G) SumcheckProof.program).find?
      (fun item => item.helper.name == entry.helper.name) = some entry := by
    rw [Domain.Binding.helperTable_ringModel]
    exact found
  rw [Domain.Binding.callHelper_of_lookup (ringModel F G) SumcheckProof.program entry lookup arguments encoded encoding]
  simp only [invoke, found, ↓reduceDIte]
  kernel_rfl

theorem helper_table : Zkc.Construction.Uniform.helperTable SumcheckProof.program F G =
    SumcheckSourceContracts.helperMeanings (F := F) (G := G) := rfl

theorem helper_present {helper : Helper} {body : Region dialect helper.inputs helper.outputs}
    (association : BodyIn SumcheckSourceViews.unit.definitions helper body) :
    helper ∈ SumcheckProof.program.payload.definitions.map CheckedDefinition.helper := by
  obtain ⟨definition, member, signature, _⟩ := association
  exact List.mem_map.mpr ⟨definition, member, signature⟩

theorem empty_helper :
    Domain.callHelper (ringModel F G) SumcheckProof.program SumcheckHelperBodies.emptyHelper.name
      [.data (.vector "bls12-381.fr")] [] = .returned [.data (.vector "bls12-381.fr" [])] := by
  have result := helper_outcome (F := F) (G := G) _
    (helper_present SumcheckSourceContracts.bodies.empty) .nil [] rfl
  rw [helper_table, SumcheckUnitContracts.empty_equation SumcheckSourceViews.unit.linked SumcheckSourceContracts.bodies] at result
  exact result

theorem append_helper (point : List F) (answer : F) :
    Domain.callHelper (ringModel F G) SumcheckProof.program SumcheckHelperBodies.appendHelper.name
      [.data (.vector "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" answer)] =
      .returned [.data (.vector "bls12-381.fr" (point ++ [answer]))] := by
  have result := helper_outcome (F := F) (G := G) _
    (helper_present SumcheckSourceContracts.bodies.append)
    (.cons point (.cons answer .nil)) _ rfl
  rw [helper_table, SumcheckUnitContracts.append_equation SumcheckSourceViews.unit.linked SumcheckSourceContracts.bodies] at result
  exact result

/-- Total helper equation: size failures remain exhausted and need no honest
resource assumption. It applies even to public tables outside the relation. -/
theorem check_helper (values point : List F) (claim : F) :
    Domain.callHelper (ringModel F G) SumcheckProof.program SumcheckHelperBodies.checkHelper.name
      [.data .boolean]
      [.data (.vector "bls12-381.fr" values), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] =
      if point.length < indexLimit then
        if point.length < 64 then
          if values.length < indexLimit then
            .returned [.data (.boolean (Zkc.Protocols.Sumcheck.Multilinear.check
              (n := 0 + point.length) values
              (Zkc.Polynomial.Quadratic.point point.length
                (Zkc.Polynomial.coordinates point.length point) Fin.elim0) claim))]
          else .stopped .exhausted
        else .returned [.data (.boolean false)]
      else .stopped .exhausted := by
  have result := helper_outcome (F := F) (G := G) _
    (helper_present SumcheckSourceAssociations.check_association)
    (SumcheckHelperLaws.checkInputs values point claim) _ rfl
  rw [helper_table, SumcheckSourceContracts.check_all] at result
  split_ifs at result ⊢ <;> exact result

end ZkcExamples.Construction.SumcheckDomainConnection
