module

public import ZkcSecurity.Families.Sumcheck.CompiledRound
public import ZkcSecurity.Examples.Components.SmallSumcheckHelpers
public import TestsSecurity.DomainSourceBridge

@[expose] public section

/-! Full adversarial-round integration against the actual retained artifact.
The generated whole-block equation, exact original helper bodies and nominal
occurrences are all consumed. This is a round control, not a whole-root proof. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace TestsSecurity.CompiledRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir.DomainReduction ZkcSecurity.Families.Sumcheck

abbrev artifact := ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact
abbrev context := TestsSecurity.DomainSourceBridge.context
abbrev field := TestsSecurity.DomainSourceBridge.field
noncomputable abbrev program := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program

def roundInstruction (index : Fin 23) : Zkc.Construction.Instruction :=
  ((artifact.instructions[1]'(by decide +kernel)).body[index.val]'(by
    have bound := index.isLt
    change index.val < 23
    exact bound))

def occurrence (index : Fin 23) : Template :=
  match (roundInstruction index).operation with
  | .observe _ template | .challenge _ _ template => template
  | _ => ⟨"", [], []⟩

def plan : CompiledRound.Plan where
  lowSite := match (roundInstruction 0).operation with | .receive site _ _ _ => site | _ => ""
  highSite := match (roundInstruction 4).operation with | .receive site _ _ _ => site | _ => ""
  producer := match (roundInstruction 0).operation with | .receive _ _ peer _ => peer | _ => ""
  lowTemplate := occurrence 3
  highTemplate := occurrence 7
  queryTemplate := occurrence 13
  deliveryTemplate := occurrence 16
  appendHelper := match (roundInstruction 17).operation with | .call helper => helper | _ => ""

/-- The actual block, with every checkpoint and result slot, has this view. -/
theorem actual_block (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] :
    Domain.evaluate (ringModel F G) program context (artifact.instructions[1]'(by decide +kernel)).body =
      CompiledRound.block plan program context field 5 := by
  funext env
  rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1Body_eq]
  rfl

def lowBase : Origin :=
  (plan.lowTemplate.origin context).get (by decide +kernel)

abbrev lowOrigin (index : Nat) : Origin := Domain.atCoordinates lowBase [index]

theorem low_found (index : Nat) :
    Domain.templateOrigin context plan.lowTemplate [index] = some (lowOrigin index) := by
  change (plan.lowTemplate.origin context).map (Domain.atCoordinates · [index]) = _
  exact congrArg (Option.map (Domain.atCoordinates · [index])) (Option.some_get _).symm

theorem low_request (index : Nat) : (lowOrigin index).request = none := by
  change lowBase.request = _
  decide +kernel

def highBase : Origin :=
  (plan.highTemplate.origin context).get (by decide +kernel)

abbrev highOrigin (index : Nat) : Origin := Domain.atCoordinates highBase [index]

theorem high_found (index : Nat) :
    Domain.templateOrigin context plan.highTemplate [index] = some (highOrigin index) := by
  change (plan.highTemplate.origin context).map (Domain.atCoordinates · [index]) = _
  exact congrArg (Option.map (Domain.atCoordinates · [index])) (Option.some_get _).symm

theorem high_request (index : Nat) : (highOrigin index).request = none := by
  change highBase.request = _
  decide +kernel

def deliveryBase : Origin :=
  (plan.deliveryTemplate.origin context).get (by decide +kernel)

abbrev deliveryOrigin (index : Nat) : Origin := Domain.atCoordinates deliveryBase [index]

theorem delivery_found (index : Nat) :
    Domain.templateOrigin context plan.deliveryTemplate [index] = some (deliveryOrigin index) := by
  change (plan.deliveryTemplate.origin context).map (Domain.atCoordinates · [index]) = _
  exact congrArg (Option.map (Domain.atCoordinates · [index])) (Option.some_get _).symm

theorem delivery_request (index : Nat) : (deliveryOrigin index).request = none := by
  change deliveryBase.request = _
  decide +kernel

def queryBase : Origin :=
  (plan.queryTemplate.origin context).get (by decide +kernel)

abbrev queryOrigin (index : Nat) : Origin := Domain.atCoordinates queryBase [index]

theorem query_found (index : Nat) :
    Domain.templateOrigin context plan.queryTemplate [index] = some (queryOrigin index) := by
  change (plan.queryTemplate.origin context).map (Domain.atCoordinates · [index]) = _
  exact congrArg (Option.map (Domain.atCoordinates · [index])) (Option.some_get _).symm

theorem query_request (index : Nat) : (queryOrigin index).request = some (.draw field) := by
  change queryBase.request = _
  decide +kernel

theorem query_resolved (index : Nat) :
    Domain.queryOrigin context context.suite field plan.queryTemplate [index] = some (queryOrigin index) := by
  unfold Domain.queryOrigin
  rw [ite_eq_left (by decide +kernel), query_found index]
  simp only [query_request, ite_true]

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- No arithmetic or helper premise is open: all received scalar pairs and
challenge replies use the actual admitted source program's append helper. -/
theorem actual_round
    (captured : Domain.Environment (uniformCarriers F G)) (capturedLength : captured.length = 5)
    (index : Nat) (point : List F) (claim : F) (history : Domain.History (uniformCarriers F G))
    (Post : Domain.History (uniformCarriers F G) → Domain.Environment (uniformCarriers F G) → Prop)
    (post : ∀ low high challenge, claim = low + high →
      Post (CompiledRound.finalHistory field (lowOrigin index) (highOrigin index)
        (queryOrigin index) (deliveryOrigin index) history low high challenge)
        (CompiledRound.output field context.suite captured index point claim history
          (lowOrigin index) (highOrigin index) (queryOrigin index) (deliveryOrigin index) low high challenge)) :
    Bridge (TableComponent.Nominal.interface (F := F) (G := G) field) Post history
      (Domain.evaluate (ringModel F G) program context (artifact.instructions[1]'(by decide +kernel)).body
        (CompiledRound.input field context.suite captured index point claim history))
      (CompiledRound.presented field context.suite captured index point claim history
        (lowOrigin index) (highOrigin index) (queryOrigin index) (deliveryOrigin index) (query_request index)) := by
  rw [actual_block]
  rw [← capturedLength]
  have appendLaw : ∀ point challenge,
      Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector field)]
        [.data (.vector field point), .data (.field field challenge)] =
        .returned [.data (.vector field (point ++ [challenge]))] := by
    intro point challenge
    exact ZkcSecurity.Realizations.Sumcheck.DomainHelpers.append (F := F) (G := G) program
      ZkcSecurity.Examples.Components.SmallSumcheck.helper_bodies.sumcheck point challenge
  constructor
  · exact CompiledRound.reading plan program context field captured index point claim history
      (lowOrigin index) (highOrigin index) (queryOrigin index) (deliveryOrigin index)
      (low_found index) (high_found index) (query_resolved index) (delivery_found index)
      (low_request index) (high_request index) (delivery_request index) (query_request index)
      appendLaw Post post
  · exact CompiledRound.coherent plan program context field captured index point claim history
      (lowOrigin index) (highOrigin index) (queryOrigin index) (deliveryOrigin index)
      (low_found index) (high_found index) (query_resolved index) (delivery_found index)
      (low_request index) (high_request index) (delivery_request index) (query_request index)
      appendLaw Post post

#print axioms actual_round

end TestsSecurity.CompiledRound
