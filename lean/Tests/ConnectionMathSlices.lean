module

public import ZkcTools.ConstructionBindings.MathRegion

@[expose] public section

/-! A closed source slice can occupy different caller frames. Same-typed
operand substitutions, a changed return selection and discarded physical work
must not acquire a connection merely by having the same signature. -/
set_option autoImplicit false
namespace Tests.ConnectionMathSlices
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ConnectionMathRegion

def body : Region dialect [.index, .index] [.index] :=
  .letOp .indexWrappingSubtract (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def target (left right : Nat) : TargetBlock := fun model ↦
  Domain.View.sequence
    (Domain.View.calculation model .indexWrappingSubtract [left, right] [.data .index])
    Domain.View.empty

/-- One derivation works at any pair of locations and any caller extent. -/
def placed (definitions : List CheckedDefinition) (left right extent : Nat) :
    Alignment definitions body [.data left, .data right] extent
      (target left right) [extent] (extent + 1) := by
  derive_math_region

/-- The actual core soundness rule supplies execution and frame preservation. -/
noncomputable def execution (definitions : List CheckedDefinition) (left right extent : Nat) :=
  (placed definitions left right extent).sound

example : Alignment [] body [.data 1, .data 0] 7 (target 1 0) [7] 8 := by
  derive_math_region

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7 (target 0 1) [7] 8 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7 (target 1 0) [0] 8 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [] body [.data 1, .data 0] 7
        (fun model ↦ Domain.View.sequence
          (Domain.View.calculation model .indexWrappingSubtract [1, 0] [.data .index])
          (target 1 0 model)) [7] 8 := by
      derive_math_region
  trivial

#print axioms placed
#print axioms execution

def subtract : CheckedDefinition where
  name := "subtract"
  kind := .math
  inputs := [.index, .index]
  outputs := [.index]
  raw := body.erase
  body := body
  formed := Region.elaborate_erase body

def twiceBody : Region dialect [.index, .index] [.index] :=
  .letOp (.invoke subtract.helper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.letOp (.invoke subtract.helper) (.cons .here (.cons (.there (.there .here)) .nil)) .nil
      (.ret (.cons .here .nil)))

def twice : CheckedDefinition where
  name := "twice"
  kind := .math
  inputs := [.index, .index]
  outputs := [.index]
  raw := twiceBody.erase
  body := twiceBody
  formed := Region.elaborate_erase twiceBody

def nestedBody : Region dialect [.index, .index] [.index] :=
  .letOp (.invoke twice.helper) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def nestedTarget (left right extent : Nat) : TargetBlock := fun model ↦
  Domain.View.sequence
    (Domain.View.calculation model .indexWrappingSubtract [left, right] [.data .index])
    (target extent right model)

/-- A nested checked call and its two inner applications share the same
derivation at arbitrary caller locations, without a helper-result assumption. -/
def nested (left right extent : Nat) :
    Alignment [subtract, twice] nestedBody [.data left, .data right] extent
      (nestedTarget left right extent) [extent + 1] (extent + 1 + 1) := by
  derive_math_region

noncomputable def nestedExecution (left right extent : Nat) := (nested left right extent).sound

example : True := by
  fail_if_success
    have : Alignment [subtract, twice] nestedBody [.data 1, .data 0] 7
        (nestedTarget 0 1 7) [8] 9 := by
      derive_math_region
  trivial

example : True := by
  fail_if_success
    have : Alignment [twice, subtract] nestedBody [.data 1, .data 0] 7
        (nestedTarget 1 0 7) [8] 9 := by
      derive_math_region
  trivial

#print axioms nested
#print axioms nestedExecution

def embeddedRegion : InstructionRegion :=
  ⟨[.data .index, .data .index],
    [⟨.calculate .indexWrappingSubtract, [0, 1], [.data .index], []⟩], [2]⟩

/-- The same typed mathematical slice installs inside the actual Math wrapper
at any caller position, retaining the caller frame and the existing arithmetic.
No second helper-result law or capture-layout proof is supplied by the author. -/
noncomputable def embedded (model : DomainModel) (program : Program) (context : Context)
    (caller : Domain.Environment model.toCarriers) (left right : Nat) :
    let environment := caller ++ [.data (.index left), .data (.index right)]
    Original.Simulation
      (fun result frame ↦ frame = environment ++ Original.encodeHelperResult result)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      ((body.denote (meaning model [])
        (show Values model.Value [.index, .index] from .cons left (.cons right .nil)).get).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context
        ⟨.mathCompute, [caller.length, caller.length + 1], [.data .index], [embeddedRegion]⟩
        environment) := by
  dsimp only
  apply (placed [] 0 1 2).embedded (captures := [.index, .index]) (sourceReferences := [0, 1])
    (region := embeddedRegion) (.cons .here (.cons (.there .here) .nil)) rfl
    model program context rfl rfl
    (Domain.Correspondence.sequence
      (Domain.Correspondence.calculation .indexWrappingSubtract [0, 1] [.data .index])
      Domain.Correspondence.empty) rfl rfl rfl (.cons left (.cons right .nil))
  simp [Domain.read, Domain.encodeValues_cons, Domain.encodeValues_nil,
    Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle]

/-- Closed stopping behavior passes through the same wrapper. There is no
successful-result or totality premise in embedded installation. -/
def readBody : Region dialect [.vector "F", .index] [.field "F"] :=
  .letOp (Calculation.boundedAt "F").op (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))
def stoppedRegion : InstructionRegion :=
  ⟨[.data (.vector "F"), .data .index],
    [⟨.calculate (.boundedAt "F"), [0, 1], [.data (.field "F")], []⟩], [2]⟩

noncomputable def stoppedEmbedded (model : DomainModel) (program : Program) (context : Context) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.vector "F", rfl, []⟩, .data (.index 0)]
    Original.Simulation
      (fun result frame ↦ frame = environment ++
        Original.encodeHelperResult (tys := [.field "F"]) result)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      (.halt .refused)
      (Domain.step model program context
        ⟨.mathCompute, [0, 1], [.data (.field "F")], [stoppedRegion]⟩ environment) := by
  let aligned : Alignment [] readBody (arguments 2) 2
      (fun model ↦ Domain.View.sequence
        (Domain.View.calculation model (.boundedAt "F") [0, 1] [.data (.field "F")])
        Domain.View.empty) [2] 3 := by derive_math_region
  exact aligned.embedded (region := stoppedRegion) (.cons .here (.cons (.there .here) .nil)) rfl
    model program context rfl rfl
    (Domain.Correspondence.sequence
      (Domain.Correspondence.calculation (.boundedAt "F") [0, 1] [.data (.field "F")])
      Domain.Correspondence.empty) rfl rfl rfl
    (.cons ([] : List (model.Field "F")) (.cons 0 .nil))
    [.data ⟨.vector "F", rfl, []⟩, .data (.index 0)] [0, 1] rfl

#print axioms embedded
#print axioms stoppedEmbedded
end Tests.ConnectionMathSlices
