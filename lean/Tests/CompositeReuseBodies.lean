import Tests.CompositeReuseSource
import Zkc.Semantics.WeakestPrecondition

/-! Equations of the admitted source, in the standard participant view that
forgets site marks. No provider action is erased in this view. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.CompositeReuseBodies
open Zkc.Source Zkc.Source.Structured
open Tests.CompositeReuseSource

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev I := participantInterface F G

structure Runtime (F : Type) where
  ignored : F
  value : Option F
  enabled : Bool

def tables : Evaluation.ComponentTables F G (I (F := F) (G := G)) := ⟨[], []⟩
def protocols : ProtocolTable (assignment F G) (I (F := F) (G := G)) :=
  unit.protocols.foldl (extendProtocolTable (.silent _) (participantActions F G) tables) []

def shiftInputs (delta : F) (runtime : Runtime F) :
    Values (Component (assignment F G)) Tests.Generated.CompositeReuseBodies.shiftSignature.inputs :=
  .cons (some runtime.ignored) (.cons runtime.value (.cons (some delta) (.cons (some runtime.enabled) .nil)))

def outerInputs (first second : F) (runtime : Runtime F) :
    Values (Component (assignment F G)) Tests.Generated.CompositeReuseBodies.outerSignature.inputs :=
  .cons (some runtime.ignored) (.cons runtime.value (.cons (some first) (.cons (some second)
    (.cons (some runtime.enabled) .nil))))

def thirdInputs (first second third : F) (runtime : Runtime F) :
    Values (Component (assignment F G)) Tests.Generated.CompositeReuseBodies.thirdSignature.inputs :=
  .cons (some runtime.ignored) (.cons runtime.value (.cons (some first) (.cons (some second)
    (.cons (some third) (.cons (some runtime.enabled) .nil)))))

def shift (delta : F) (runtime : Runtime F) : PIR.Process (I (F := F) (G := G)) (Option F) :=
  (shiftDefinition.denoteWith (.silent _) (participantActions F G) tables protocols
    (ProtocolContext.enter {} "shift" [1, 0]) 1 (shiftInputs delta runtime)).bind
      fun values => .done (values.get .here)

def outer (first second : F) (runtime : Runtime F) : PIR.Process (I (F := F) (G := G)) (Option F) :=
  (outerDefinition.denoteWith (.silent _) (participantActions F G) tables protocols
    {} 1 (outerInputs first second runtime)).bind fun values => .done (values.get .here)

def third (first second last : F) (runtime : Runtime F) : PIR.Process (I (F := F) (G := G)) (Option F) :=
  (thirdDefinition.denoteWith (.silent _) (participantActions F G) tables protocols
    {} 1 (thirdInputs first second last runtime)).bind fun values => .done (values.get .here)

def route (runtime : Runtime F) (value : Option F) : Runtime F := { runtime with value := value }

/-- The composite interface is the invocation of its actual admitted source
declaration, with the checked prefix table replaced by the linked full table. -/
theorem outer_invocation (first second : F) (runtime : Runtime F) :
    ((invokeProtocol protocols Tests.Generated.CompositeReuseBodies.outerSignature
      {} 1 (outerInputs first second runtime)).bind fun values => .done (values.get .here)) =
      outer (G := G) first second runtime := by
  have law := protocol_invoke_body_view (.silent _) (participantActions F G) tables
    unit.protocols unit.protocolsLinked outerDefinition outer_member
    Tests.Generated.CompositeReuseBodies.outerBody outer_raw {} 1 (outerInputs first second runtime)
  exact congrArg (fun process => process.bind fun values => .done (values.get .here)) law

/-- The exported Third interface is the selected source root in the standard
participant interpretation, which forgets only site observations. -/
theorem third_selected_root (first second last : F) (runtime : Runtime F) :
    ((program.participant F G 1 (thirdInputs first second last runtime)).bind
      fun values => .done (values.get .here)) = third (G := G) first second last runtime := by
  change ((invokeProtocol (unit.protocolTable F G)
    Tests.Generated.CompositeReuseBodies.thirdSignature {} 1
    (thirdInputs first second last runtime)).interpret forgetSites).bind _ = _
  rw [unit.protocolTable_forgetSites]
  have law := protocol_invoke_body_view (.silent _) (participantActions F G) tables
    unit.protocols unit.protocolsLinked thirdDefinition third_member
    Tests.Generated.CompositeReuseBodies.thirdBody third_raw {} 1 (thirdInputs first second last runtime)
  exact congrArg (fun process => process.bind fun values => .done (values.get .here)) law

theorem shift_binding (delta : F) (runtime : Runtime F) :
    shift (G := G) delta runtime =
      if runtime.enabled then .done (runtime.value.map (· + delta)) else .halt .reject := by
  rcases runtime with ⟨ignored, value, enabled⟩
  cases enabled <;> cases value <;> kernel_rfl

/-- Kernel reduction follows the two actual protocol applications, including
their second operands, swapped roles, and the enabled capture of the suffix. -/
theorem outer_binding (first second : F) (runtime : Runtime F) :
    outer (G := G) first second runtime =
      (shift first runtime).bind fun value => shift second (route runtime value) := by
  rcases runtime with ⟨ignored, value, enabled⟩
  cases enabled <;> cases value <;> kernel_rfl

/-- This equation exposes only the outer call boundary to the third client. -/
theorem third_binding (first second last : F) (runtime : Runtime F) :
    third (G := G) first second last runtime =
      (outer first second runtime).bind fun value => shift last (route runtime value) := by
  rcases runtime with ⟨ignored, value, enabled⟩
  cases enabled <;> cases value <;> kernel_rfl

end Tests.CompositeReuseBodies
