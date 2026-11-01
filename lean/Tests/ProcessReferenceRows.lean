module

public import Zkc.Source.Structured.NormalForm.Denote
public import Zkc.Source.Structured.Bindings.Assembly
public meta import ZkcTools.StructuredSource.ProcessReference
public meta import ZkcTools.StructuredSource.NamedValues
public meta import Lean.Meta.Check

@[expose] public section

/-! Dependent callee rows are compacted under every optional branch. Source
signatures determine the complete row; equal-typed fields retain their order.
Both reference interfaces and all applicability premises remain kernel checked. -/
set_option autoImplicit false
namespace Tests.ProcessReferenceRows
open Zkc.Source Zkc.Source.Structured NormalForm
open PIR

def signature : ProtocolSignature :=
  ⟨"ordered-callee", ["role"], [.index, .index, .boolean], [.index], [[0], [0], [0]], [[0]]⟩

def key : CalleeKey :=
  ⟨signature, 0, Bindings.optionalPattern signature.inputs, []⟩

named_values Arguments [left, right, accepted] := key.pattern.scope

def selectedArguments : Values (Argument [] key.pattern.scope) key.pattern.scope :=
  id (.cons (.input .here) (.cons (.input (.there .here))
    (.cons (.input (.there (.there .here))) .nil)))

def source {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted stop : Option Bool) :
    Process I (Option Nat × Option Nat × Option Bool) :=
  match stop with
  | none => .halt .incomplete
  | some true => .halt .refused
  | some false => callee (Arguments.eval (Bindings.emptyResults model) selectedArguments
      (Arguments.pack { left, right, accepted }))

source_reference direct from @source using [source, selectedArguments]

example {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted : Option Bool) :
    direct model callee left right accepted (some false) =
      callee (Arguments.pack { left, right, accepted }) := rfl

example {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted : Option Bool) :
    direct model callee left right accepted none = .halt .incomplete := rfl

example {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted : Option Bool) :
    direct model callee left right accepted (some true) = .halt .refused := rfl

/-- A returned false decision remains a returned false decision. -/
example {I : PIR.Signature} (model : DomainModel) :
    direct (I := I) model (fun row => let data := Arguments.unpack row
      .done (data.left, data.right, data.accepted)) (some 3) (some 5) (some false) (some false) =
      .done (some 3, some 5, some false) := rfl

example {I : PIR.Signature} (model : DomainModel) :
    direct (I := I) model (fun row => let data := Arguments.unpack row
      .done (data.left, data.right, data.accepted)) (some 3) (some 5) none (some false) ≠
      .done (some 5, some 3, none) := by
  intro reversed
  cases reversed

-- The output telescope depends on the descriptor as well as its argument row.
-- Compacting only the visible values would leave these dependent indices behind.
def descriptors : List CalleeKey := [key]

def dependentSource {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model descriptors[0].pattern.scope →
      Process I (Values (Component model.Value) descriptors[0].signature.outputs))
    (left right : Option Nat) (accepted stop : Option Bool) :
    Process I (Values (Component model.Value) descriptors[0].signature.outputs) :=
  match stop with
  | none => .halt .incomplete
  | some true => .halt .refused
  | some false => callee (Arguments.eval (Bindings.emptyResults model) selectedArguments
      (Arguments.pack { left, right, accepted }))

source_reference dependent from @dependentSource using [dependentSource, selectedArguments]

example {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model descriptors[0].pattern.scope →
      Process I (Values (Component model.Value) [.index]))
    (left right : Option Nat) (accepted : Option Bool) :
    dependent model callee left right accepted (some false) =
      callee (Arguments.pack { left, right, accepted }) := rfl

/-- A source equation may rely on a mathematical admission premise. It stays
on the generated equation even when the runtime reference does not use it. -/
theorem admitted {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted stop : Option Bool) (expected : Nat)
    (present : left = some expected) :
    (if left = some expected then source model callee left right accepted stop else .halt .refused) =
      source model callee left right accepted stop := by
  simp only [present, ↓reduceIte]

source_reference checked from_equation @admitted using [source, selectedArguments]

example {I : PIR.Signature} (model : DomainModel)
    (callee : Binders model key.pattern.scope → Process I (Option Nat × Option Nat × Option Bool))
    (left right : Option Nat) (accepted stop : Option Bool) (expected : Nat)
    (present : left = some expected) :
    (if left = some expected then source model callee left right accepted stop else .halt .refused) =
      checked model callee left right accepted stop :=
  checked_equation model callee left right accepted stop expected present

example {I : PIR.Signature} (model : DomainModel) :
    (if (none : Option Nat) = some 7 then source (I := I) model (fun _ => .done (none, none, none))
      none none none (some false) else .halt .refused) ≠
      checked model (fun _ => .done (none, none, none)) none none none (some false) := by
  intro erasedPremise
  cases erasedPremise

open Lean Meta in
run_meta do
  for name in [`direct_certificate, `checked_certificate, `dependent_certificate] do
    let some body := (← getConstInfo (`Tests.ProcessReferenceRows ++ name)).value? | throwError "missing reference certificate"
    let mut body := body
    while body.isLambda do body := body.bindingBody!
    unless body.isAppOf ``Subtype.mk do throwError "reference is not shared"
    let runtime := body.getAppArgs[2]!
    for evaluator in [``NormalForm.Arguments.eval, ``NormalForm.Argument.eval,
        ``NormalForm.Comp.eval, ``NormalForm.entryAt] do
      if runtime.getUsedConstants.contains evaluator then
        throwError "dependent callee row retained evaluator {evaluator}"
  forallTelescopeReducing (← getConstInfo `Tests.ProcessReferenceRows.checked_equation).type fun parameters _ => do
    unless parameters.size == 9 do throwError "source premise telescope changed"
    unless ← isProp (← inferType parameters.back!) do throwError "admission premise missing"

-- Command failure remains transactional and does not install a partial view.
open Lean Elab Command in
run_cmd do
  let refused ← try
    ZkcTools.Generation.Commands.atomic "refusal-control" do
      elabCommand (← `(command| source_reference invalid from (fun n : Nat => n) using []))
    pure false
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure true
  unless refused do throwError "non-process reference was admitted"
  if (← getEnv).contains `Tests.ProcessReferenceRows.invalid_certificate ||
      (← getEnv).contains `Tests.ProcessReferenceRows.invalid then
    throwError "failed reference command leaked declarations"

#print axioms direct_equation
#print axioms checked_equation
#print axioms dependent_equation
end Tests.ProcessReferenceRows
