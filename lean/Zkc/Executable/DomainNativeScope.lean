module

public import Zkc.Executable.DomainCpuOperations
public import Zkc.Executable.DomainHelpers

@[expose] public section

/-! Finite nominal eligibility of native Code readings. The certificate contains
only structural schemas, occurrence metadata and coordinate depths. It never
contains an execution equation, a numerical relation or an honest-input premise.
The original native reader remains independently checked. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source

/-- Static coordinate depth is part of the nominal scope, even though the
retained native ABI erases it from the sort of an indices value. -/
inductive NativeSlot where
  | data (type : Structured.Ty)
  | transcript (suite : String)
  | indices (depth : Nat)
  deriving DecidableEq, Repr

def NativeSlot.sort : NativeSlot → ValueSort
  | .data ty => .data ty
  | .transcript suite => .transcript suite
  | .indices _ => .indices

def NativeSlot.ofSort : ValueSort → NativeSlot
  | .data ty => .data ty
  | .transcript suite => .transcript suite
  | .indices => .indices 0

/-- The current transcript is checked separately from its suite. -/
structure NativeScope where
  slots : List NativeSlot
  current : Nat
  deriving DecidableEq, Repr

def NativeScope.reading (scope : NativeScope) : Reading :=
  ⟨scope.slots.map NativeSlot.sort, scope.current⟩

def NativeScope.append (scope : NativeScope) (results : List NativeSlot) (advances : Bool := false) : NativeScope :=
  ⟨scope.slots ++ results, if advances then scope.slots.length + results.length - 1 else scope.current⟩

/-- Exactly the metadata pushed by the admitted helper table, in lookup order. -/
def nativeHelperSignatures (program : Structured.Program) : List Structured.Helper :=
  program.payload.definitions.reverse.map (·.helper)

/-- Both path kinds and the root Entry are inspected, before event interpretation. -/
def nativeTemplate (context : Context) (depth : Nat) (template : Template) : Bool :=
  template.entry == context.entry && template.repeats == depth &&
    template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat")

def nativeMessageEvent : List String → Bool
  | ["message", _, site, schema, _, _] => site == schema
  | _ => false

def nativeQueryEvent : List String → Bool
  | ["query", _, _, _, _, "draw", _] => true
  | _ => false

/-- Finite declaration checks for one nonloop operation. Empty bodies are
checked by the owning Code check, below. Unsupported scalar envelopes refuse. -/
def nativeResults (program : Structured.Program) (context : Context) (scope : NativeScope)
    (operation : Operation) (operands : List Nat) : Option (List NativeSlot × Bool) :=
  match operation, operands with
  | .receive site schema _ ty, [] =>
      if site = schema ∧ (scalarType ty).isSome then some ([.data ty], false) else none
  | .indicesEmpty, [] => some ([.indices 0], false)
  | .indicesAppend, [coordinates, index] =>
      match scope.slots[coordinates]?, scope.slots[index]? with
      | some (.indices depth), some (.data .index) => some ([.indices (depth + 1)], false)
      | _, _ => none
  | .observe suite template, [state, value, coordinates] =>
      match scope.slots[state]?, scope.slots[value]?, scope.slots[coordinates]? with
      | some (.transcript actual), some (.data ty), some (.indices depth) =>
          if state = scope.current ∧ suite = actual ∧ suite = context.suite ∧
              (scalarType ty).isSome ∧ nativeTemplate context depth template ∧ nativeMessageEvent template.event then
            some ([.transcript suite], true) else none
      | _, _, _ => none
  | .challenge suite field template, [state, coordinates] =>
      match scope.slots[state]?, scope.slots[coordinates]? with
      | some (.transcript actual), some (.indices depth) =>
          if state = scope.current ∧ actual = suite ∧ suite = context.suite ∧
              context.contract = "random." ++ field ++ "/0" ∧ context.request = some (.draw field) ∧
              nativeTemplate context depth template ∧ nativeQueryEvent template.event then
            some ([.data (.field field), .transcript suite], true) else none
      | _, _ => none
  | .calculate calculation, references =>
      if references.map (scope.slots[·]?) = calculation.op.arguments.map (some ∘ NativeSlot.data) ∧
          calculation.op.arguments.all dataType ∧ calculation.op.results.all dataType then
        some (calculation.op.results.map NativeSlot.data, false) else none
  | .call name, references =>
      match (nativeHelperSignatures program).find? (fun helper => helper.name == name) with
      | some helper =>
          if references.map (scope.slots[·]?) = helper.inputs.map (some ∘ NativeSlot.data) ∧
              helper.inputs.all dataType ∧ helper.outputs.all dataType then
            some (helper.outputs.map NativeSlot.data, false) else none
      | none => none
  | .guard _, [condition] =>
      if scope.slots[condition]? = some (.data .boolean) then some ([], false) else none
  | _, _ => none

mutual
/-- Check the complete structural scope without executing any instruction. -/
def checkNativeCode (program : Structured.Program) (context : Context) :
    List Code → NativeScope → Option NativeScope
  | [], scope => some scope
  | code :: rest, scope => do
      let next ← checkNativeItem program context code scope
      checkNativeCode program context rest next

def checkNativeItem (program : Structured.Program) (context : Context) :
    Code → NativeScope → Option NativeScope
  | .charge _, scope => some scope
  | .step ⟨operation, operands, declared, []⟩ _, scope => do
      let (results, advances) ← nativeResults program context scope operation operands
      if results.map NativeSlot.sort = declared then some (scope.append results advances) else none
  | .helper ⟨.call name, operands, declared, []⟩, scope => do
      let (results, advances) ← nativeResults program context scope (.call name) operands
      if results.map NativeSlot.sort = declared then some (scope.append results advances) else none
  | .loop _ _ yielded (count :: references) declared body, scope => do
      if scope.slots[count]? ≠ some (.data .index) then none else do
        let carried ← references.mapM (scope.slots[·]?)
        if carried.map NativeSlot.sort ≠ declared ∨
            !custody (scope.slots.map NativeSlot.sort) scope.current references then none else do
          let innerCurrent := match transcriptPosition declared with
            | some position => scope.slots.length + 1 + position
            | none => scope.current
          let final ← checkNativeCode program context body
            ⟨scope.slots ++ .data .index :: carried, innerCurrent⟩
          if yielded.map (final.slots[·]?) ≠ carried.map some ∨
              !custody (final.slots.map NativeSlot.sort) final.current yielded ∨
              (transcriptPosition declared = none ∧ final.current ≠ scope.current) then none else
            some ⟨scope.slots ++ carried, match transcriptPosition declared with
              | some position => scope.slots.length + position
              | none => scope.current⟩
  | _, _ => none
end

/-- A compact certificate is the final structural scope and a successful finite
check. Its proof field is a check result, never the desired semantic equation. -/
structure NativeCertificate (program : Structured.Program) (context : Context)
    (code : List Code) (start : NativeScope) where
  final : NativeScope
  checked : checkNativeCode program context code start = some final

theorem checkNativeCode_append (program : Structured.Program) (context : Context) :
    ∀ (first second : List Code) (scope : NativeScope),
      checkNativeCode program context (first ++ second) scope =
        (checkNativeCode program context first scope).bind (checkNativeCode program context second)
  | [], _, _ => rfl
  | head :: tail, second, scope => by
      simp only [List.cons_append, checkNativeCode]
      cases checkNativeItem program context head scope <;>
        simp [checkNativeCode_append program context tail second]

variable {F G : Type}

/-- Scope truth is nominal schema truth and actual coordinate length, not a
source relation. All field/group/index values remain arbitrary. -/
def NativeSlot.Holds (slot : NativeSlot) (value : Domain.Value (Structured.uniformCarriers F G)) : Prop :=
  match slot with
  | .data ty => value.sort = .data ty
  | .transcript suite => value.sort = .transcript suite
  | .indices depth => ∃ path, value = .indices path ∧ path.length = depth

def NativeScope.Holds (scope : NativeScope) (env : Environment F G) : Prop :=
  List.Forall₂ NativeSlot.Holds scope.slots env

theorem NativeSlot.Holds.sort {slot : NativeSlot} {value : Domain.Value (Structured.uniformCarriers F G)}
    (holds : slot.Holds value) : value.sort = slot.sort := by
  cases slot with
  | data | transcript => exact holds
  | indices depth => obtain ⟨path, rfl, _⟩ := holds; rfl

theorem NativeScope.Holds.schema {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) : env.map Domain.Value.sort = scope.slots.map NativeSlot.sort := by
  unfold NativeScope.Holds at holds
  generalize scope.slots = slots at holds ⊢
  induction holds with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.sort, ih]

/-- Every selected slot is present, with its real nominal value. -/
theorem NativeScope.Holds.get {scope : NativeScope} {env : Environment F G}
    (holds : scope.Holds env) {reference : Nat} {slot : NativeSlot}
    (found : scope.slots[reference]? = some slot) :
    ∃ value, env[reference]? = some value ∧ slot.Holds value := by
  rcases scope with ⟨slots, current⟩
  change List.Forall₂ NativeSlot.Holds slots env at holds
  change slots[reference]? = some slot at found
  induction holds generalizing reference with
  | nil => simp at found
  | cons head tail ih =>
      cases reference with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst slot
                exact ⟨_, rfl, head⟩
      | succ reference => exact ih found

end Zkc.Executable.DomainVM
