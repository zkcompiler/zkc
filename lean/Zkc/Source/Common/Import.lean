module

public import Zkc.Source.Common.Vocabulary
public import Zkc.Source.ContextDecoding

@[expose] public section

/-! Checked binding and role admission of a native-exported snapshot.

References are de Bruijn positions in the current context, with original inputs
in declaration order. Every produced value is pushed at position zero. This
checker cannot authenticate the snapshot against its claimed native byte hash.
-/

set_option autoImplicit false

namespace Zkc.Source.Common.Native

def selected (roles : List Nat) : Nat → Bool := fun role => roles.contains role

def elaborate (returned : Nat) (result : Ty) :
    (Γ : List Ty) → List Instruction → Except (FormationError Ty) (Program Nat language services Γ result)
  | Γ, [] => return .ret (← decodeVariable Γ result returned)
  | Γ, .pure op args :: next => do
      let operands ← decodeOperands Γ (language.arguments op) args
      let body : Mathematical.Block Nat language Γ (language.result op) :=
        .letOp op operands (.ret .here)
      return .calculate body (← elaborate returned result (language.result op :: Γ) next)
  | Γ, .restrict roles ty index :: next => do
      let value ← decodeVariable Γ ty index
      let body : Mathematical.Block Nat language Γ ty := .restrict (selected roles) value (.ret .here)
      return .calculate body (← elaborate returned result (ty :: Γ) next)
  | Γ, .exchange site sender receiver ty index :: next => do
      return .exchange site sender receiver (← decodeVariable Γ ty index)
        (← elaborate returned result (ty :: Γ) next)
  | Γ, .draw site owner field index :: next => do
      let args ← decodeOperands Γ (services.arguments field) [index]
      return .query site owner field args (← elaborate returned result (.field field :: Γ) next)
  | Γ, .guard site owner index :: next => do
      return .guard site owner (← decodeVariable Γ .boolean index)
        (← elaborate returned result Γ next)
  | Γ, .statement relation types selectors args :: next => do
      return .statement relation selectors (← decodeOperands Γ types args)
        (← elaborate returned result Γ next)

def inputScopes : (types : List Ty) → List (List Nat) →
    Option (Values (fun _ => Nat → Bool) types)
  | [], [] => some .nil
  | _ :: types, scope :: scopes =>
      (inputScopes types scopes).map fun rest => .cons (selected scope) rest
  | _, _ => none

def Instruction.site : Instruction → Option String
  | .exchange site .. | .draw site .. | .guard site .. => some site
  | _ => none

def Snapshot.scopeValid (snapshot : Snapshot) (scope : List Nat) : Bool :=
  !scope.isEmpty && scope.all (fun role => role < snapshot.roles.length) && scope.length = scope.eraseDups.length

def Snapshot.shapeValid (snapshot : Snapshot) : Bool :=
  !snapshot.roles.isEmpty && snapshot.roles.length ≤ 16 &&
  snapshot.roles.all (fun role => !role.isEmpty) &&
  snapshot.roles.length = snapshot.roles.eraseDups.length &&
  snapshot.inputs.length ≤ 512 && snapshot.instructions.length ≤ 1024 &&
  snapshot.inputRoles.all snapshot.scopeValid && snapshot.scopeValid snapshot.outputRoles &&
  snapshot.instructions.all (fun instruction => match instruction with
    | .restrict roles .. => snapshot.scopeValid roles
    | .exchange site sender receiver .. =>
        !site.isEmpty && sender < snapshot.roles.length && receiver < snapshot.roles.length && sender != receiver
    | .draw site owner .. | .guard site owner _ => !site.isEmpty && owner < snapshot.roles.length
    | .pure (.select (.service _)) _ => false
    | .statement relation _ _ _ => !relation.isEmpty && snapshot.result == .boolean
    | _ => true) &&
  let sites := snapshot.instructions.filterMap Instruction.site
  sites.length = sites.eraseDups.length

/-- The carrier returned by `Snapshot.check`, retaining declaration, body and
scopes. Constructing this structure alone does not prove admission. Certificates
bind it to successful checking through `Zkc.Verification.Imported` or an explicit
checking equation. The native source hash is evidence metadata, never a proof
premise by itself. -/
structure Imported where
  snapshot : Snapshot
  program : Program Nat language services snapshot.inputs snapshot.result
  scopes : Values (fun _ => Nat → Bool) snapshot.inputs

def Snapshot.check (snapshot : Snapshot) : Except String Imported := do
  if !snapshot.shapeValid then throw "common-source-shape"
  let some scopes := inputScopes snapshot.inputs snapshot.inputRoles
    | throw "common-source-input-scopes"
  let program ← (elaborate snapshot.returned snapshot.result snapshot.inputs snapshot.instructions).mapError
    (fun _ => "common-source-operands")
  if !program.check (List.range snapshot.roles.length) scopes.get then throw "common-source-availability"
  if !snapshot.outputRoles.all (program.scope scopes.get) then throw "common-source-output-scope"
  return ⟨snapshot, program, scopes⟩

/-- Assemble an admitted source from independently exposed typed parts.
Clients can keep the program transparent without reducing the availability
checker during every dependent-type comparison. All admission premises remain. -/
theorem Snapshot.check_parts (snapshot : Snapshot)
    (program : Program Nat language services snapshot.inputs snapshot.result)
    (scopes : Values (fun _ => Nat → Bool) snapshot.inputs)
    (shape : snapshot.shapeValid = true)
    (inputs : inputScopes snapshot.inputs snapshot.inputRoles = some scopes)
    (body : elaborate snapshot.returned snapshot.result snapshot.inputs snapshot.instructions = .ok program)
    (available : program.check (List.range snapshot.roles.length) scopes.get = true)
    (output : snapshot.outputRoles.all (program.scope scopes.get) = true) :
    snapshot.check = .ok ⟨snapshot, program, scopes⟩ := by
  simp [Snapshot.check, shape, inputs, body, available, output,
    bind, pure, Except.bind, Except.mapError]
  rfl

theorem inputScopes_get (snapshot : Snapshot)
    (valid : (inputScopes snapshot.inputs snapshot.inputRoles).isSome) :
    inputScopes snapshot.inputs snapshot.inputRoles =
      some ((inputScopes snapshot.inputs snapshot.inputRoles).get valid) := by
  generalize result : inputScopes snapshot.inputs snapshot.inputRoles = checked at *
  cases checked with
  | none => cases valid
  | some scopes => rfl

def Imported.denote (imported : Imported) (meaning : Mathematical.Meaning language)
    (condition : meaning.Value .boolean → Bool) (self : Nat)
    (inputs : Values (fun ty => Option (meaning.Value ty)) imported.snapshot.inputs) :
    PIR.Proc (Participant.interface Nat Ty services meaning.Value) (Option (meaning.Value imported.snapshot.result)) :=
  (imported.program.denote meaning condition self inputs.get).bind fun value =>
    .done (Participant.restrict (decide (self ∈ imported.snapshot.outputRoles)) value)

end Zkc.Source.Common.Native
