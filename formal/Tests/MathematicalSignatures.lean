import Zkc.Source.Mathematical.SignatureAdmission
import Tests.MathematicalResolvedTypes
import Tests.MathematicalManifest

set_option autoImplicit false
namespace Tests.MathematicalSignatures
open Zkc.Source.Mathematical

def boolean : Raw.TypeUse := ⟨⟨0⟩, []⟩
def vector (count : Static.Raw) : Raw.TypeUse := ⟨⟨1⟩, [count]⟩

def capability : Raw.CapabilityType := ⟨⟨0⟩, 1, [vector (.parameter 0)], boolean⟩
def capabilityUse : Raw.CapabilityUse := ⟨⟨0⟩, [.add (.parameter 0) (.literal 0)]⟩
def operation : Raw.Operation := ⟨⟨0⟩, 1, [capabilityUse], [vector (.parameter 0)], boolean, .ordered, []⟩

def manifest : Raw.Manifest :=
  ⟨[], [MathematicalManifest.twiceIdentity], [MathematicalManifest.counterIdentity],
    [MathematicalManifest.counterIdentity], []⟩

def module : Raw.Module :=
  ⟨[], MathematicalResolvedTypes.templates, [operation],
    [⟨⟨0⟩, 1, vector (.parameter 0)⟩], [capability], [], [], [], ⟨⟨0⟩, [], [], []⟩⟩

private def asString {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

def check (source : Raw.Module) (statics : List Static.Raw) : Except String Bool :=
  (show StateT Nat (Except String) Bool from do
    let table ← asString (TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false) source.types)
    let selected ← asString (SignatureAdmission.operation MathematicalTypes.emptyMeaning table
      (fun _ : Fin 1 => (.literal ⟨8, by decide⟩ : Static.Expression 0)) source manifest 0 statics rfl)
    let wire ← asString (SignatureAdmission.wire MathematicalTypes.emptyMeaning table
      (fun _ : Fin 1 => (.literal ⟨8, by decide⟩ : Static.Expression 0)) source.wires manifest 0 statics)
    let signature := selected.signature
    return match signature.capabilities, signature.arguments with
      | [service], [argument] =>
          decide (service.identity = MathematicalManifest.counterIdentity) &&
          decide (service.arguments = [argument]) &&
          decide (service.result = signature.result) &&
          decide (wire.payload.expanded.shape = argument)
      | _, _ => false).run' 1000000

-- The operation object retains the source module's actual type table owner.
example {domains meaning rawTypes table arity target parameters source manifest index actuals}
    (selected : SignatureAdmission.Operation (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters source manifest index actuals) : source.types = rawTypes :=
  selected.typeTable

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match check module [.parameter 0] with | .ok result => result | .error _ => false)
    "substitution agrees across operation, capability and wire signatures"
  checks.holds (!(check module []).isOk) "operation static arity"
  checks.holds (!(check module [.parameter 1]).isOk) "caller static scope"
  checks.holds (!(check module [.multiply (.literal 0) (.pow2 (.literal 64))]).isOk)
    "operation arguments retain dormant overflow refusal"
  checks.holds (!(check { module with operations := [] } [.parameter 0]).isOk) "operation reference"
  checks.holds (!(check { module with operations := [{ operation with identity := ⟨1⟩ }] } [.parameter 0]).isOk)
    "operation manifest identity reference"
  checks.holds (!(check { module with capabilityTypes := [] } [.parameter 0]).isOk) "capability signature reference"
  checks.holds (!(check { module with capabilityTypes := [{ capability with identity := ⟨1⟩ }] } [.parameter 0]).isOk)
    "service manifest identity reference"
  checks.holds (!(check { module with capabilityTypes := [{ capability with statics := 2 }] } [.parameter 0]).isOk)
    "capability static arity"
  checks.holds (!(check { module with wires := [⟨⟨1⟩, 1, vector (.parameter 0)⟩] } [.parameter 0]).isOk)
    "wire manifest identity reference"
  checks.holds (!(check { module with wires := [⟨⟨0⟩, 1, vector (.parameter 1)⟩] } [.parameter 0]).isOk)
    "wire declaration has its own static scope"
  checks.finish "mathematical declaration signatures"

#eval run
end Tests.MathematicalSignatures
