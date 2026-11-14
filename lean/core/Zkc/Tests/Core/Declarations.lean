import Zkc.Tests.Core.Check
import Zkc.Core.RoundTrip
import Zkc.Core.Laws
import Zkc.Tests.Core.Reflexivity

/-! Kernel checks for declared records and variants and for `match`.

- `fixtures/declarations.json` declares a record used exactly once, with a `nat` and a
  `bool` field, a variant of two alternatives with a `nat` and a `bool` payload, and a
  variant without alternatives. Its first function makes the record of its inputs, reads the
  `bool` field, injects the `nat` input into the first alternative when the field holds and
  the field into the second otherwise, and matches: the first region returns the payload, the
  second the literal 7. Its second function matches on a value of the variant without
  alternatives; it has no region, and no value to run on. The package elaborates, its typed
  package unelaborates to it, and its printed JSON reads back to it.
- The first function, for an arbitrary model: on `(n, true)` it returns `n`, on `(n, false)`
  it returns 7.
- Refusals: a type that names an undeclared record, and an operation of the core that names
  an undeclared record or variant, are refused alike; a position beyond the fields of a
  declared record; a match with fewer regions than its variant has alternatives. `Ty.named` refuses a record type whose use or shape is not its
  declaration's.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Declarations

/-! ## The JSON package -/

raw_package raw from file "fixtures/declarations.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl declared :
    (raw.records, raw.variants) equals
      (([⟨.exactlyOnce, [.nat, .bool]⟩], [⟨[.nat, .bool]⟩, ⟨[]⟩]) :
        List RecordDeclaration × List VariantDeclaration)
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/declarations.json"

kernel_refl reprinted_eq : reprinted equals raw

/-- The function that builds the record and matches on the variant: the older of the two. -/
abbrev chooses : Var typed.functions ⟨[.nat, .bool], [.nat], false⟩ := ⟨1, rfl⟩

/-- The record's field holds: the first alternative, whose region returns the payload. -/
theorem first_alternative (model : Model) (count : Nat) :
    (typed.program.functions.table model).get chooses (.cons count (.cons true .nil)) =
      .done (.cons count .nil) := kernel_rfl%

/-- The record's field does not hold: the second alternative, whose region returns 7. -/
theorem second_alternative (model : Model) (count : Nat) :
    (typed.program.functions.table model).get chooses (.cons count (.cons false .nil)) =
      .done (.cons (7 : Nat) .nil) := kernel_rfl%

/-! ## Refusals -/

/-- A function whose input names record 3 of a package without records. -/
abbrev undeclared : Raw.Package :=
  ⟨[], [], [], [], [⟨false, [.record 3 .free []], [.nat], some (.ret [])⟩], [], none⟩

kernel_refl undeclared_refused :
    (match elaborate undeclared with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.declaration, some (.function 0), []⟩

/-- The refusal of a package with one record of a `nat` field, no variant, and one function
without inputs and outputs. -/
abbrev refusalOf (body : Raw.LocalRegion) : Option Refusal :=
  match elaborate ⟨[], [⟨.free, [.nat]⟩], [], [], [⟨false, [], [], some body⟩], [], none⟩ with
  | .error refusal => some refusal
  | .ok _ => none

-- An operation of the core that names an undeclared record or variant is refused as a type
-- that names one is: `local.make`, `local.get`, `local.variant`, and an operation on a
-- sequence of an undeclared record. The refusal is at the instruction.
kernel_refl undeclared_make :
    refusalOf (.step (.builtin (.recordMake 3) []) (.ret [])) equals
      some ⟨.declaration, some (.function 0), [0]⟩
kernel_refl undeclared_get :
    refusalOf (.step (.builtin (.recordGet 3 0) [0]) (.ret [])) equals
      some ⟨.declaration, some (.function 0), [0]⟩
kernel_refl undeclared_variant :
    refusalOf (.step (.builtin (.variantMake 0 0) [0]) (.ret [])) equals
      some ⟨.declaration, some (.function 0), [0]⟩
kernel_refl undeclared_element :
    refusalOf (.step (.builtin (.seqLength (.record 3 .free []) none) [0]) (.ret [])) equals
      some ⟨.declaration, some (.function 0), [0]⟩

-- A position beyond the fields of a declared record is a refusal of the operation's data.
kernel_refl beyond_fields :
    refusalOf (.step (.builtin (.recordGet 0 5) [0]) (.ret [])) equals
      some ⟨.builtin, some (.function 0), [0]⟩

/-- A match with one region on a variant of two alternatives. -/
abbrev oneRegion : Raw.Package :=
  ⟨[], [], [⟨[.nat, .bool]⟩], [],
    [⟨false, [.variant 0 []], [.nat],
      some (.step (.match 0 0 [] [.nat] (.arm (.ret [0]) .none)) (.ret [1]))⟩], [], none⟩

kernel_refl oneRegion_refused :
    (match elaborate oneRegion with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.operand, some (.function 0), [0]⟩

/-- The type table of the fixture. -/
abbrev table : TypeTable := ⟨0, [⟨.exactlyOnce, [.nat, .bool]⟩], [⟨[.nat, .bool]⟩, ⟨[]⟩]⟩

kernel_refl named_record : Ty.named table (.record 0 .exactlyOnce [.nat, .bool]) equals true
kernel_refl other_use : Ty.named table (.record 0 .free [.nat, .bool]) equals false
kernel_refl other_shape : Ty.named table (.record 0 .exactlyOnce [.nat]) equals false
kernel_refl undeclared_record : Ty.named table (.record 1 .free []) equals false
kernel_refl other_alternatives : Ty.named table (.variant 0 [.nat]) equals false

#print axioms elaborate_eq
#print axioms first_alternative
#print axioms second_alternative

end Declarations
