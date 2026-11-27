module

@[expose] public section
set_option autoImplicit false

/-! The rule by which a name of the source stands in a Lean name, for the formal library's
commands that declare named views over a subject and for the checks that spell the names. -/

namespace Zkc.Subject

/-- Whether a name of the source can stand in a Lean name as it is: letters of the basic
alphabet, digits and underscores, not beginning with a digit. It is read byte by byte, with
operations that rest on no axiom beyond `propext` and `Quot.sound`, which is what the audit asks
of the subject library. -/
def plainSourceName (name : String) : Bool :=
  let digit (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57
  let letter (b : UInt8) : Bool := (65 ≤ b.toNat && b.toNat ≤ 90) || (97 ≤ b.toNat && b.toNat ≤ 122)
  match name.toUTF8.toList with
  | [] => false
  | b :: bs => !digit b && (b :: bs).all fun c => digit c || letter c || c.toNat == 95

/-- The Lean name of a deployed input, a function of the origins alone: `input_<name>`, or
`port<ordinal>` where the source name is not plain or is the name of `count - 1` other deployed
inputs. Nothing declared in a scope changes it. -/
def inputBinderName (raw : String) (ordinal count : Nat) : String :=
  if plainSourceName raw && count == 1 then "input_" ++ raw else s!"port{ordinal}"

/-- The Lean name of the validity of a deployed input whose name is `name`. -/
def validBinderName (name : String) : String := "valid_" ++ name

/-- The Lean name of the witness at a position of the relation's witness parameters. -/
def witnessBinderName (index : Nat) : String := s!"witness{index}"

end Zkc.Subject
