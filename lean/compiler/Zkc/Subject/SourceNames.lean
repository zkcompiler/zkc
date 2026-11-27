module

@[expose] public section
set_option autoImplicit false

/-! The rule by which a name of the source stands in a Lean name, for the issuer and for the
formal library's tools that read the origins of a subject. -/

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

/-- The Lean name of a deployed input: `input_<name>`, or `port<ordinal>` where the source
name is not plain, is shared by another deployed input, or is taken (with its validity name)
in the scope where it is introduced. -/
def inputBinderName (raw : String) (ordinal count : Nat) (taken : String → Bool) : String :=
  let name := "input_" ++ raw
  if plainSourceName raw && count == 1 && !taken name && !taken ("valid_" ++ name) then name
  else s!"port{ordinal}"

end Zkc.Subject