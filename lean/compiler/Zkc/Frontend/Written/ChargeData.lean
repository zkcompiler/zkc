module

public import Zkc.Core.Program.Identity

@[expose] public section
namespace Zkc.Frontend.Written

/-- A closed source quotient and the ordered, definition-relative locations of its draw.
The model supplies the challenge alphabet and the formal consumer checks the locations. -/
structure DrawCharge where
  owner : Core.Key
  numerator : Nat
  denominator : Nat
  draws : List (List (Core.Key × Nat) × Core.Key)
  deriving DecidableEq, Repr

end Zkc.Frontend.Written
