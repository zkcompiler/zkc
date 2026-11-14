import Zkc.Core.Concrete

/-! Equality of data is decided in the kernel.

The model that runs compares data at every guard on an element of a field. These statements
are closed by `decide` and by `rfl`, so a statement about a run of that model can be checked by
the kernel and not only by compiled code. -/

set_option autoImplicit false

open Zkc.Core.Concrete

namespace DataEquality

example : (Datum.number 1 == Datum.number 1) = true := by decide
example : (Datum.number 1 == Datum.number 2) = false := by decide
example : Datum.sequence [.number 1, .sequence [.number 2]] =
    .sequence [.number 1, .sequence [.number 2]] := by decide
example : Datum.number 1 ≠ .sequence [] := by decide
example : (Datum.sequence [.number 1, .number 2] == .sequence [.number 1, .number 2]) = true := rfl
example : (Datum.ofPoint generator == Datum.ofPoint generator) = true := by decide

end DataEquality
