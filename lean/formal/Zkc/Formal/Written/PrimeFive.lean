module

public import Zkc.Formal.Written.ArithmeticModel
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace Zkc.Formal.Written.PrimeFive

scoped instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A small odd-characteristic instance for observing signs and a uniform returning challenge. -/
abbrev model := ArithmeticModel.model (ZMod 5) (ZMod 5)

end Zkc.Formal.Written.PrimeFive
