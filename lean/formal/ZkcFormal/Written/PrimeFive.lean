module

public import ZkcFormal.Written.ArithmeticModel
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace ZkcFormal.Written.PrimeFive

scoped instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A small odd-characteristic instance for observing signs and a uniform returning challenge. -/
abbrev model := ArithmeticModel.model (ZMod 5) (ZMod 5)

end ZkcFormal.Written.PrimeFive
