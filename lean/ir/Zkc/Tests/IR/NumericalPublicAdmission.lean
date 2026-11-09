module

public import Zkc.IR.Executable.Installed

@[expose] public section

/-! Public clients must be able to check numerical-plan admission by kernel
reduction, without access to hidden implementation declarations. -/
namespace Tests.NumericalPublicAdmission
open Zkc.Executable Zkc.Algebra.RingExpression

example : Numerical.digitCount 0 = 1 ∧ Numerical.digitCount 9 = 1 ∧
    Numerical.digitCount 10 = 2 ∧ Numerical.digitCount 99 = 2 ∧
    Numerical.digitCount 100 = 3 ∧ Numerical.digitCount 256 = 3 := by decide +kernel

/-- The current compiled interpolation plan, with a broadcast challenge. -/
def interpolation : String :=
  "[\"zkc.numerical-plan/0\",[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",2],[\"input\",1],[\"neg\",0],[\"add\",2,3],[\"mul\",1,4],[\"add\",0,5]],[6]],256,4,[1,0,2,3,2,2,1]]"

example : Numerical.decode scalarField scalarCharacteristic [true, true, false] interpolation =
    .ok (.add (.input 0) (.mul (.input 2) (.add (.input 1) (.neg (.input 0))))) := by decide +kernel

end Tests.NumericalPublicAdmission
