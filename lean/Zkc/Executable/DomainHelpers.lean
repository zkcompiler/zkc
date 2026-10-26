module

public import Zkc.Executable.HelperSoundness
public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Checked native helpers target the actual admitted Domain table. The native
cost is still the cost of the executable function at its supplied arguments;
no formula for mathematical helper work is substituted. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The existing helper checker establishes Prepared for the canonical table.
This transports its typed result/stop proof, not a success assumption. -/
theorem checkHelpers_prepared (vocabulary : Vocabulary) (validator : Validator)
    (program : Structured.Program) {names : List String}
    (checked : checkHelpers vocabulary validator program names = .ok ()) :
    ∀ name ∈ names, Prepared vocabulary validator
      (Domain.helperTable (Structured.ringModel F G) program) name := by
  rw [Uniform.DomainAdapter.helperTable_eq]
  exact checkHelpers_sound vocabulary validator program checked

end Zkc.Executable.DomainVM
