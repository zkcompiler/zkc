import Zkc.Source.LocalInputs

/-! Total results of admitted pure local source programs.

The optional projection is used only with a proof that binding and execution
return. It supplies no fallback for missing inputs or a stopped local program.
The execution boundary has unit state and an empty event type.
-/

set_option autoImplicit false

namespace Zkc.Source.LocalExecution

abbrev noEffects : PIR.Signature := ⟨Empty, fun op => nomatch op⟩
def noHandler : PIR.Handler noEffects Unit Empty := fun op => nomatch op

def returnedValue? {A : Type} : Except BindingError (PIR.Execution Unit Empty A) → Option A
  | .ok ⟨.returned value, _, _⟩ => some value
  | _ => none

end Zkc.Source.LocalExecution
