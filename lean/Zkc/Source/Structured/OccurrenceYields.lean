module

public import Zkc.Source.Structured.Occurrence
public import Zkc.Semantics.Yields

@[expose] public section

/-! Return invariants through occurrence boundaries. These facts quantify over
every reply; they do not provide a successful execution of a stopped process. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OccurrenceYields
open Zkc.Source Zkc.Source.Structured

theorem within {carriers : Carriers} {A : Type} {property : A → Prop}
    (site : String) (index : Nat)
    (process : PIR.Process (Occurrence.signature carriers) A)
    (holds : PIR.Yields property process) :
    PIR.Yields property (Occurrence.iterations.within site index process) := by
  exact fun _ => holds.bind fun _ result => fun _ => result

end Zkc.Source.Structured.OccurrenceYields
