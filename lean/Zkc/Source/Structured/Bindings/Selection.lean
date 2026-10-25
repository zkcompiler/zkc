module

public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Exact syntax selection for generated callback bindings. This traverses the
retained typed Region, not an execution model or a second representation. -/

namespace Zkc.Source.Structured.Bindings

abbrev CallbackBody := Σ inputs outputs, Region protocolDialect inputs outputs

/-- Select the first repeat bearing this retained site, including nested
callbacks. Generated equations check its complete typed body independently. -/
def findRepeat (site : String) : {inputs outputs : List Ty} →
    Region protocolDialect inputs outputs → Option CallbackBody
  | _, _, .ret _ | _, _, .stop _ => none
  | _, _, .bind body next => (findRepeat site body).orElse fun _ => findRepeat site next
  | _, _, .letOp op _ bodies next =>
    let inner : Option CallbackBody := match op, bodies with
      | .repeat _ found, .cons body .nil =>
        if found == site then some ⟨_, _, body⟩ else findRepeat site body
      | _, _ => none
    inner.orElse fun _ => findRepeat site next

end Zkc.Source.Structured.Bindings
