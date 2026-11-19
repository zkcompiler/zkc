import Zkc.Frontend.Emit.Root

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend

structure CallerKeys where
  site : Key
  reduction : Key
  evaluator : Key

/-- Read the application site and both callees from the emitted caller. -/
def sumcheckCallKeys (e : Emit.RootEmission) (root : Key) : Option CallerKeys := do
  let .protocol _ _ _ _ (.mk _ [_,.op site _ (.apply red [0,1]) _,.op _ _ (.compute [1] (.call eval)) _,_,_] _) ←
    e.named.definitions.find? (·.key == root) | none
  return ⟨site,red,eval⟩

end Zkc.Tools.Formal
