module

import Zkc.Formal.WorldObservation

open Zkc.Core Zkc.Formal.World

section
variable {V : Vocabulary} (M : Model V)
private abbrev site : Occurrence := ⟨[], ⟨0⟩⟩

private def request (argument : Bool) : GOp M :=
  .given (.request ⟨0⟩) 0 [1] site [.bool] (.cons argument .nil) .bool

private def entry (argument : Bool) : (op : GOp M) × (GSig M).Reply op := ⟨request M argument, true⟩

private def payload : ((op : GOp M) × (GSig M).Reply op) → Bool
  | ⟨.given _ _ _ _ [.bool] (.cons x .nil) _, _⟩ => x
  | _ => false

-- The same reply can conceal different requests. The owner sees them and the listener
-- receives exactly the reply. A stateful service can distinguish the two requests.
example : entry M false ≠ entry M true := fun same => Bool.noConfusion (congrArg (payload M) same)
example : forgetPayload (entry M false) = forgetPayload (entry M true) := rfl
example : roleEntry 1 (entry M false) = roleEntry 1 (entry M true) := rfl
example : roleEntry 2 (entry M true) = none := rfl

private def remembers : Service M Bool := fun _ op v next => next = payload M ⟨op,v⟩

example (argument : Bool) : Observed (remembers M) false
    (.call (request M argument) (fun _ => .done ())) [entry M argument] (.returned ()) argument :=
  .call rfl .done

-- An unlisted role cannot read a private source entry in any reachable scoped network.
private def privateDraw {V : Vocabulary} (kind : GivenKind V) : Grant V := ⟨kind, 0, [], site, .bool⟩

example (kind : GivenKind V) (source : Source M) {H B : Role → Type}
    {c c' : Net M H B × Pending M} {trace}
    (restricted : NetworkScoped (Access.fromGrants (· = privateDraw kind)) c.1)
    (run : Reach M source c trace c') (v : Bool) :
    Happened.heard 1 kind 0 site .bool v ∉ trace := by
  intro mem
  obtain ⟨listeners, same, hears⟩ := (reach_scoped restricted run).1 _ mem
  cases same
  exact List.not_mem_nil hears

end
