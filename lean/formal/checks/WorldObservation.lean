module

import ZkcFormal.WorldObservation
import ZkcFormal.Written.FiniteModel
import Zkc.Core.Evidence.ProtocolReadback
meta import ZkcFormal.Written.FiniteModel
meta import Zkc.Core.Evidence.ProtocolReadback
meta import Zkc.Frontend.Written.Root
meta import Zkc.Frontend.Syntax.Parser

open Zkc.Core ZkcFormal.World

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
private def privateDraw {V : Vocabulary} (kind : GivenKind V) : Grant V := ⟨kind, 0, [], site, [], .bool⟩

example (kind : GivenKind V) (listeners : List Role) :
    (Access.fromGrants (· = privateDraw kind)).operation 0
      (ROp.own (M := M) kind listeners site [] .nil .bool) ↔ listeners = [] := by
  change (Grant.mk kind 0 listeners site [] .bool = Grant.mk kind 0 [] site [] .bool) ↔ _
  simp

example (kind : GivenKind V) :
    ¬ (Access.fromGrants (· = privateDraw kind)).operation 0
      (ROp.own (M := M) kind [] site [.bool] (.cons true .nil) .bool) := by
  change Grant.mk kind 0 [] site [.bool] .bool ≠ Grant.mk kind 0 [] site [] .bool
  simp

example (kind : GivenKind V) (source : Source M) {H B : Role → Type}
    {c c' : Net M H B × Pending M} {trace}
    (restricted : NetworkScoped (Access.fromGrants (· = privateDraw kind)) c.1)
    (run : Reach M source c trace c') (v : Bool) :
    Happened.heard 1 kind 0 site .bool v ∉ trace := by
  intro mem
  obtain ⟨listeners, _, same, hears⟩ := (reach_scoped restricted run).1 _ mem
  cases same
  exact List.not_mem_nil hears

end

section
open Zkc.Frontend ZkcFormal.Written

private def checkPrivateProjection (a : Admitted Standard) (root : Key) : Except String Unit := do
  let p := a.program
  let some ⟨shape, member⟩ := ProtocolEntry.locatePorts p.headers root 2 [] []
    | throw "missing two-role root"
  let M := FiniteModel.model
  let net := (Statements.projections p M member [] .nil).1
  let .call (.own kind [] at_ _ _ τ) _ := net 1 | throw "remapped owner must request the private coin"
  unless at_.site.through.length == 1 do throw "private coin must belong to the child application"
  let [⟨site, .given _ 1 [], _⟩] := shape.events [] id | throw "unexpected declared listeners"
  unless site == at_.site do throw "projected owner has a different site"
  -- Every honest continuation is authorized, independently of any candidate replacement.
  have _ := projections_scoped net
  have _ := @admitted_replacement_reads _ M (fun _ _ => none) a _ member [] .nil 1 (net 1)
    (projections_scoped net 1)
  match quiet : net 0 with
  | .done _ =>
    have denied : ¬ (Access.ofProjections net).hears 0 kind 1 at_ τ := by
      change ¬ Offers (net 0) _
      rw [quiet]
      exact id
    let impostor : Zkc.Core.Program M (HList (RV M 0) []) :=
      .call (.hear kind 1 at_ τ) (fun _ => .done .nil)
    have _ : ¬ Scoped (Access.ofProjections net) 0 impostor :=
      fun authorized => denied authorized.1
    return ()
  | _ => throw "the other role must finish without a source read"

#eval show IO Unit from do
  let text := "\n".intercalate ["module access", "protocol Child roles(A, B)():",
    "    coin @A <- sample bool", "protocol Outer roles(P, V)():",
    "    Child() @(A = V, B = P)", "scheme Private = Outer:", "    prover P",
    "    construction interactive", ""]
  let input : SourceInput := ⟨"access.zkc", Syntax.parseString "access.zkc" text⟩
  let state ← IO.ofExcept (Written.sourceState (← assemble #[input] fun _ => pure none))
  let some selected := state.results.schemes.find? (·.name == "Private") | throw (IO.userError "missing scheme")
  let root ← IO.ofExcept (Written.admitInstance state selected.protocol default)
  let run {b : Zkc.Vocabulary.Project.Bindings} (a : Admitted b.vocabulary) : Except String Unit := do
    match b, a with
    | ⟨[], _⟩, program => checkPrivateProjection program ⟨root.id⟩
    | _, _ => throw "unexpected external primitives"
  IO.ofExcept (run root.evidence.admitted)

end
