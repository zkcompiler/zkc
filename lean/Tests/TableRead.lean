module

public import Zkc.Realization.TableRead

@[expose] public section

namespace Tests.TableRead
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization.TableRead

/-- Success uses the same theorem under any caller frame and field carrier. -/
noncomputable def placed (model : DomainModel) (domain : String)
    (caller : Domain.Environment model.toCarriers) (first second : model.Field domain) :
    let environment := caller ++ [.data ⟨.vector domain, rfl, [first, second]⟩,
      .data (.index 2), .data (.index 1)]
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ [.data (.boolean true), .data ⟨.field domain, rfl, second⟩]))
      ((spine domain ⟨caller.length + 3, caller.length, caller.length + 1,
        caller.length + 2, "read"⟩).block model environment) := by
  have result := simulation model domain
    (caller ++ [.data ⟨.vector domain, rfl, [first, second]⟩, .data (.index 2), .data (.index 1)])
    caller.length (caller.length + 1) (caller.length + 2) "read" [first, second] 2 1
    (by simp) (by simp) (by simp)
  simpa [read_eq, indexLimit, PIR.Process.interpret, PIR.Process.bind] using result

example : (recognize (instructions "field" ⟨9, 2, 4, 5, "read"⟩)).isSome = true := by decide +kernel

/-- Guarding one index cannot authorize a read at a different index. -/
example : (recognize ((instructions "field" ⟨3, 0, 1, 2, "read"⟩).set 2
    ⟨.calculate (.boundedAt "field"), [0, 1], [.data (.field "field")], []⟩)).isSome = false := by
  decide +kernel

/-- A caller boolean cannot replace the generated range comparison. -/
example : (recognizeAt 3 ((instructions "field" ⟨3, 0, 1, 2, "read"⟩).set 1
    ⟨.require "read", [0], [], []⟩)).isSome = false := by decide +kernel

def run (model : DomainModel) (domain : String) (program : Program) (context : Context)
    (cells : List (model.Field domain)) (rows position : Nat) :=
  (Domain.evaluate model program context (instructions domain ⟨3, 0, 1, 2, "read"⟩)
    [.data ⟨.vector domain, rfl, cells⟩, .data (.index rows), .data (.index position)]).interpret
      Original.forgetCheckpoints

/-- An extra physical cell does not extend the declared logical table. -/
theorem outside_refused (model : DomainModel) (domain : String) (program : Program)
    (context : Context) (first second : model.Field domain) :
    run model domain program context [first, second] 1 1 = .halt .refused := by
  unfold run
  rw [correspondence]
  rfl

/-- Finite-index ingress remains checked even when the requested cell exists. -/
theorem oversized_rows_refused (model : DomainModel) (domain : String) (program : Program)
    (context : Context) (value : model.Field domain) :
    run model domain program context [value] indexLimit 0 = .halt .refused := by
  unfold run
  rw [correspondence]
  rfl

/-- A declared bound cannot manufacture a missing stored cell. -/
theorem truncated_refused (model : DomainModel) (domain : String) (program : Program)
    (context : Context) (value : model.Field domain) :
    run model domain program context [value] 2 1 = .halt .refused := by
  have actual := simulation model domain
    [.data ⟨.vector domain, rfl, [value]⟩, .data (.index 2), .data (.index 1)]
    0 1 2 "read" [value] 2 1 rfl rfl rfl
  unfold run
  rw [correspondence]
  simpa [read_eq, indexLimit, PIR.Process.interpret, PIR.Process.bind] using actual.forget

#print axioms placed
#print axioms truncated_refused
#print axioms Zkc.Realization.TableRead.simulation
end Tests.TableRead
