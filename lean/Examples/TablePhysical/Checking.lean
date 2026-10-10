import Examples.TablePhysical.Simulation
import Examples.TableProtocol.Optimization

/-! Check the actual typed physical region against the retained logical source.
Acceptance composes checked logical folding with independent choices at physical
preparation occurrences. Partial evaluations, guards and calls remain at their
logical occurrences. The original source continues to own phase admission.
-/

set_option autoImplicit false
namespace TablePhysical
open TableProtocol Zkc.Source Zkc.Realization

structure Checked (Γ : List Ty) (ty : Ty)
    (source : RawRegion Ty Protocol.Operation) (candidate : RawRegion Ty Operation) where
  logical : Region Protocol.language Γ ty
  physical : Region language Γ ty
  sourceDecoded : source.elaborate (language := Protocol.language) Γ ty = .ok logical
  targetDecoded : candidate.elaborate (language := language) Γ ty = .ok physical
  logicalEquivalence : Zkc.Compiler.RegionEquivalence Protocol.meaning logical (erase physical)

def check (Γ : List Ty) (ty : Ty)
    (source : RawRegion Ty Protocol.Operation) (candidate : RawRegion Ty Operation) :
    Except String (Checked Γ ty source candidate) :=
  match hs : source.elaborate (language := Protocol.language) Γ ty with
  | .error _ => .error "malformed-source"
  | .ok logical =>
    match ht : candidate.elaborate (language := language) Γ ty with
    | .error _ => .error "malformed-physical-region"
    | .ok physical =>
      match Optimization.folding.check logical (erase physical) with
      | some equivalent => .ok ⟨logical, physical, hs, ht, equivalent⟩
      | none => .error "physical-source-mismatch"

theorem Checked.correct {S E : Type}
    (logicalHandler : PIR.Handler Protocol.protocolInterface S E) {Γ : List Ty} {ty : Ty}
    {source : RawRegion Ty Protocol.Operation} {candidate : RawRegion Ty Operation}
    (accepted : Checked Γ ty source candidate)
    (actual : Region language Γ ty) (decoded : candidate.elaborate (language := language) Γ ty = .ok actual)
    (a : Environment TableProtocol.Value Γ) (b : Environment Value Γ)
    (s : S) (t : State S) (states : representation.states s t)
    (inputs : representation.Environments a s b t) :
    representation.Results (fun event => [event]) (fun event => [event]) s t
      ((accepted.logical.denote Protocol.meaning a).run logicalHandler s)
      ((actual.denote meaning b).run (handler logicalHandler) t) := by
  have same : accepted.physical = actual := Except.ok.inj (accepted.targetDecoded.symm.trans decoded)
  rw [← same, ← accepted.logicalEquivalence.denote a]
  exact TablePhysical.correct logicalHandler accepted.physical a b s t states inputs

/-- Source input values embed without allocating or demanding a prepared cell. -/
def inputs {Γ : List Ty} (env : Environment TableProtocol.Value Γ) : Environment Value Γ :=
  fun {ty} v => embed ty (env v)

theorem inputs_related {S : Type} {Γ : List Ty} (env : Environment TableProtocol.Value Γ)
    (s : S) (t : State S) : representation.Environments env s (inputs env) t :=
  fun ty v => decode_embed t.store ty (env v)

/-- A producer is intentionally outside the checker's proof. Its output is
decoded and checked independently, including dormant branches and loop bodies. -/
def propose (mode : Mode) : RawRegion Ty Protocol.Operation → RawRegion Ty Operation
  | .ret index => .ret index
  | .stop why => .stop why
  | .letOp op args next =>
    .letOp (match op with | .base (.evaluate d n) => .prepare mode d n | _ => .invoke op)
      args (propose mode next)
  | .branch condition yes no => .branch condition (propose mode yes) (propose mode no)
  | .iterate count ty initial body next => .iterate count ty initial (propose mode body) (propose mode next)
  | .bind ty body next => .bind ty (propose mode body) (propose mode next)

end TablePhysical
