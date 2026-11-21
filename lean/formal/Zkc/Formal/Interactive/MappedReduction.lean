module

public import Zkc.Core.Evidence.OperationSite
public import Zkc.Formal.Interactive.Application
public import Zkc.Formal.Interactive.LinkedReduction

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core

variable {V : Vocabulary} {p : Core.Typed V} {hdr : ProtocolHeader V}
variable {state t residual : V.Ty} {k n : Nat}

abbrev earlier {p : Core.Typed V} {hdr : ProtocolHeader V} {member : Member p.headers.protocols hdr}
    (entry : ProtocolEntry p.defs member) : Core.Typed V := ⟨entry.earlier,entry.definitions,entry.distinct⟩

/-- A caller may hold more information than the reduction's ports require. The actual
operand types and role assignment determine which values enter the callee experiment. -/
structure MappedReduction (root : Member p.headers.protocols hdr) (callee site : Key)
    (state t residual : V.Ty) (k n : Nat) (events : Events t)
    (observer : Role) (roles : List Role) (args : List Name) (route : List OperationSite.Move) where
  caller : ProtocolEntry p.defs root
  linked : Linked (earlier caller) callee state t residual k n events
  operands : List (LTy V)
  distinct : roles.Nodup
  covers : roles.length = 2
  fits : Fits operands ((inputs state (.seq t (some k)) t).map (LTy.map (RoleMap.ofList roles distinct).to))
  verifier : (RoleMap.ofList roles distinct).back observer = 1
  found : OperationSite.Contains (D := roleDialect V caller.earlier observer) site (RoleOp.apply linked.ref roles distinct covers operands fits)
    args route (project observer caller.body)

def mappedReduction (root : Member p.headers.protocols hdr) (callee site : Key)
    (state t residual : V.Ty) (k n : Nat) (events : Events t) (observer : Role) (roles : List Role)
    (args : List Name) (route : List OperationSite.Move) :
    Option (MappedReduction root callee site state t residual k n events observer roles args route) := do
  let caller := p.defs.protocolEntry p.distinct root
  let linked ← link (earlier caller) callee state t residual k n events
  let actual ← OperationSite.locate route (project observer caller.body)
  if distinct : roles.Nodup then do
    if covers : roles.length = 2 then do
      let ρ := RoleMap.ofList roles distinct
      letI := decideFits actual.ins ((inputs state (.seq t (some k)) t).map (LTy.map ρ.to))
      if fits : Fits actual.ins ((inputs state (.seq t (some k)) t).map (LTy.map ρ.to)) then do
        if verifier : ρ.back observer = 1 then do
          let ⟨found⟩ ← actual.check (BodyAnalysis.roleChecks observer)
            (BodyAnalysis.roleChecks_lawful (List.nodup_append.mp caller.distinct).1)
            site (.apply linked.ref roles distinct covers actual.ins fits) args
          return ⟨caller,linked,actual.ins,distinct,covers,fits,verifier,found⟩
        else none
      else none
    else none
  else none

variable {root : Member p.headers.protocols hdr} {callee site : Key} {events : Events t}
variable {observer : Role} {roles : List Role} {args : List Name} {route : List OperationSite.Move}

unseal Zkc.Core.roleMeaning

theorem reindexProbability {σ : Type} (M : Model V) (K : Experiment (RSig M) σ)
    {header : ProtocolHeader V} (run : (r : Role) → HList (RV M r) header.ins → Program M (HList (RV M r) header.outs))
    {r : Role} (same : r = 1) (vs : HList (RV M r) header.ins) (s : σ)
    (post : HList (RV M r) header.outs → σ → Bool) :
    K.probability (run r vs) s post =
      K.probability (run 1 (same ▸ vs)) s (fun out => post (same.symm ▸ out)) := by
  cases same
  rfl

/-- Apply the reduction at the caller's observation and service state. The caller relates its
actual arguments to the entry claim and its postcondition to a true returned residual. -/
theorem MappedReduction.soundFrom
    (call : MappedReduction root callee site state t residual k n events observer roles args route)
    (M : Model V) [DecidableEq (M.Val t)] (q : Claims (M.Val t)) (cost : Mass) (nonneg : 0 ≤ cost)
    {σ : Type} (K : Experiment (RSig M) σ) (path : List Frame) (s : σ)
    (vs : HList (RV M observer) call.operands) (hidden : RV M 1 ⟨state,[0]⟩)
    (point : List (M.Val t)) (claim : M.Val t) (x : q.State n) (wrong : claim ≠ q.value n x)
    (entered : (call.verifier ▸ enterAll M (RoleMap.ofList roles call.distinct) observer
      (fitAllRV M call.fits vs)) = publicArgs M hidden point claim)
    (post : HList (RV M observer) ((PointReturn.ports t residual (k+n)).map
      (LTy.map (RoleMap.ofList roles call.distinct).to)) → σ → Bool)
    (returned : ∀ out after, post (leaveAll M (RoleMap.ofList roles call.distinct) observer
      (call.verifier.symm ▸ out)) after = true → correctReturn M q x point.length out = true)
    (bounds : call.linked.rounds.BoundsFrom M (Defs.fnTable M call.linked.entry.definitions)
      (Defs.rTable M call.linked.entry.definitions) (K.renamePeers (RoleMap.ofList roles call.distinct).to)
      q cost (path ++ [.application site]) (initialEnv M hidden k point claim) s x) :
    K.probability (roleOp M observer (Defs.fnTable M call.caller.definitions)
      (Defs.rTable M call.caller.definitions) site
      (.apply call.linked.ref roles call.distinct call.covers call.operands call.fits) path vs) s post ≤
      (n : Mass) * cost := by
  rw [K.probability_application]
  let inner := path ++ [.application site]
  let service := K.renamePeers (RoleMap.ofList roles call.distinct).to
  let run := fun r => Defs.rTable M call.caller.definitions _ call.linked.ref r inner
  rw [reindexProbability (header := reduction callee state t residual k n call.linked.shape)
    M service run call.verifier, entered]
  apply Mass.le_trans _ (call.linked.soundFrom M q cost nonneg service inner s hidden point claim x wrong bounds)
  apply service.expect_mono
  intro out after _
  by_cases h : post (leaveAll M (RoleMap.ofList roles call.distinct) observer (call.verifier.symm ▸ out)) after
  · simp [h, returned out after h]
  · simp [h]

end Zkc.Formal.Interactive.Sumcheck.ReductionRound
