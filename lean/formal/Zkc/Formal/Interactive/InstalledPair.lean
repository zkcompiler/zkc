module

public import Zkc.Formal.Interactive.PairRound
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary} (rows : ScalarRows V) {hs : Headers V} (defs : Defs V hs)
variable (decode : ScalarRows.PairEncoding) (boundaryKey evaluationKey : Key)

/-- Check bodies against this installation once. Each round checks only its typed references. -/
structure InstalledPair where
  boundary : Member hs.fns (rows.scalarHeader boundaryKey [rows.pair])
  evaluate : Member hs.fns (rows.scalarHeader evaluationKey [rows.pair, rows.scalarTy])
  ends : rows.BoundaryLaw boundaryKey (fun M => Defs.fnTable M defs _ boundary) decode
  atPoint : rows.EvaluationLaw evaluationKey (fun M => Defs.fnTable M defs _ evaluate) decode

def installPair (unique : (hs.fns.map (·.key)).Nodup) (proof : rows.Companion decode) :
    Option (InstalledPair rows defs decode boundaryKey evaluationKey) := do
  let b ← FunctionEntry.resolve hs.fns (rows.scalarHeader boundaryKey [rows.pair])
  let e ← FunctionEntry.resolve hs.fns (rows.scalarHeader evaluationKey [rows.pair,rows.scalarTy])
  let ⟨ends⟩ ← proof.boundary defs unique (.call b)
  let ⟨atPoint⟩ ← proof.evaluate defs unique (.call e)
  return ⟨b,e,ends,atPoint⟩

variable {rows defs decode boundaryKey evaluationKey}

def InstalledPair.atMembers (proof : InstalledPair rows defs decode boundaryKey evaluationKey)
    (unique : (hs.fns.map (·.key)).Nodup) {msg st out : V.Ty} (ops : Members hs rows.scalarTy msg st out) :
    Option (PLift (PairLaws rows defs ops decode)) := do
  if same : msg = rows.pair then
    return ← show Option _ from by
      subst msg
      exact do
        let ⟨b⟩ ← ops.boundary.same? (.call proof.boundary) unique
        let ⟨e⟩ ← ops.evaluate.same? (.call proof.evaluate) unique
        return ⟨⟨rfl, fun M _ math m => b ▸ proof.ends M math m.1 m.2.1,
          fun M _ math m r => e ▸ proof.atPoint M math m.1 m.2.1 r⟩⟩
  else none

end Zkc.Formal.Interactive.Sumcheck.ReductionRound
