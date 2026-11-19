module

public import Zkc.Frontend.Constructed.Execution
public import Zkc.Formal.ProbabilisticProcess
public import VCVio.OracleComp.QueryTracking.ListCache
public import VCVio.OracleComp.EvalDist

@[expose] public section

namespace Zkc.Tools.Formal.ConstructedVerifier
open Core Frontend.Constructed Zkc.Formal.ProbabilisticProcess
open OracleComp OracleSpec

variable {assembly : Frontend.Assembly} {request : ExecutionRequest}

/-- Message policies may fail or update their state. The observer explicitly decides
what query information the policy for subsequent messages can use. -/
structure Policy (M : Model V) (σ : Type) (m : Type → Type) where
  commitment : Occurrence → σ → m (Option (M.Val point) × σ)
  response : Occurrence → σ → m (Option (M.Val scalar) × σ)
  observe : Query → Units → σ → σ

abbrev Cache := List (Query × Units)

/-- Cache the full framed query with VCVio's list-cache handler. The draw on a miss
is supplied by the experiment. Hits still notify the observer. -/
def serve {M : Model V} {σ : Type} {m : Type → Type} [Monad m]
    (policy : Policy M σ m) (draw : Query → m Units) :
    (op : Input M) → Cache × σ → m (Option ((signature M).Reply op) × Cache × σ)
  | .commitment at_, (cache,s) => do
    let (x,s') ← policy.commitment at_ s
    return (x,cache,s')
  | .response at_, (cache,s) => do
    let (x,s') ← policy.response at_ s
    return (x,cache,s')
  | .squeeze q, (cache,s) => do
    let (units,cache') ← QueryImpl.ListCache.handler draw q cache
    return (some units,cache',policy.observe q units s)

/-- An experiment on the constructed verifier. Acceptance means its admitted guard
returned. The complete initial cache, message policies and squeeze law belong to the
caller. This defines an event probability and imposes no security bound on it. -/
noncomputable def acceptance {M : Model V} {σ : Type} (v : Verifier assembly request) (i : Interpretation M)
    (identity : Identity) (inputs : HList (RV M v.verifier) v.deployment.entry.ins)
    (policy : Policy M σ ProbComp) (draw : Query → ProbComp Units) (initial : Cache × σ) :=
  (v.run i identity inputs).map fun process =>
    let event := fun (result : Outcome Stop _ × Cache × σ) =>
      match result.1 with | .returned _ => True | .halted _ | .unavailable => False
    prEvent (event <$> run (serve policy draw) process initial)

end Zkc.Tools.Formal.ConstructedVerifier
