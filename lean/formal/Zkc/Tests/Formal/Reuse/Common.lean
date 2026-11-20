import Zkc.Tests.Formal.SourceProtocolRoots
import Zkc.Formal.Written.SumcheckRows

namespace Zkc.Tests.Formal.Reuse
open Core Frontend Formal.Interactive.Sumcheck ReductionRound
open SourcePairMembers (sourceRows)

abbrev events := SourceProtocolRoots.sourceEvents
abbrev vectors := SourceProtocolRoots.vectorRows

abbrev SumEndpoint (c : SourceProtocolRoots.ReadbackFixture) (red eval : Key) :=
  TableVerifier.Certified (sourceRows c.emission.bindings) (vectors c.emission.bindings)
    c.evidence.admitted.program ⟨c.id⟩ red eval 10 (events c.emission.bindings)

def implementation {V : Core.Vocabulary} (rows : ScalarRows V) (affine : Bool) (key : Key) :=
  if affine then rows.affineReadback key else rows.evaluationReadback key

abbrev gateRow := Zkc.Tools.Formal.gateRow

structure GateEndpoint (b : Zkc.Vocabulary.Project.Bindings) (p : Core.Typed b.vocabulary) (rootKey red site loopKey : Key)
    (args : List Name) where
  head : ProtocolHeader b.vocabulary
  root : Member p.headers.protocols head
  selected : head.key = rootKey
  state : b.vocabulary.Ty
  residual : b.vocabulary.Ty
  atCall : AtSite p root red site state (sourceRows b).scalarTy residual 0 4 (events b) args (loopRoute 4 loopKey 4 7)
  bound : b.vocabulary.row (.inr gateRow) = some (Gate.signature (sourceRows b))
  members : atCall.linked.rounds.AllMembers (fun op => Gate.Laws (sourceRows b) (.inr gateRow) bound
    atCall.linked.entry.definitions op)

def installGate {b : Zkc.Vocabulary.Project.Bindings} {p : Core.Typed b.vocabulary} {rootKey red site loopKey : Key}
    {args : List Name} {head : ProtocolHeader b.vocabulary} (root : Member p.headers.protocols head)
    (selected : head.key = rootKey) {state residual : b.vocabulary.Ty}
    (atCall : AtSite p root red site state (sourceRows b).scalarTy residual 0 4 (events b) args (loopRoute 4 loopKey 4 7)) :
    Option (GateEndpoint b p rootKey red site loopKey args) := do
  let gate ← Zkc.Formal.Written.SumcheckRows.checkGateMembers gateRow atCall.linked.entry.definitions
    (List.nodup_append.mp atCall.linked.entry.distinct).1 atCall.linked.rounds
  return ⟨head,root,selected,state,residual,atCall,gate.bound,gate.members⟩

/-- Pair the executable component theorem with the requested claim in the typed source. -/
structure SourceGate (c : SourceProtocolRoots.CheckedRoot) (red site loopKey : Key) (args : List Name)
    (claim : Emit.LocalApplication) where
  component : GateEndpoint c.emission.bindings c.evidence.admitted.program ⟨c.id⟩ red site loopKey args
  association : c.emission.externalApplicationAt? c.state ⟨c.id⟩ site red [0,1] "p" "Zkc.Circuit.summand" = some claim

def atSource {c : SourceProtocolRoots.CheckedRoot} {red site loopKey : Key} {args : List Name}
    (component : GateEndpoint c.emission.bindings c.evidence.admitted.program ⟨c.id⟩ red site loopKey args)
    (claim : Emit.LocalApplication) : Option (SourceGate c red site loopKey args claim) :=
  if associated : c.emission.externalApplicationAt? c.state ⟨c.id⟩ site red [0,1] "p" "Zkc.Circuit.summand" = some claim then
    some ⟨component,associated⟩
  else none

end Zkc.Tests.Formal.Reuse
