import Zkc.Tests.Formal.SourceProtocolRoots

namespace Zkc.Tests.Formal.Reuse
open Core Frontend Formal.Interactive.Sumcheck ReductionRound
open SourcePairMembers (sourceRows)

abbrev events := SourceProtocolRoots.sourceEvents
abbrev vectors := SourceProtocolRoots.vectorRows

abbrev SumEndpoint (c : SourceProtocolRoots.CheckedRoot) (red eval : Key) :=
  TableVerifier.Certified (sourceRows c.emission.bindings) (vectors c.emission.bindings)
    c.evidence.admitted.program ⟨c.id⟩ red eval 10 (events c.emission.bindings)

def implementation {V : Core.Vocabulary} (rows : ScalarRows V) (affine : Bool) (key : Key) :=
  if affine then rows.affineReadback key else rows.evaluationReadback key

def gateRow := Emit.primitiveName ⟨"circuit.gate_evaluate", #[.type (StandardNames.fieldType .bls12381Fr)]⟩

structure GateEndpoint (b : Emit.Bindings) (p : Core.Typed b.vocabulary) (rootKey red site loopKey : Key)
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

def installGate {b : Emit.Bindings} {p : Core.Typed b.vocabulary} {rootKey red site loopKey : Key}
    {args : List Name} {head : ProtocolHeader b.vocabulary} (root : Member p.headers.protocols head)
    (selected : head.key = rootKey) {state residual : b.vocabulary.Ty}
    (atCall : AtSite p root red site state (sourceRows b).scalarTy residual 0 4 (events b) args (loopRoute 4 loopKey 4 7)) :
    Option (GateEndpoint b p rootKey red site loopKey args) := do
  let rows := sourceRows b
  if sig : b.signature gateRow = some ⟨[Gate.message rows,rows.scalarTy],[rows.scalarTy]⟩ then
    have bound : b.vocabulary.row (.inr gateRow) = some (Gate.signature rows) := by
      change ((b.signature gateRow).map _).map _ = _
      rw [sig]
      rfl
    let defs := atCall.linked.entry.definitions
    let ⟨members⟩ ← atCall.linked.rounds.checkMembers _ (Gate.check rows _ bound defs (List.nodup_append.mp atCall.linked.entry.distinct).1)
    return ⟨head,root,selected,state,residual,atCall,bound,members⟩
  else none

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
