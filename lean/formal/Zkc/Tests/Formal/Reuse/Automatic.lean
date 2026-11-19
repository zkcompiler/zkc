import Zkc.Tests.Formal.Reuse.Common

namespace Zkc.Tests.Formal.Reuse.Automatic
open Core Frontend Formal.Interactive.Sumcheck ReductionRound
open SourcePairMembers (sourceRows)

def sumcheck (c : SourceProtocolRoots.ReadbackFixture) (red eval : Key) (affine : Bool) : Option (SumEndpoint c red eval) :=
  let b := c.emission.bindings
  let rows := sourceRows b
  TableVerifier.certify rows (vectors b) c.evidence.admitted.program ⟨c.id⟩ red eval 10 (events b) (implementation rows affine)

def withLayerCall {α : Type} (c : SourceProtocolRoots.CheckedRoot) (red site : Key) (args : List Name) (loopKey : Key)
    (visit : ∀ {head : ProtocolHeader c.emission.bindings.vocabulary}
      (root : Member c.evidence.admitted.program.headers.protocols head), head.key = ⟨c.id⟩ →
      ∀ {st out}, AtSite c.evidence.admitted.program root red site st (sourceRows c.emission.bindings).scalarTy out
        0 4 (events c.emission.bindings) args (loopRoute 4 loopKey 4 7) → Option α) : Option α := do
  let p := c.evidence.admitted.program
  let b := c.emission.bindings
  let [⟨hdr,root⟩] := Member.withKey ProtocolHeader.key ⟨c.id⟩ p.headers.protocols | none
  if selected : hdr.key = ⟨c.id⟩ then
    let [⟨callee,_⟩] := Member.withKey ProtocolHeader.key red p.headers.protocols | none
    let [st,_,_] := callee.ins | none
    let [_,_,out] := callee.outs | none
    let found ← atSite p root red site st.ty (sourceRows b).scalarTy out.ty 0 4 (events b) args (loopRoute 4 loopKey 4 7)
    visit root selected found
  else none

def gkr (c : SourceProtocolRoots.CheckedRoot) (red site : Key) (args : List Name) (loopKey : Key) :
    Option (GateEndpoint c.emission.bindings c.evidence.admitted.program ⟨c.id⟩ red site loopKey args) :=
  withLayerCall c red site args loopKey fun {_} root selected {_ _} call => installGate root selected call

end Zkc.Tests.Formal.Reuse.Automatic
