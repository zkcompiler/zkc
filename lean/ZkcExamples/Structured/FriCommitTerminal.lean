module

public import ZkcExamples.Structured.FriCommitAdmission
public import ZkcExamples.Structured.FriPhaseCalls
public meta import ZkcExamples.Structured.FriCommitRound
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback

@[expose] public section

/-! The terminal message is selected from the actual Commit continuation.
The layer sequences and the original geometry remain available across this
exchange. They are distinct SSA values even when their sorts agree. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCommitTerminal
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceViews FriSourceBodies FriCommitRound FriBinding
open OracleProtocol (concrete)

def delivery : Region.OperationCut roundNext :=
  (Region.cutFirst (d := protocolDialect) (fun op ↦ match op with | .exchange .. => true | _ => false) roundNext).get
    (by kernel_rfl)

set_option maxRecDepth 6000 in
checked_cut_suffix finish := delivery

def messageSite :=
  (match delivery.op with | .exchange _ 0 1 site => some site | _ => none).get (by kernel_rfl)

/-- The two handle sequences come from different ports of the returned
round state. Geometry and count come from the pre-round environment. -/
def layersPort : Var delivery.context layersSort.type := delivery.inherited (.there (.there .here))
def foldsPort : Var delivery.context layersSort.type := delivery.inherited (.there (.there (.there .here)))
def shiftPort : Var delivery.context (.field extension) :=
  delivery.inherited (FriCommitAdmission.shiftPort.weakenPrefix roundSite.spec.state)
def rowsPort : Var delivery.context .index :=
  delivery.inherited (FriCommitAdmission.sizePort.weakenPrefix roundSite.spec.state)
def countPort : Var delivery.context .index :=
  delivery.inherited (FriCommitAdmission.countPort.weakenPrefix roundSite.spec.state)

def output (model : DomainModel) (initial : OracleAnchor) (layers folds : List OracleAnchor)
    (shift : model.Field extension) (cs : List (model.Field extension)) :
    Values (Value model) protocol0Signature.outputs :=
  FriPhaseCalls.prependPairs (FriPhaseCalls.pairs none (concrete model initialSort.type initial)
    none (concrete model layersSort.type layers) none (concrete model layersSort.type folds))
    (.cons (concrete model (.field extension) shift) (.cons (concrete model .index 32)
      (.cons (concrete model (.vector extension) cs) (.cons (concrete model .index 3) .nil))))

end ZkcExamples.Structured.FriCommitTerminal
