module

public import ZkcExamples.Structured.FriBindingExecution
public import Zkc.Source.TypedABI

@[expose] public section

/-! The retained FRI callers transfer three logical pairs through their
ordinary source instructions. The helpers here name the admitted ABI fields
and preserve the mark, source coordinate, participant and child call frame. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriPhaseCalls
open Zkc.Source Zkc.Source.Structured
open FriSource FriBinding

variable {model : DomainModel}
abbrev Process (model : DomainModel) := PIR.Process (OracleProtocol.Interface model)

structure Caller where
  context : ProtocolContext

def Caller.mark (caller : Caller) (model : DomainModel) (site : String) : Process model Unit :=
  .call (.mark site (qualifyProtocolSite caller.context.applicationPrefix site)) .done

structure TransferSite where
  mark : String
  location : OracleLocation

/-- Select adjacent mark and registry operations in the caller's own
straight-line continuation. A callback cannot supply a caller's site. -/
def transferSites (select : OracleOp → Bool) : RawRegion Ty ProtocolOp → List TransferSite
  | .letOp (.mark mark) _ _ .nil (.letOp (.oracle op location) _ _ .nil next) =>
    if select op then ⟨mark, location⟩ :: transferSites select next else transferSites select next
  | .letOp _ _ _ _ next => transferSites select next
  | _ => []

def inputsOnly : OracleOp → Bool
  | .input .. => true
  | _ => false

def projectionsOnly : OracleOp → Bool
  | .components .. => true
  | _ => false

structure Transfers where
  initial : TransferSite
  layers : TransferSite
  folds : TransferSite

def oneTransferGroup : List TransferSite → Option Transfers
  | [a, b, c] => some ⟨a, b, c⟩
  | _ => none

def twoTransferGroups : List TransferSite → Option (Transfers × Transfers)
  | [a, b, c, d, e, f] => some (⟨a, b, c⟩, ⟨d, e, f⟩)
  | _ => none

def Caller.call (caller : Caller) (selected : CallSite)
    (args : Values (Value model) selected.signature.inputs) : Process model (Values (Value model) selected.signature.outputs) := do
  caller.mark model selected.site
  (verifierAlgebra model).application caller.context selected.signature selected.site
    (invokeProtocol (verifierTable model) selected.signature (selected.childContext caller.context) 1 args)

abbrev Pair (model : DomainModel) (sort : OracleLogicalSort) :=
  Values (Value model) [sort.dataType, sort.type]

structure Fields (F : OracleLogicalSort → Type) where
  initial : F initialSort
  layers : F layersSort
  folds : F layersSort

abbrev Pairs (model : DomainModel) := Fields (Pair model)
abbrev Handles (model : DomainModel) := Fields (fun sort ↦ Value model sort.type)

def pairs (a : Value model initialSort.dataType) (b : Value model initialSort.type)
    (c : Value model layersSort.dataType) (d : Value model layersSort.type)
    (e : Value model layersSort.dataType) (f : Value model layersSort.type) : Pairs model :=
  ⟨.cons a (.cons b .nil), .cons c (.cons d .nil), .cons e (.cons f .nil)⟩

/-- Use typed projections even for an opaque reply from a nested call. The
names at each use site follow the actual returned tuple in order. -/
abbrev fields {V : Ty → Type} {types : List Ty} {A : Type}
    (args : Values V types) (body : TypedABI.Curried V A types) : A :=
  TypedABI.apply body (Environment.toValues args.get)

def Caller.input (caller : Caller) (site : TransferSite) (sort : OracleLogicalSort) (pair : Pair model sort) :
    Process model (Value model sort.type) := do
  caller.mark model site.mark
  let out ← PIR.Process.call (.oracle ⟨.input sort 0 [1] [("rows", 32)], site.location, 1,
    caller.context.roles, pair⟩) .done
  return out.get .here

def Caller.project (caller : Caller) (site : TransferSite) (sort : OracleLogicalSort) (handle : Value model sort.type) :
    Process model (Pair model sort) := do
  caller.mark model site.mark
  PIR.Process.call (.oracle ⟨.components sort 0 [1], site.location, 1,
    caller.context.roles, .cons handle .nil⟩) .done

def Caller.inputs (caller : Caller) (sites : Transfers) (supplied : Pairs model) : Process model (Handles model) := do
  let a ← caller.input sites.initial initialSort supplied.initial
  let b ← caller.input sites.layers layersSort supplied.layers
  let c ← caller.input sites.folds layersSort supplied.folds
  return ⟨a, b, c⟩

def Caller.projections (caller : Caller) (sites : Transfers) (handles : Handles model) : Process model (Pairs model) := do
  let a ← caller.project sites.initial initialSort handles.initial
  let b ← caller.project sites.layers layersSort handles.layers
  let c ← caller.project sites.folds layersSort handles.folds
  return ⟨a, b, c⟩

def prependPairs {ts : List Ty} (projected : Pairs model) (tail : Values (Value model) ts) :
    Values (Value model) ([initialSort.dataType, initialSort.type, layersSort.dataType, layersSort.type,
      layersSort.dataType, layersSort.type] ++ ts) :=
  .cons (projected.initial.get .here) (.cons (projected.initial.get (.there .here))
    (.cons (projected.layers.get .here) (.cons (projected.layers.get (.there .here))
      (.cons (projected.folds.get .here) (.cons (projected.folds.get (.there .here)) tail)))))

end ZkcExamples.Structured.FriPhaseCalls
