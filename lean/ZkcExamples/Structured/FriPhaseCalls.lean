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
  definition : Nat

def Caller.mark (caller : Caller) (model : DomainModel) (site : String) : Process model Unit :=
  .call (.mark site (qualifyProtocolSite caller.context.applicationPrefix site)) .done

def Caller.location (caller : Caller) (row : Nat) : OracleLocation :=
  ⟨⟨caller.definition, []⟩, caller.definition, [7, 1, row]⟩

def Caller.call (caller : Caller) (signature : ProtocolSignature) (site : String)
    (args : Values (Value model) signature.inputs) : Process model (Values (Value model) signature.outputs) := do
  caller.mark model site
  (verifierAlgebra model).application caller.context signature site
    (invokeProtocol (verifierTable model) signature (caller.context.enter site [0, 1]) 1 args)

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

def Caller.input (caller : Caller) (row : Nat) (sort : OracleLogicalSort) (pair : Pair model sort) :
    Process model (Value model sort.type) := do
  caller.mark model ""
  let out ← PIR.Process.call (.oracle ⟨.input sort 0 [1] [("rows", 32)], caller.location row, 1,
    caller.context.roles, pair⟩) .done
  return out.get .here

def Caller.project (caller : Caller) (row : Nat) (sort : OracleLogicalSort) (handle : Value model sort.type) :
    Process model (Pair model sort) := do
  caller.mark model ""
  PIR.Process.call (.oracle ⟨.components sort 0 [1], caller.location row, 1,
    caller.context.roles, .cons handle .nil⟩) .done

def Caller.inputs (caller : Caller) (row : Nat) (supplied : Pairs model) : Process model (Handles model) := do
  let a ← caller.input row initialSort supplied.initial
  let b ← caller.input (row + 1) layersSort supplied.layers
  let c ← caller.input (row + 2) layersSort supplied.folds
  return ⟨a, b, c⟩

def Caller.projections (caller : Caller) (row : Nat) (handles : Handles model) : Process model (Pairs model) := do
  let a ← caller.project row initialSort handles.initial
  let b ← caller.project (row + 1) layersSort handles.layers
  let c ← caller.project (row + 2) layersSort handles.folds
  return ⟨a, b, c⟩

def prependPairs {ts : List Ty} (projected : Pairs model) (tail : Values (Value model) ts) :
    Values (Value model) ([initialSort.dataType, initialSort.type, layersSort.dataType, layersSort.type,
      layersSort.dataType, layersSort.type] ++ ts) :=
  .cons (projected.initial.get .here) (.cons (projected.initial.get (.there .here))
    (.cons (projected.layers.get .here) (.cons (projected.layers.get (.there .here))
      (.cons (projected.folds.get .here) (.cons (projected.folds.get (.there .here)) tail)))))

end ZkcExamples.Structured.FriPhaseCalls
