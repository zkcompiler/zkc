import Zkc.Source.Mathematical.AdmissionWork
import Zkc.Source.Mathematical.Raw
import Zkc.Source.Mathematical.GraphAdmission
import Zkc.Source.Mathematical.FormationLimits

/-! Resolve a carrier region before intrinsic graph admission.

The declaration owner supplies certified operation and static selection. This
layer preserves every written field, including attributes and authored static
expressions, while replacing uses with the selected operation/count in the
graph core. It neither installs a registry nor accepts an authored purity flag
as an operation interpretation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.GraphResolution

structure OperationUse where
  operation : Raw.Reference .operation
  statics : List Static.Raw
  attributes : Raw.Attribute

inductive Error where
  | resource | depth
  | selection (reason : String)
  | graph (reason : Graph.Error)
  deriving Repr

/-- These relations belong to the declaration/registry owner. A resolver must
produce their witnesses; it cannot supply an unproved success flag. -/
structure Resolver (algebra : Graph.Algebra) where
  OperationValid : OperationUse → algebra.Op → Prop
  CountValid : Static.Raw → algebra.Count → Prop
  operation : (source : OperationUse) →
    StateT Nat (Except String) { op : algebra.Op // OperationValid source op }
  count : (source : Static.Raw) →
    StateT Nat (Except String) { count : algebra.Count // CountValid source count }

variable {algebra : Graph.Algebra}

mutual
  inductive Node (resolver : Resolver algebra) where
    | operation (source : OperationUse) (selected : algebra.Op)
        (valid : resolver.OperationValid source selected) (arguments : List (Raw.Reference .region))
    | tuple (elements : List (Raw.Reference .region))
    | project (value : Raw.Reference .region) (component : Nat)
    | map (source : Static.Raw) (count : algebra.Count) (valid : resolver.CountValid source count)
        (body : Region resolver)
    | fold (source : Static.Raw) (count : algebra.Count) (valid : resolver.CountValid source count)
        (initial : List (Raw.Reference .region)) (body : Region resolver)
  inductive Region (resolver : Resolver algebra) where
    | mk (captures : List (Raw.Reference .value)) (nodes : List (Node resolver))
        (outputs : List (Raw.Reference .region))
end

variable {resolver : Resolver algebra}

mutual
  def Node.erase : Node resolver → Raw.Node
    | .operation source _ _ arguments => .operation source.operation source.statics source.attributes arguments
    | .tuple elements => .tuple elements
    | .project value component => .project value component
    | .map source _ _ body => .map source body.erase
    | .fold source _ _ initial body => .fold source initial body.erase
  def Region.erase : Region resolver → Raw.Region
    | .mk captures nodes outputs => .mk captures (nodes.map Node.erase) outputs
end

def Region.captures : Region resolver → List Nat
  | .mk captures _ _ => captures.map (·.index)

mutual
  def Node.lower (next : Graph.Raw algebra.Op algebra.Count) : Node resolver → Graph.Raw algebra.Op algebra.Count
    | .operation _ op _ arguments => .operation op (arguments.map (·.index)) next
    | .tuple elements => .tuple (elements.map (·.index)) next
    | .project value component => .project value.index component next
    | .map _ count _ body => .map count body.captures body.lower next
    | .fold _ count _ initial body => .fold count (initial.map (·.index)) body.captures body.lower next
  def Region.lower : Region resolver → Graph.Raw algebra.Op algebra.Count
    | .mk _ nodes outputs => nodes.foldr (fun node next => node.lower next) (.outputs (outputs.map (·.index)))
end

private def consume (amount : Nat := 1) : StateT Nat (Except Error) Unit :=
  AdmissionWork.consume .resource amount

private def select {α : Type} (action : StateT Nat (Except String) α) : StateT Nat (Except Error) α :=
  AdmissionWork.checked .resource Error.selection action

mutual
  def node (resolver : Resolver algebra) (depth : Nat) (raw : Raw.Node) :
      StateT Nat (Except Error) { result : Node resolver // result.erase = raw } := do
    consume
    match hraw : raw with
    | .operation index statics attributes arguments =>
        let _ ← AdmissionWork.length .resource statics
        let _ ← AdmissionWork.length .resource arguments
        let selected ← select (resolver.operation ⟨index, statics, attributes⟩)
        return ⟨.operation ⟨index, statics, attributes⟩ selected.val selected.property arguments, by
          simp [Node.erase, hraw]⟩
    | .tuple elements =>
        let _ ← AdmissionWork.length .resource elements
        return ⟨.tuple elements, by simp [Node.erase, hraw]⟩
    | .project value component => return ⟨.project value component, by simp [Node.erase, hraw]⟩
    | .map count body =>
        let selected ← select (resolver.count count)
        let body ← region resolver (depth - 2) body
        return ⟨.map count selected.val selected.property body.val, by simp [Node.erase, body.property, hraw]⟩
    | .fold count initial body =>
        let _ ← AdmissionWork.length .resource initial
        let selected ← select (resolver.count count)
        let body ← region resolver (depth - 2) body
        return ⟨.fold count selected.val selected.property initial body.val, by simp [Node.erase, body.property, hraw]⟩
  termination_by sizeOf raw
  def nodes (resolver : Resolver algebra) (depth : Nat) (raw : List Raw.Node) :
      StateT Nat (Except Error) { result : List (Node resolver) // result.map Node.erase = raw } := do
    match hraw : raw with
    | [] => return ⟨[], by simp [hraw]⟩
    | first :: rest =>
        let first ← node resolver depth first
        let rest ← nodes resolver depth rest
        return ⟨first.val :: rest.val, by simp [first.property, rest.property, hraw]⟩
  termination_by sizeOf raw
  def region (resolver : Resolver algebra) : Nat → (raw : Raw.Region) →
      StateT Nat (Except Error) { result : Region resolver // result.erase = raw }
    | 0, _ => throw .depth
    | depth + 1, .mk captures body outputs => do
        consume
        let _ ← AdmissionWork.length .resource captures
        let _ ← AdmissionWork.length .resource outputs
        let body ← nodes resolver (depth + 1) body
        return ⟨.mk captures body.val outputs, by simp [Region.erase, body.property]⟩
  termination_by _ raw => sizeOf raw
end

variable {Role : Type} [DecidableEq Role]

structure Admitted (resolver : Resolver algebra) (parties : List Role)
    (Γ : List (Port Role algebra.Ty)) (raw : Raw.Region) where
  resolved : Region resolver
  erasure : resolved.erase = raw
  captured : Graph.SelectedOperands Γ resolved.captures
  graph : Graph.Decoded parties algebra captured.ports resolved.lower

def admit [DecidableEq algebra.Ty] (resolver : Resolver algebra) (parties : List Role)
    (capacity : Graph.Capacity algebra) (countValid : algebra.Count → Bool)
    (Γ : List (Port Role algebra.Ty)) (raw : Raw.Region) (budget : Nat := 1000000)
    (signatures : Graph.SignatureMeasurements capacity := fun _ => none) :
    Except Error (Admitted resolver parties Γ raw) := do
  let resolved ← (region resolver (FormationLimits.regionDepth + 1) raw).run' (min budget 1000000)
  let captured ← (Graph.selectOperands Γ resolved.val.captures).mapError Error.graph
  let graph ← (Graph.decode parties capacity countValid (FormationLimits.regionDepth + 1)
    captured.ports resolved.val.lower signatures).mapError Error.graph
  return ⟨resolved.val, resolved.property, captured, graph⟩

end Zkc.Source.Mathematical.GraphResolution
