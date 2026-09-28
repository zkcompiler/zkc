import Zkc.Source.Context
import Zkc.Source.Mathematical.FormationLimits

/-! Explicit structural capacity for an admission consumer. The semantic type
algebra remains independent of these finite consumer limits. Cached sizes are
certified against the supplied mathematical size functions; they do not bound
leaf-payload comparisons or arbitrary installed callback work.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical

structure TypeSize where
  nodes : Nat
  height : Nat
  deriving DecidableEq, Repr

def TypeSize.Within (size : TypeSize) : Prop :=
  size.nodes ≤ FormationLimits.typeNodes ∧ size.height ≤ FormationLimits.typeDepth + 1

instance (size : TypeSize) : Decidable size.Within := inferInstanceAs (Decidable (_ ∧ _))

structure TypeMeasurement {Ty : Type} (nodes height : Ty → Nat) (ty : Ty) where
  size : TypeSize
  nodes_eq : size.nodes = nodes ty
  height_eq : size.height = height ty
  within : size.Within

/-- Exact root measurements are mathematically unique even though their
counters are retained at runtime. Decomposition certificates need not be. -/
instance {Ty : Type} {nodes height : Ty → Nat} {ty : Ty} :
    Subsingleton (TypeMeasurement nodes height ty) where
  allEq first second := by
    cases first with
    | mk first firstNodes firstHeight firstBound =>
      cases second with
      | mk second secondNodes secondHeight secondBound =>
        cases first with
        | mk firstNodesValue firstHeightValue =>
          cases second with
          | mk secondNodesValue secondHeightValue =>
            have sameNodes := firstNodes.trans secondNodes.symm
            have sameHeight := firstHeight.trans secondHeight.symm
            simp only at sameNodes sameHeight
            cases sameNodes
            cases sameHeight
            rfl

/-- Root measurements can travel with a selected signature without making
decomposition strategy part of the operation's identity. -/
structure SignatureMeasurement {Ty : Type} (nodes height : Ty → Nat)
    (arguments : List Ty) (result : Ty) where
  inputs : Values (TypeMeasurement nodes height) arguments
  output : TypeMeasurement nodes height result

instance {Ty : Type} {nodes height : Ty → Nat} {arguments : List Ty} {result : Ty} :
    Subsingleton (SignatureMeasurement nodes height arguments result) where
  allEq first second := by
    cases first with
    | mk inputs output =>
      cases second with
      | mk otherInputs otherOutput =>
        cases Subsingleton.elim inputs otherInputs
        cases Subsingleton.elim output otherOutput
        rfl

/-- A product view supplies certified children. The consumer owns the cost of
obtaining this view; selection then reuses the chosen certificate. -/
structure CertifiedProductView {Ty : Type} (product : List Ty → Ty)
    (Certificate : Ty → Type) (type : Ty) where
  types : List Ty
  sound : type = product types
  child : {ty : Ty} → Var types ty → Certificate ty

/-- Consumer certificates carry structural measurements and any reusable
decomposition needed by admission. The semantic type algebra stays separate. -/
structure TypeCapacity (Ty Count : Type) (product : List Ty → Ty) (vector : Ty → Count → Ty) where
  nodes : Ty → Nat
  height : Ty → Nat
  product_nodes : ∀ types, nodes (product types) = 1 + (types.map nodes).sum
  product_height : ∀ types, height (product types) = 1 + (types.map height).foldr max 0
  vector_nodes : ∀ type count, nodes (vector type count) = 1 + nodes type
  vector_height : ∀ type count, height (vector type count) = 1 + height type
  Certificate : Ty → Type
  measurement : {type : Ty} → Certificate type → TypeMeasurement nodes height type
  boundary : {type : Ty} → TypeMeasurement nodes height type → Certificate type
  productCertificate : {types : List Ty} → TypeMeasurement nodes height (product types) →
    Values Certificate types → Certificate (product types)
  vectorCertificate : {type : Ty} → (count : Count) →
    TypeMeasurement nodes height (vector type count) → Certificate type → Certificate (vector type count)
  view : {type : Ty} → Certificate type → Option (CertifiedProductView product Certificate type)
  measure : (type : Ty) → Option (Certificate type)

namespace TypeCapacity
variable {Ty Count : Type} {product : List Ty → Ty} {vector : Ty → Count → Ty}
  (capacity : TypeCapacity Ty Count product vector)

abbrev Measured (type : Ty) := capacity.Certificate type

abbrev SignatureMeasurement (arguments : List Ty) (result : Ty) :=
  Zkc.Source.Mathematical.SignatureMeasurement capacity.nodes capacity.height arguments result

/-- Additional laws for completeness arguments. Sound typed formation needs
the certificates themselves; a consumer that deliberately refuses more inputs
need not satisfy these completeness laws. -/
structure Lawful : Prop where
  measurement_boundary : ∀ {type} (measured : TypeMeasurement capacity.nodes capacity.height type),
    capacity.measurement (capacity.boundary measured) = measured
  measurement_product : ∀ {types} measured (children : Values capacity.Certificate types),
    capacity.measurement (capacity.productCertificate measured children) = measured
  measurement_vector : ∀ {type} count measured (child : capacity.Certificate type),
    capacity.measurement (capacity.vectorCertificate count measured child) = measured
  view_product : ∀ {types} measured (children : Values capacity.Certificate types),
    capacity.view (capacity.productCertificate measured children) = some ⟨types, rfl, fun selected => children.get selected⟩
  view_complete : ∀ {types} (certificate : capacity.Certificate (product types)),
    ∃ view, capacity.view certificate = some view ∧ view.types = types
  measure_complete : ∀ type,
    capacity.nodes type ≤ FormationLimits.typeNodes → capacity.height type ≤ FormationLimits.typeDepth + 1 →
    (capacity.measure type).isSome = true

structure MeasuredList (types : List Ty) where
  size : TypeSize
  nodes_eq : size.nodes = (types.map capacity.nodes).sum
  height_eq : size.height = (types.map capacity.height).foldr max 0
  within : size.Within

/-- Running counters for a cached child list. Only `size` has runtime content;
the original and remaining type lists occur in erased accounting equations. -/
structure AggregationState (pending all : List Ty) where
  size : TypeSize
  nodes_eq : size.nodes + (pending.map capacity.nodes).sum = (all.map capacity.nodes).sum
  height_eq : max size.height ((pending.map capacity.height).foldr max 0) =
    (all.map capacity.height).foldr max 0
  within : size.Within

def AggregationState.start (types : List Ty) : AggregationState capacity types types :=
  ⟨⟨0, 0⟩, Nat.zero_add _, Nat.zero_max _, by simp [TypeSize.Within]⟩

def AggregationState.advance {first : Ty} {rest all : List Ty}
    (state : AggregationState capacity (first :: rest) all) (child : capacity.Measured first) :
    Option (AggregationState capacity rest all) :=
  let measured := capacity.measurement child
  let size : TypeSize :=
    ⟨state.size.nodes + measured.size.nodes, max state.size.height measured.size.height⟩
  if bounded : size.Within then
    some ⟨size,
      by simpa [size, measured.nodes_eq, Nat.add_assoc] using state.nodes_eq,
      by simpa [size, measured.height_eq, Nat.max_assoc] using state.height_eq, bounded⟩
  else none

def AggregationState.finish {all : List Ty} (state : AggregationState capacity [] all) :
    MeasuredList capacity all :=
  ⟨state.size, by simpa using state.nodes_eq, by simpa using state.height_eq, state.within⟩

def aggregateLoop {pending all : List Ty} (children : Values capacity.Measured pending)
    (state : AggregationState capacity pending all) : Option (MeasuredList capacity all) :=
  match children with
  | .nil => some (state.finish capacity)
  | .cons first rest => do
      let state ← state.advance capacity first
      aggregateLoop rest state

/-- Combine cached child sizes, counting every occurrence. Each prefix is
checked before continuing; no child structure is traversed again, and sibling
elements do not consume recursive stack space. -/
def aggregate {types : List Ty} (children : Values capacity.Measured types) :
    Option (MeasuredList capacity types) :=
  capacity.aggregateLoop children (AggregationState.start capacity types)

theorem AggregationState.advance_complete {first : Ty} {rest all : List Ty}
    (state : AggregationState capacity (first :: rest) all) (child : capacity.Measured first)
    (bounded : (TypeSize.mk ((all.map capacity.nodes).sum)
      ((all.map capacity.height).foldr max 0)).Within) :
    (state.advance capacity child).isSome = true := by
  have nodes := state.nodes_eq
  have height := state.height_eq
  have childNodes := (capacity.measurement child).nodes_eq
  have childHeight := (capacity.measurement child).height_eq
  simp only [List.map_cons, List.sum_cons, List.foldr_cons] at nodes height
  have prefixBound : (TypeSize.mk (state.size.nodes + (capacity.measurement child).size.nodes)
      (max state.size.height (capacity.measurement child).size.height)).Within := by
    rcases bounded with ⟨nodeBound, heightBound⟩
    constructor <;> dsimp at * <;> omega
  simp [AggregationState.advance, prefixBound]

theorem aggregateLoop_complete {pending all : List Ty} (children : Values capacity.Measured pending)
    (state : AggregationState capacity pending all)
    (bounded : (TypeSize.mk ((all.map capacity.nodes).sum)
      ((all.map capacity.height).foldr max 0)).Within) :
    (capacity.aggregateLoop children state).isSome = true := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      have accepted := state.advance_complete capacity first bounded
      cases found : state.advance capacity first with
      | none => simp [found] at accepted
      | some next => simpa [aggregateLoop, found] using ih next

theorem aggregate_iff {types : List Ty} (children : Values capacity.Measured types) :
    (capacity.aggregate children).isSome = true ↔
      (TypeSize.mk ((types.map capacity.nodes).sum) ((types.map capacity.height).foldr max 0)).Within := by
  constructor
  · intro accepted
    cases found : capacity.aggregate children with
    | none => simp [found] at accepted
    | some measured => simpa [TypeSize.Within, measured.nodes_eq, measured.height_eq] using measured.within
  · intro bounded
    exact capacity.aggregateLoop_complete children (AggregationState.start capacity types) bounded

def measureProduct {types : List Ty} (children : Values capacity.Measured types) :
    Option (capacity.Measured (product types)) := do
  let combined ← capacity.aggregate children
  let size : TypeSize := ⟨1 + combined.size.nodes, 1 + combined.size.height⟩
  if bounded : size.Within then
    return capacity.productCertificate
      ⟨size, by simp [size, capacity.product_nodes, combined.nodes_eq],
        by simp [size, capacity.product_height, combined.height_eq], bounded⟩ children
  else none

theorem measureProduct_iff {types : List Ty} (children : Values capacity.Measured types) :
    (capacity.measureProduct children).isSome = true ↔
      (TypeSize.mk (capacity.nodes (product types)) (capacity.height (product types))).Within := by
  constructor
  · intro accepted
    obtain ⟨certificate, _⟩ := Option.isSome_iff_exists.mp accepted
    have measured := (capacity.measurement certificate).within
    simpa [TypeSize.Within, (capacity.measurement certificate).nodes_eq,
      (capacity.measurement certificate).height_eq] using measured
  · intro bounded
    have combinedBound : (TypeSize.mk ((types.map capacity.nodes).sum)
        ((types.map capacity.height).foldr max 0)).Within := by
      rcases bounded with ⟨nodes, height⟩
      simp only [capacity.product_nodes, capacity.product_height] at nodes height
      constructor <;> dsimp at * <;> omega
    have accepted := (capacity.aggregate_iff children).mpr combinedBound
    cases found : capacity.aggregate children with
    | none => simp [found] at accepted
    | some combined =>
      have fits : (TypeSize.mk (1 + combined.size.nodes) (1 + combined.size.height)).Within := by
        simpa [capacity.product_nodes, capacity.product_height, combined.nodes_eq, combined.height_eq] using bounded
      simp [measureProduct, found, fits]

def measureVector {type : Ty} (child : capacity.Measured type) (count : Count) :
    Option (capacity.Measured (vector type count)) :=
  let measured := capacity.measurement child
  let size : TypeSize := ⟨1 + measured.size.nodes, 1 + measured.size.height⟩
  if bounded : size.Within then
    some (capacity.vectorCertificate count
      ⟨size, by simp [size, capacity.vector_nodes, measured.nodes_eq],
        by simp [size, capacity.vector_height, measured.height_eq], bounded⟩ child)
  else none

def measureTypes (types : List Ty) : Option (Values capacity.Measured types) :=
  Values.ofList? capacity.measure types

theorem measureTypes_iff (types : List Ty) :
    (capacity.measureTypes types).isSome = true ↔
      ∀ type ∈ types, (capacity.measure type).isSome = true :=
  Values.ofList?_isSome_iff capacity.measure types

theorem measureTypes_complete (lawful : capacity.Lawful) (types : List Ty)
    (bounded : ∀ type ∈ types,
      capacity.nodes type ≤ FormationLimits.typeNodes ∧ capacity.height type ≤ FormationLimits.typeDepth + 1) :
    (capacity.measureTypes types).isSome = true :=
  (capacity.measureTypes_iff types).mpr fun type member =>
    lawful.measure_complete type (bounded type member).1 (bounded type member).2

/-- Use a previously admitted signature's counters, or measure a generic
caller's signature at the boundary. Retained input measurements certify boundedness; the fallback checks inputs to preserve the generic refusal behavior. -/
def measureSignatureResult (arguments : List Ty) (result : Ty)
    (known : Option (capacity.SignatureMeasurement arguments result)) : Option (capacity.Measured result) :=
  match known with
  | some measured => some (capacity.boundary measured.output)
  | none => do
      let _ ← capacity.measureTypes arguments
      capacity.measure result

end TypeCapacity
end Zkc.Source.Mathematical
