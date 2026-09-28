import Zkc.Source.Mathematical.Data
import Zkc.Source.Mathematical.TypeCapacity

/-! Bounded measurement of expanded structural types.

Repeated children count repeatedly, including when the runtime shares them.
Vector lengths remain symbolic and are never unrolled. The mathematical size
and height functions occur in certificates; admission uses the bounded walk.
Leaf payloads (nominal names and static expressions) have separate costs.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Data
variable {Atom Count : Type}

mutual
  def Shape.nodes : Shape Atom Count → Nat
    | .atom _ | .fin _ => 1
    | .product elements => 1 + shapesNodes elements
    | .vector element _ => 1 + element.nodes
  def shapesNodes : List (Shape Atom Count) → Nat
    | [] => 0
    | first :: rest => first.nodes + shapesNodes rest
end

mutual
  def Shape.height : Shape Atom Count → Nat
    | .atom _ | .fin _ => 1
    | .product elements => 1 + shapesHeight elements
    | .vector element _ => 1 + element.height
  def shapesHeight : List (Shape Atom Count) → Nat
    | [] => 0
    | first :: rest => max first.height (shapesHeight rest)
end

/-- Residual budget and the computed height, certified without reevaluating
an unbounded mathematical size function at runtime. -/
structure WalkResult {Subject : Type} (nodes height : Subject → Nat)
    (subject : Subject) (depth budget : Nat) where
  remaining : Nat
  measuredHeight : Nat
  nodes_eq : remaining + nodes subject = budget
  height_eq : measuredHeight = height subject
  height_le : measuredHeight ≤ depth

/-- A list walk keeps only its remaining allowance and running maximum.
The original node/height accounting is proof data, erased at runtime. -/
structure MeasurementState (shapes all : List (Shape Atom Count)) (depth budget : Nat) where
  remaining : Nat
  seenHeight : Nat
  nodes_eq : remaining + shapesNodes all = budget + shapesNodes shapes
  height_eq : max seenHeight (shapesHeight shapes) = shapesHeight all
  height_le : seenHeight ≤ depth

def MeasurementState.start (shapes : List (Shape Atom Count)) (depth budget : Nat) :
    MeasurementState shapes shapes depth budget :=
  ⟨budget, 0, rfl, Nat.zero_max _, Nat.zero_le _⟩

def MeasurementState.advance {first : Shape Atom Count} {rest : List (Shape Atom Count)}
    {all : List (Shape Atom Count)} {depth budget : Nat}
    (state : MeasurementState (first :: rest) all depth budget)
    (head : WalkResult Shape.nodes Shape.height first depth state.remaining) :
    MeasurementState rest all depth budget :=
  ⟨head.remaining, max state.seenHeight head.measuredHeight,
    by have := state.nodes_eq; have := head.nodes_eq; simp only [shapesNodes] at *; omega,
    by rw [head.height_eq, Nat.max_assoc]; exact state.height_eq,
    Nat.max_le.mpr ⟨state.height_le, head.height_le⟩⟩

def MeasurementState.finish {all : List (Shape Atom Count)} {depth budget : Nat}
    (state : MeasurementState [] all depth budget) :
    WalkResult shapesNodes shapesHeight all depth budget :=
  ⟨state.remaining, state.seenHeight, by simpa [shapesNodes] using state.nodes_eq,
    by simpa [shapesHeight] using state.height_eq, state.height_le⟩

mutual
  /-- Visits at most `budget` type constructors. Height uses one for a leaf. -/
  def Shape.measure : (depth budget : Nat) → (shape : Shape Atom Count) →
      Option (WalkResult Shape.nodes Shape.height shape depth budget)
    | 0, _, _ => none
    | _ + 1, 0, _ => none
    | depth + 1, budget + 1, .atom _ => some ⟨budget, 1, rfl, rfl, by omega⟩
    | depth + 1, budget + 1, .fin _ => some ⟨budget, 1, rfl, rfl, by omega⟩
    | depth + 1, budget + 1, .product elements => do
        let result ← measureShapesLoop depth elements (MeasurementState.start elements depth budget)
        return ⟨result.remaining, 1 + result.measuredHeight,
          by simp only [Shape.nodes]; have := result.nodes_eq; omega,
          by simp [Shape.height, result.height_eq], by have := result.height_le; omega⟩
    | depth + 1, budget + 1, .vector element _ => do
        let result ← element.measure depth budget
        return ⟨result.remaining, 1 + result.measuredHeight,
          by simp only [Shape.nodes]; have := result.nodes_eq; omega,
          by simp [Shape.height, result.height_eq], by have := result.height_le; omega⟩
  termination_by structural _ _ shape => shape

  /-- A tail call handles the remaining siblings. Only nested type constructors
  use recursive stack depth; a wide product does not keep a frame per child. -/
  def measureShapesLoop (depth : Nat) : (shapes : List (Shape Atom Count)) →
      {all : List (Shape Atom Count)} → {budget : Nat} → MeasurementState shapes all depth budget →
      Option (WalkResult shapesNodes shapesHeight all depth budget)
    | [], _, _, state => some state.finish
    | first :: rest, _, _, state => do
        let head ← first.measure depth state.remaining
        measureShapesLoop depth rest (state.advance head)
  termination_by structural shapes _ _ _ => shapes
end

def measureShapes (depth budget : Nat) (shapes : List (Shape Atom Count)) :
    Option (WalkResult shapesNodes shapesHeight shapes depth budget) :=
  measureShapesLoop depth shapes (MeasurementState.start shapes depth budget)

mutual
  theorem Shape.measure_complete : (shape : Shape Atom Count) → (depth budget : Nat) →
      shape.nodes ≤ budget → shape.height ≤ depth → (shape.measure depth budget).isSome = true
    | shape, 0, _, _, bounded => by cases shape <;> simp [Shape.height] at bounded
    | shape, _ + 1, 0, bounded, _ => by cases shape <;> simp [Shape.nodes] at bounded
    | .atom _, _ + 1, _ + 1, _, _ => rfl
    | .fin _, _ + 1, _ + 1, _, _ => rfl
    | .product elements, depth + 1, budget + 1, nodes, height => by
        have accepted := measureShapesLoop_complete elements depth
          (MeasurementState.start elements depth budget)
          (by change shapesNodes elements ≤ budget; simp only [Shape.nodes] at nodes; omega)
          (by simp only [Shape.height] at height; omega)
        cases found : measureShapesLoop depth elements (MeasurementState.start elements depth budget) with
        | none => simp [found] at accepted
        | some result => simp [Shape.measure, found]
    | .vector element _, depth + 1, budget + 1, nodes, height => by
        have accepted := element.measure_complete depth budget
          (by simp only [Shape.nodes] at nodes; omega)
          (by simp only [Shape.height] at height; omega)
        cases found : element.measure depth budget with
        | none => simp [found] at accepted
        | some result => simp [Shape.measure, found]
  termination_by structural shape _ _ _ _ => shape

  theorem measureShapesLoop_complete : (shapes : List (Shape Atom Count)) → (depth : Nat) →
      {all : List (Shape Atom Count)} → {budget : Nat} → (state : MeasurementState shapes all depth budget) →
      shapesNodes shapes ≤ state.remaining → shapesHeight shapes ≤ depth →
      (measureShapesLoop depth shapes state).isSome = true
    | [], _, _, _, _, _, _ => rfl
    | first :: rest, depth, _, _, state, nodes, height => by
        have firstAccepted := first.measure_complete depth state.remaining
          (by simp only [shapesNodes] at nodes; omega)
          (by simp only [shapesHeight, Nat.max_le] at height; exact height.1)
        cases firstFound : first.measure depth state.remaining with
        | none => simp [firstFound] at firstAccepted
        | some head =>
          have restAccepted := measureShapesLoop_complete rest depth (state.advance head)
            (by have := head.nodes_eq; simp only [shapesNodes] at nodes
                change shapesNodes rest ≤ head.remaining; omega)
            (by simp only [shapesHeight, Nat.max_le] at height; exact height.2)
          simpa [measureShapesLoop, firstFound] using restAccepted
  termination_by structural shapes _ _ _ _ _ _ => shapes
end

theorem measureShapes_complete (shapes : List (Shape Atom Count)) (depth budget : Nat)
    (nodes : shapesNodes shapes ≤ budget) (height : shapesHeight shapes ≤ depth) :
    (measureShapes depth budget shapes).isSome = true :=
  measureShapesLoop_complete shapes depth (MeasurementState.start shapes depth budget) nodes height

def Shape.withinLimits (shape : Shape Atom Count) : Bool :=
  (shape.measure (FormationLimits.typeDepth + 1) FormationLimits.typeNodes).isSome

theorem Shape.withinLimits_bounds {shape : Shape Atom Count} (accepted : shape.withinLimits = true) :
    shape.nodes ≤ FormationLimits.typeNodes ∧ shape.height ≤ FormationLimits.typeDepth + 1 := by
  unfold withinLimits at accepted
  cases found : shape.measure (FormationLimits.typeDepth + 1) FormationLimits.typeNodes with
  | none => simp [found] at accepted
  | some result =>
      have := result.nodes_eq
      exact ⟨by omega, result.height_eq ▸ result.height_le⟩

theorem Shape.withinLimits_iff (shape : Shape Atom Count) :
    shape.withinLimits = true ↔
      shape.nodes ≤ FormationLimits.typeNodes ∧ shape.height ≤ FormationLimits.typeDepth + 1 :=
  ⟨Shape.withinLimits_bounds, fun bounded => shape.measure_complete _ _ bounded.1 bounded.2⟩

theorem shapesNodes_eq (shapes : List (Shape Atom Count)) :
    shapesNodes shapes = (shapes.map Shape.nodes).sum := by
  induction shapes with
  | nil => rfl
  | cons first rest ih => simp [shapesNodes, ih]

theorem shapesHeight_eq (shapes : List (Shape Atom Count)) :
    shapesHeight shapes = (shapes.map Shape.height).foldr max 0 := by
  induction shapes with
  | nil => rfl
  | cons first rest ih => simp [shapesHeight, ih]

/-- Boundary certificates retain only the root measurement. Constructed
products reuse the certificates of their actual operands. Child selection can
therefore avoid allocating evidence for unrelated boundary components. -/
inductive Shape.Certificate : Shape Atom Count → Type where
  | boundary {shape : Shape Atom Count} (measured : TypeMeasurement Shape.nodes Shape.height shape) :
      Certificate shape
  | product {elements : List (Shape Atom Count)}
      (measured : TypeMeasurement Shape.nodes Shape.height (.product elements))
      (children : Values Certificate elements) : Certificate (.product elements)

def Shape.Certificate.measurement {shape : Shape Atom Count} : shape.Certificate →
    TypeMeasurement Shape.nodes Shape.height shape
  | .boundary measured | .product measured _ => measured

/-- Convert cached counters without evaluating `nodes` or `height`. -/
def WalkResult.measurement? {shape : Shape Atom Count} {depth budget : Nat}
    (result : WalkResult Shape.nodes Shape.height shape depth budget) :
    Option (TypeMeasurement Shape.nodes Shape.height shape) :=
  let size : TypeSize := ⟨budget - result.remaining, result.measuredHeight⟩
  if bounded : size.Within then
    some ⟨size, by have := result.nodes_eq; simp only [size]; omega,
      result.height_eq, bounded⟩
  else none

theorem WalkResult.measurement?_complete {shape : Shape Atom Count} {depth budget : Nat}
    (result : WalkResult Shape.nodes Shape.height shape depth budget)
    (nodes : budget ≤ FormationLimits.typeNodes) (height : depth ≤ FormationLimits.typeDepth + 1) :
    result.measurement?.isSome = true := by
  have bounded : (TypeSize.mk (budget - result.remaining) result.measuredHeight).Within :=
    ⟨Nat.le_trans (Nat.sub_le _ _) nodes, Nat.le_trans result.height_le height⟩
  simp [WalkResult.measurement?, bounded]

/-- A child of a certified product is within the same structural limits.
Measure it only when this component is selected. -/
def Shape.measureBounded (shape : Shape Atom Count)
    (nodes : shape.nodes ≤ FormationLimits.typeNodes)
    (height : shape.height ≤ FormationLimits.typeDepth + 1) :
    TypeMeasurement Shape.nodes Shape.height shape :=
  let result := (shape.measure (FormationLimits.typeDepth + 1) FormationLimits.typeNodes).get
    (shape.measure_complete _ _ nodes height)
  ⟨⟨FormationLimits.typeNodes - result.remaining, result.measuredHeight⟩,
    by have := result.nodes_eq; change FormationLimits.typeNodes - result.remaining = _; omega, result.height_eq,
    ⟨Nat.sub_le _ _, result.height_le⟩⟩

theorem selected_nodes_le {shapes : List (Shape Atom Count)} {shape : Shape Atom Count}
    (selected : Var shapes shape) : shape.nodes ≤ shapesNodes shapes := by
  induction selected with
  | here => simp [shapesNodes]
  | there _ ih => simp only [shapesNodes]; omega

theorem selected_height_le {shapes : List (Shape Atom Count)} {shape : Shape Atom Count}
    (selected : Var shapes shape) : shape.height ≤ shapesHeight shapes := by
  induction selected with
  | here => exact Nat.le_max_left _ _
  | there _ ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

def Shape.Certificate.view {shape : Shape Atom Count} (certificate : shape.Certificate) :
    Option (CertifiedProductView Shape.product Shape.Certificate shape) :=
  match certificate with
  | .product _ children => some ⟨_, rfl, fun selected => children.get selected⟩
  | .boundary measured =>
    match shape, measured with
    | .product elements, measured => some ⟨elements, rfl, fun selected =>
        .boundary (Shape.measureBounded _
          (by have := measured.within.1; rw [measured.nodes_eq] at this
              have childBound := selected_nodes_le selected; simp only [Shape.nodes] at this; omega)
          (by have := measured.within.2; rw [measured.height_eq] at this
              have childBound := selected_height_le selected; simp only [Shape.height] at this; omega))⟩
    | .atom _, _ | .fin _, _ | .vector _ _, _ => none

structure CertifiedWalk (shape : Shape Atom Count) (depth budget : Nat)
    extends WalkResult Shape.nodes Shape.height shape depth budget where
  certificate : shape.Certificate

/-- The one bounded structural walker supplies the root measurement. A
successful boundary call retains only root certificate data. Selecting a product
component performs a bounded walk of that child; the admission meter must cover it. -/
def Shape.certify (depth budget : Nat) (shape : Shape Atom Count) :
    Option (CertifiedWalk shape depth budget) := do
  let walk ← shape.measure depth budget
  let measured ← walk.measurement?
  return ⟨walk, .boundary measured⟩

theorem Shape.certify_complete (shape : Shape Atom Count) (depth budget : Nat)
    (nodes : shape.nodes ≤ budget) (height : shape.height ≤ depth)
    (budgetBound : budget ≤ FormationLimits.typeNodes) (depthBound : depth ≤ FormationLimits.typeDepth + 1) :
    (shape.certify depth budget).isSome = true := by
  have accepted := shape.measure_complete depth budget nodes height
  cases found : shape.measure depth budget with
  | none => simp [found] at accepted
  | some result =>
      simp [Shape.certify, found, Option.isSome_bind, Option.any_true]
      exact result.measurement?_complete budgetBound depthBound

def capacity : TypeCapacity (Shape Atom Count) Count Shape.product Shape.vector where
  nodes := Shape.nodes
  height := Shape.height
  product_nodes types := by simp [Shape.nodes, shapesNodes_eq]
  product_height types := by simp [Shape.height, shapesHeight_eq]
  vector_nodes _ _ := rfl
  vector_height _ _ := rfl
  Certificate := Shape.Certificate
  measurement := Shape.Certificate.measurement
  boundary := Shape.Certificate.boundary
  productCertificate := Shape.Certificate.product
  vectorCertificate _ measured _ := .boundary measured
  view := Shape.Certificate.view
  measure shape := (shape.certify (FormationLimits.typeDepth + 1) FormationLimits.typeNodes).map
    (·.certificate)

/-- Retaining child certificates leaves the structural acceptance boundary
exactly equal to the mathematical node and height limits. -/
theorem capacity_measure_iff (shape : Shape Atom Count) :
    (capacity.measure shape).isSome = true ↔
      shape.nodes ≤ FormationLimits.typeNodes ∧ shape.height ≤ FormationLimits.typeDepth + 1 := by
  constructor
  · intro accepted
    obtain ⟨certificate, _⟩ := Option.isSome_iff_exists.mp accepted
    have bounded := certificate.measurement.within
    simpa [TypeSize.Within, certificate.measurement.nodes_eq, certificate.measurement.height_eq]
      using bounded
  · intro bounded
    simpa [capacity] using shape.certify_complete (FormationLimits.typeDepth + 1)
      FormationLimits.typeNodes bounded.1 bounded.2 (Nat.le_refl _) (Nat.le_refl _)

/-- Every concrete product certificate exposes its actual components. The view
itself does not traverse children; it produces a selector for the checked index. -/
theorem product_view_types {elements : List (Shape Atom Count)}
    (certificate : (Shape.product elements).Certificate) :
    ∃ view, capacity.view certificate = some view ∧ view.types = elements := by
  cases certificate with
  | boundary measured => exact ⟨_, rfl, rfl⟩
  | product measured children => exact ⟨_, rfl, rfl⟩

theorem capacity_lawful : (capacity (Atom := Atom) (Count := Count)).Lawful where
  measurement_boundary := by intros; rfl
  measurement_product := by intros; rfl
  measurement_vector := by intros; rfl
  view_product := by intros; rfl
  view_complete := product_view_types
  measure_complete := fun shape nodes height => (capacity_measure_iff shape).mpr ⟨nodes, height⟩

end Zkc.Source.Mathematical.Data
