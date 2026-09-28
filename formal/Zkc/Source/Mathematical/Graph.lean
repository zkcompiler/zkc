import Zkc.Source.Mathematical.Meaning

/-! Intrinsically typed pure graphs over resolved operation signatures.

The graph retains its indexed bodies and explicit capture edges. Availability
belongs to each value; an unused capture does not taint a node. This is the pure
mathematical layer used before placement, independent of a storage schedule.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Graph

structure Algebra where
  Ty : Type
  Count : Type := Nat
  Op : Type
  arguments : Op → List Ty
  result : Op → Ty
  index : Count → Ty
  condition : Ty
  Wire : Ty → Type
  product : List Ty → Ty
  vector : Ty → Count → Ty

variable {Role : Type} [DecidableEq Role] {parties : List Role} {algebra : Algebra}

abbrev Ports := List (Port Role algebra.Ty)

def vectorPorts (count : algebra.Count) (ports : Ports (Role := Role) (algebra := algebra)) :
    Ports (Role := Role) (algebra := algebra) :=
  ports.map fun port => ⟨port.roles, algebra.vector port.ty count⟩

/-- Region outputs are exact references. Availability weakening belongs to the
protocol boundary, not to pure graph nodes or fold invariants. -/
inductive Region (parties : List Role) (algebra : Algebra) :
    List (Port Role algebra.Ty) → List (Port Role algebra.Ty) → Type where
  | outputs {Γ ports} (refs : Operands Γ ports) : Region parties algebra Γ ports
  | operation {Γ ports roles} (op : algebra.Op) (args : Inputs Γ (algebra.arguments op))
      (availability : roles = Inputs.available parties args)
      (next : Region parties algebra (⟨roles, algebra.result op⟩ :: Γ) ports) :
      Region parties algebra Γ ports
  | tuple {Γ ports types roles} (args : Inputs Γ types)
      (availability : roles = Inputs.available parties args)
      (next : Region parties algebra (⟨roles, algebra.product types⟩ :: Γ) ports) :
      Region parties algebra Γ ports
  | project {Γ ports types ty} (value : Input Γ (algebra.product types))
      (component : Var types ty)
      (next : Region parties algebra (⟨value.1, ty⟩ :: Γ) ports) :
      Region parties algebra Γ ports
  | map {Γ ports captures outputs} (count : algebra.Count) (capture : Operands Γ captures)
      (body : Region parties algebra (⟨parties, algebra.index count⟩ :: captures) outputs)
      (next : Region parties algebra (vectorPorts count outputs ++ Γ) ports) :
      Region parties algebra Γ ports
  | fold {Γ ports captures carried} (count : algebra.Count) (initial : Operands Γ carried)
      (capture : Operands Γ captures)
      (body : Region parties algebra
        (⟨parties, algebra.index count⟩ :: (carried ++ captures)) carried)
      (next : Region parties algebra (carried ++ Γ) ports) :
      Region parties algebra Γ ports

/-- Total mathematical meanings. This interface describes values, not machine
buffers. The product/vector laws are supplied separately for transformation
proofs; formation and evaluation need only these total constructors. -/
structure Interpretation (algebra : Algebra) where
  Value : algebra.Ty → Type
  count : algebra.Count → Nat
  pure : (op : algebra.Op) → Values Value (algebra.arguments op) → Value (algebra.result op)
  condition : Value algebra.condition → Bool
  index : {n : algebra.Count} → Fin (count n) → Value (algebra.index n)
  tuple : {types : List algebra.Ty} → Values Value types → Value (algebra.product types)
  project : {types : List algebra.Ty} → {ty : algebra.Ty} →
    Var types ty → Value (algebra.product types) → Value ty
  vector : {ty : algebra.Ty} → {n : algebra.Count} →
    (Fin (count n) → Value ty) → Value (algebra.vector ty n)
  element : {ty : algebra.Ty} → {n : algebra.Count} →
    Value (algebra.vector ty n) → Fin (count n) → Value ty

structure Interpretation.Lawful (meaning : Interpretation algebra) : Prop where
  project_tuple : ∀ {types ty} (values : Values meaning.Value types) (component : Var types ty),
    meaning.project component (meaning.tuple values) = values.get component
  tuple_project : ∀ {types} (value : meaning.Value (algebra.product types)),
    ∃ values : Values meaning.Value types, meaning.tuple values = value
  element_vector : ∀ {ty count} (values : Fin (meaning.count count) → meaning.Value ty) (i : Fin (meaning.count count)),
    meaning.element (meaning.vector values) i = values i
  vector_element : ∀ {ty count} (value : meaning.Value (algebra.vector ty count)),
    meaning.vector (meaning.element value) = value

/-- Left fold in ascending index order. Admission stores one body regardless of
count; this recursion belongs only to its mathematical execution. -/
def indexedFold {A : Type} : (count : Nat) → (Fin count → A → A) → A → A
  | 0, _, value => value
  | count + 1, body, value => indexedFold count (fun i => body i.succ) (body 0 value)

@[simp] theorem indexedFold_zero {A : Type} (body : Fin 0 → A → A) (value : A) :
    indexedFold 0 body value = value := rfl

theorem indexedFold_succ {A : Type} (count : Nat) (body : Fin (count + 1) → A → A)
    (value : A) : indexedFold (count + 1) body value =
      indexedFold count (fun i => body i.succ) (body 0 value) := rfl

/-- Transpose the ordered body outputs into one mathematical vector per output. -/
def collectVectors (meaning : Interpretation algebra) (self : Role) (count : algebra.Count) :
    (ports : List (Port Role algebra.Ty)) →
    (Fin (meaning.count count) → Values (Component meaning.Value self) ports) →
      Values (Component meaning.Value self) (vectorPorts count ports)
  | [], _ => .nil
  | _ :: ports, values =>
      .cons (fun available => meaning.vector (fun i => (values i).get .here available))
        (collectVectors meaning self count ports (fun i =>
          match values i with | .cons _ rest => rest))

def Region.denote (meaning : Interpretation algebra) (self : Role) {Γ ports} :
    Region parties algebra Γ ports → Environment meaning.Value self Γ →
      Values (Component meaning.Value self) ports
  | .outputs refs, env => Operands.eval env refs
  | .operation op args availability next, env =>
      next.denote meaning self (env.push
        (fun h => meaning.pure op (Inputs.read parties args env (availability ▸ h))))
  | .tuple args availability next, env =>
      next.denote meaning self (env.push
        (fun h => meaning.tuple (Inputs.read parties args env (availability ▸ h))))
  | .project (ty := ty) value component next, env =>
      next.denote meaning self (env.push (ty := ⟨value.1, ty⟩)
        (fun h => meaning.project component (env value.2 h)))
  | .map count capture body next, env =>
      let captured := Operands.eval env capture
      let values := collectVectors meaning self count _ (fun i =>
        body.denote meaning self
          (Source.Environment.push (fun v => captured.get v) (fun _ => meaning.index i)))
      next.denote meaning self (env.prepend values)
  | .fold count initial capture body next, env =>
      let captured := Operands.eval env capture
      let step := fun i values => body.denote meaning self
        (Source.Environment.push (Source.Environment.prepend (fun v => captured.get v) values)
          (fun _ => meaning.index i))
      next.denote meaning self (env.prepend (indexedFold (meaning.count count) step (Operands.eval env initial)))

/-- Source-level product elimination has its registered mathematical meaning. -/
theorem project_tuple (meaning : Interpretation algebra) (laws : meaning.Lawful)
    {types ty} (values : Values meaning.Value types) (component : Var types ty) :
    meaning.project component (meaning.tuple values) = values.get component :=
  laws.project_tuple values component

end Zkc.Source.Mathematical.Graph
