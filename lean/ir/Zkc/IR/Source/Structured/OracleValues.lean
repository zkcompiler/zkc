module

public import Zkc.IR.Source.Structured.Algebra

@[expose] public section

/-! Protocol boundary values with deferred holder data. These references contain no virtual body,
store, admissibility proof, or evaluator. Ordinary mathematical carriers remain unchanged. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- A complete logical sort, including sequence capacity independently of element shape. -/
inductive OracleLogicalSort where
  | singleton (kind : OracleKind)
  | sequence (kind : OracleKind) (maximum : Nat)
  deriving DecidableEq, Repr

@[reducible] def OracleLogicalSort.type : OracleLogicalSort → Ty
  | .singleton kind => .oracle kind
  | .sequence kind maximum => .oracleSequence kind maximum

@[reducible] def OracleLogicalSort.dataType : OracleLogicalSort → Ty
  | .singleton kind => kind.data
  | .sequence kind _ => .sequence kind.data

def OracleLogicalSort.ofType : Ty → Option OracleLogicalSort
  | .oracle kind => some (.singleton kind)
  | .oracleSequence kind maximum => some (.sequence kind maximum)
  | _ => none

@[simp] theorem OracleLogicalSort.ofType_type (sort : OracleLogicalSort) :
    ofType sort.type = some sort := by cases sort <;> rfl

theorem OracleLogicalSort.dataType_ne_product (sort : OracleLogicalSort)
    (identity constructor : String) (fields : ProductFields) :
    sort.dataType ≠ .product identity constructor fields := by
  cases sort with
  | sequence => simp [OracleLogicalSort.dataType]
  | singleton kind =>
    cases kind with
    | table row rows => cases row <;> simp [OracleLogicalSort.dataType, OracleKind.data]

/-- Shape coordinates follow the existing kind's exact dimension order. The reference is data,
not evidence of store membership, static-extent validity, or an honest input relation. -/
abbrev OracleShape (kind : OracleKind) := Values (fun _ ↦ Nat) kind.shape

structure OracleReference (kind : OracleKind) where
  anchor : OracleAnchor
  shape : OracleShape kind

@[reducible] def OracleLogicalSort.References : OracleLogicalSort → Type
  | .singleton kind => OracleReference kind
  | .sequence kind _ => List (OracleReference kind)

/-- Both interface leaves refer to this exact pair. In particular an empty sequence still retains
its holder, receivers and complete logical sort. No payload equality can manufacture this pair. -/
structure OracleDataView (sort : OracleLogicalSort) where
  holder : Nat
  receivers : List Nat
  references : sort.References

def OracleDataView.anchors {sort : OracleLogicalSort} (view : OracleDataView sort) :
    (carriers : Carriers) → carriers.Value sort.type :=
  match sort, view with
  | .singleton _, view => fun _ ↦ view.references.anchor
  | .sequence _ _, view => fun _ ↦ view.references.map (·.anchor)

/-- Receiver membership is checked after role substitution; forwarding retains the stored order.
The exact reference tuple includes every actual shape, anchor, repetition and sequence position. -/
def OracleDataView.SamePair {sort : OracleLogicalSort} (left right : OracleDataView sort) : Prop :=
  left.holder = right.holder ∧
    (∀ role, role ∈ left.receivers ↔ role ∈ right.receivers) ∧ left.references = right.references

theorem OracleDataView.SamePair.anchors_eq {sort : OracleLogicalSort}
    {left right : OracleDataView sort} (same : left.SamePair right) (carriers : Carriers) :
    left.anchors carriers = right.anchors carriers := by
  cases sort <;> simp only [OracleDataView.anchors, same.2.2]

/-- Concrete aggregate values have only their recursive encoding. Deferred data is a distinct
leaf, including a deferred general sequence. A product itself is never a concrete opaque leaf. -/
def Ty.isAggregate : Ty → Bool
  | .product .. | .sequence _ => true
  | _ => false

mutual
  inductive ProtocolValue (carriers : Carriers) : Ty → Type where
    | concrete {type : Ty} (atomic : type.isAggregate = false) (value : carriers.Value type) :
        ProtocolValue carriers type
    | deferred {sort : OracleLogicalSort} (view : OracleDataView sort) :
        ProtocolValue carriers sort.dataType
    | product (identity constructor : String) (fields : ProductFields)
        (values : Values (ProtocolValue carriers) fields.toList) :
        ProtocolValue carriers (.product identity constructor fields)
    | sequence (element : Ty) (values : ProtocolSequence carriers element) :
        ProtocolValue carriers (.sequence element)

  /-- An explicitly indexed list avoids untyped elements and retains each deferred leaf. -/
  inductive ProtocolSequence (carriers : Carriers) : Ty → Type where
    | nil {element : Ty} : ProtocolSequence carriers element
    | cons {element : Ty} : ProtocolValue carriers element → ProtocolSequence carriers element →
        ProtocolSequence carriers element
end

/-- Structural induction on a sequence does not inspect or force its element values. -/
theorem ProtocolSequence.induction {carriers : Carriers} {element : Ty}
    {motive : ProtocolSequence carriers element → Prop} (nil : motive .nil)
    (cons : ∀ value values, motive values → motive (.cons value values))
    (values : ProtocolSequence carriers element) : motive values := by
  cases values with
  | nil => exact nil
  | cons value values => exact cons value values (ProtocolSequence.induction nil cons values)

def ProtocolSequence.ofList {carriers : Carriers} {element : Ty} :
    List (ProtocolValue carriers element) → ProtocolSequence carriers element
  | [] => .nil
  | value :: rest => .cons value (ofList rest)

def ProtocolSequence.toList {carriers : Carriers} {element : Ty} :
    ProtocolSequence carriers element → List (ProtocolValue carriers element)
  | .nil => []
  | .cons value rest => value :: rest.toList

@[simp] theorem ProtocolSequence.toList_ofList {carriers : Carriers} {element : Ty}
    (values : List (ProtocolValue carriers element)) : (ofList values).toList = values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [ofList, toList, ih]

@[simp] theorem ProtocolSequence.ofList_toList {carriers : Carriers} {element : Ty}
    (values : ProtocolSequence carriers element) : ofList values.toList = values := by
  induction values using ProtocolSequence.induction with
  | nil => rfl
  | cons value values ih => simp only [ofList, toList, ih]

namespace ProtocolValue

mutual
  def ofConcrete {carriers : Carriers} :
      (type : Ty) → carriers.Value type → ProtocolValue carriers type
    | .sequence element, values => .sequence element (ofConcreteSequence element values)
    | .product identity constructor fields, values =>
        .product identity constructor fields (ofConcreteFields fields values)
    | .polynomial _, value => .concrete rfl value
    | .boolean, value => .concrete rfl value
    | .index, value => .concrete rfl value
    | .field _, value => .concrete rfl value
    | .vector _, value => .concrete rfl value
    | .group _, value => .concrete rfl value
    | .groups _, value => .concrete rfl value
    | .indices, value => .concrete rfl value
    | .service _, value => .concrete rfl value
    | .oracle _, value => .concrete rfl value
    | .oracleSequence _ _, value => .concrete rfl value
    | .resourceUnit _, value => .concrete rfl value

  def ofConcreteFields {carriers : Carriers} : (fields : ProductFields) →
      carriers.ProductValue fields → Values (ProtocolValue carriers) fields.toList
    | .nil, _ => .nil
    | .cons type rest, (value, values) =>
        .cons (ofConcrete type value) (ofConcreteFields rest values)

  def ofConcreteSequence {carriers : Carriers} : (element : Ty) →
      List (carriers.Value element) → ProtocolSequence carriers element
    | _, [] => .nil
    | element, value :: values =>
        .cons (ofConcrete element value) (ofConcreteSequence element values)
end

mutual
  /-- Partial structural retraction only: `none` means deferred data is present, not a source stop.
  This function never reads a store, checks a virtual predicate, or evaluates a virtual body. -/
  def toConcrete {carriers : Carriers} : {type : Ty} → ProtocolValue carriers type →
      Option (carriers.Value type)
    | _, .concrete _ value => some value
    | _, .deferred _ => none
    | _, .product _ _ fields values => toConcreteFields fields values
    | _, .sequence _ values => toConcreteSequence values

  def toConcreteFields {carriers : Carriers} : (fields : ProductFields) →
      Values (ProtocolValue carriers) fields.toList → Option (carriers.ProductValue fields)
    | .nil, .nil => some ()
    | .cons _ rest, .cons value values => do
        let head ← toConcrete value
        let tail ← toConcreteFields rest values
        pure (head, tail)

  def toConcreteSequence {carriers : Carriers} : {element : Ty} →
      ProtocolSequence carriers element → Option (List (carriers.Value element))
    | _, .nil => some []
    | _, .cons value values => do
        let head ← toConcrete value
        let tail ← toConcreteSequence values
        pure (head :: tail)
end

@[simp] theorem toConcrete_concrete {carriers : Carriers} {type : Ty}
    (atomic : type.isAggregate = false) (value : carriers.Value type) :
    toConcrete (.concrete atomic value) = some value := by
  rw [toConcrete]

@[simp] theorem toConcrete_product {carriers : Carriers} (identity constructor : String)
    (fields : ProductFields) (values : Values (ProtocolValue carriers) fields.toList) :
    toConcrete (.product identity constructor fields values) = toConcreteFields fields values := by
  rw [toConcrete]

@[simp] theorem toConcrete_sequence {carriers : Carriers} (element : Ty)
    (values : ProtocolSequence carriers element) :
    toConcrete (.sequence element values) = toConcreteSequence values := by rw [toConcrete]

mutual
  @[simp] theorem toConcrete_ofConcrete {carriers : Carriers} (type : Ty)
      (value : carriers.Value type) : toConcrete (ofConcrete type value) = some value := by
    cases type with
    | sequence element =>
      simpa only [ofConcrete, toConcrete] using
        toConcreteSequence_ofConcreteSequence element value
    | product identity constructor fields =>
      simpa only [ofConcrete, toConcrete] using toConcreteFields_ofConcreteFields fields value
    | _ => simp only [ofConcrete]; exact toConcrete_concrete _ _
  termination_by (sizeOf type, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  @[simp] theorem toConcreteFields_ofConcreteFields {carriers : Carriers} (fields : ProductFields)
      (values : carriers.ProductValue fields) :
      toConcreteFields fields (ofConcreteFields fields values) = some values := by
    cases fields with
    | nil => cases values; simp [ofConcreteFields, toConcreteFields]
    | cons type rest =>
      rcases values with ⟨value, values⟩
      simp only [ofConcreteFields, toConcreteFields, toConcrete_ofConcrete type value,
        toConcreteFields_ofConcreteFields rest values]
      rfl
  termination_by (sizeOf fields, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  @[simp] theorem toConcreteSequence_ofConcreteSequence {carriers : Carriers} (element : Ty)
      (values : List (carriers.Value element)) :
      toConcreteSequence (ofConcreteSequence element values) = some values := by
    cases values with
    | nil => simp [ofConcreteSequence, toConcreteSequence]
    | cons value values =>
      simp only [ofConcreteSequence, toConcreteSequence, toConcrete_ofConcrete element value,
        toConcreteSequence_ofConcreteSequence element values]
      rfl
  termination_by (sizeOf element, values.length + 1)
  decreasing_by all_goals subst_vars; simp_wf; omega
end

theorem ofConcrete_injective {carriers : Carriers} (type : Ty) :
    Function.Injective (ofConcrete (carriers := carriers) type) := by
  intro left right equal
  have := congrArg toConcrete equal
  simpa only [toConcrete_ofConcrete, Option.some.injEq] using this

@[simp] theorem toConcrete_deferred {carriers : Carriers} {sort : OracleLogicalSort}
    (view : OracleDataView sort) : toConcrete (carriers := carriers) (.deferred view) = none := by
  simp [toConcrete]

/-- Packing and projection copy the recursive fields; they perform no data demand. -/
def unpack {carriers : Carriers} {identity constructor : String} {fields : ProductFields}
    (value : ProtocolValue carriers (.product identity constructor fields)) :
    Values (ProtocolValue carriers) fields.toList := by
  generalize equation : Ty.product identity constructor fields = type at value
  cases value with
  | concrete atomic value => cases equation; contradiction
  | deferred view => exact False.elim (OracleLogicalSort.dataType_ne_product _ _ _ _ equation.symm)
  | sequence element values => cases equation
  | product identity constructor fields values => cases equation; exact values

@[simp] theorem unpack_product {carriers : Carriers} (identity constructor : String)
    (fields : ProductFields) (values : Values (ProtocolValue carriers) fields.toList) :
    unpack (.product identity constructor fields values) = values := rfl

def project {carriers : Carriers} {identity constructor : String} {fields : ProductFields}
    {type : Ty} (value : ProtocolValue carriers (.product identity constructor fields))
    (field : Var fields.toList type) : ProtocolValue carriers type := (unpack value).get field

@[simp] theorem project_product {carriers : Carriers} (identity constructor : String)
    (fields : ProductFields) (values : Values (ProtocolValue carriers) fields.toList)
    {type : Ty} (field : Var fields.toList type) :
    project (.product identity constructor fields values) field = values.get field := rfl

theorem ofConcreteFields_get {carriers : Carriers} (fields : ProductFields)
    (values : carriers.ProductValue fields) {type : Ty} (field : Var fields.toList type) :
    (ofConcreteFields fields values).get field =
      ofConcrete type ((fields.unpack values).get field) := by
  cases fields with
  | nil => cases field
  | cons type rest =>
    rcases values with ⟨value, values⟩
    cases field with
    | here => rw [ofConcreteFields, ProductFields.unpack]; rfl
    | there field =>
      rw [ofConcreteFields, ProductFields.unpack]
      exact ofConcreteFields_get rest values field
termination_by fields

@[simp] theorem project_ofConcrete {carriers : Carriers} (identity constructor : String)
    (fields : ProductFields) (value : carriers.ProductValue fields) {type : Ty}
    (field : Var fields.toList type) :
    project (ofConcrete (.product identity constructor fields) value) field =
      ofConcrete type ((fields.unpack value).get field) := by
  simp only [ofConcrete, project_product, ofConcreteFields_get]

end ProtocolValue
end Zkc.Source.Structured
