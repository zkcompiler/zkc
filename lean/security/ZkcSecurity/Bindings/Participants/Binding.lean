module

public import ZkcSecurity.Bindings.Transcript.DomainBinding
public import Zkc.Construction.Scalar

@[expose] public section

/-! # The policy-derived binding codec

A host binds a policy statement before the first request. The policy-derived
codec (`policyCodec`) binds it as one typed public-value binding event
(`Zkc.Construction.Event.publicBinding`): the application context and a row with
one entry per published input, in policy order, labelled by its position and
holding the input's typed public value (`publicValue`): scalars, vectors,
counts, ordered sequences and nominal products. Aggregate components preserve
their types recursively; product identity and constructor are retained. Schema admission excludes logical handles recursively. The row is injective on
every statement at the admitted types, malformed values included (`policyRow_injective`), and every
statement's history has one event, so the codec is injective and prefix-free and
discharges statement determination (`ZkcSecurity.FiatShamir.BindingCodec.determined`).

This discharges statement determination only. That the native transcript absorbs
the serialization of this typed representation is the separate obligation
`binding.native-absorption`, a trusted link until a theorem about native
transcript bytes exists.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

variable {F G : Type}

/- The typed public value of one eligible published input. The proof is
schema admission, not a value-validity predicate or a native codec. -/
mutual
  def publicValue : (ty : Ty) → ty.isHandle = false → assignment F G ty → PublicValue (Payload F G)
    | .boolean, _, value => .scalar (.boolean value)
    | .index, _, value => .count value
    | .field domain, _, value => .scalar (.field domain value)
    | .vector domain, _, values => .vector (values.map (.field domain))
    | .group domain, _, value => .scalar (.group domain value)
    | .groups domain, _, values => .vector (values.map (.group domain))
    | .indices, _, values => .sequence (PublicValues.ofList (values.map .count))
    | .service _, data, _ | .oracle _, data, _ | .oracleSequence .., data, _ => nomatch data
    | .sequence element, data, values =>
      .sequence (PublicValues.ofList (values.map (publicValue element data)))
    | .product identity constructor fields, data, value =>
      .product identity constructor (publicFields fields data value)

  def publicFields : (fields : ProductFields) → fields.hasHandle = false →
      (uniformCarriers F G).ProductValue fields → PublicValues (Payload F G)
    | .nil, _, () => .nil
    | .cons type rest, data, (value, values) =>
      .cons (publicValue type (Bool.or_eq_false_iff.mp data).1 value)
        (publicFields rest (Bool.or_eq_false_iff.mp data).2 values)
end

mutual
  theorem publicValue_injective : ∀ (ty : Ty) (data : ty.isHandle = false),
      Function.Injective (publicValue (F := F) (G := G) ty data)
    | .boolean, _, _, _, same => by simpa [publicValue] using same
    | .index, _, _, _, same => by simpa [publicValue] using same
    | .field _, _, _, _, same => by simpa [publicValue] using same
    | .vector _, _, _, _, same => by
        simp only [publicValue, PublicValue.vector.injEq] at same
        exact (List.map_inj_right (fun _ _ equal => by cases equal; rfl)).mp same
    | .group _, _, _, _, same => by simpa [publicValue] using same
    | .groups _, _, _, _, same => by
        simp only [publicValue, PublicValue.vector.injEq] at same
        exact (List.map_inj_right (fun _ _ equal => by cases equal; rfl)).mp same
    | .indices, _, _, _, same => by
        simp only [publicValue, PublicValue.sequence.injEq] at same
        exact (List.map_inj_right (fun _ _ equal => PublicValue.count.inj equal)).mp
          (PublicValues.ofList_injective same)
    | .service _, data, _, _, _ | .oracle _, data, _, _, _
    | .oracleSequence .., data, _, _, _ => nomatch data
    | .sequence element, data, _, _, same => by
        simp only [publicValue, PublicValue.sequence.injEq] at same
        exact (List.map_inj_right (fun _ _ equal => publicValue_injective element data equal)).mp
          (PublicValues.ofList_injective same)
    | .product _ _ fields, data, _, _, same => by
        simp only [publicValue, PublicValue.product.injEq, true_and] at same
        exact publicFields_injective fields data same

  theorem publicFields_injective : ∀ (fields : ProductFields) (data : fields.hasHandle = false),
      Function.Injective (publicFields (F := F) (G := G) fields data)
    | .nil, _, (), (), _ => rfl
    | .cons type rest, data, (value, values), (other, others), same => by
        have components := PublicValues.cons.inj same
        have head := publicValue_injective type (Bool.or_eq_false_iff.mp data).1 components.1
        have tail := publicFields_injective rest (Bool.or_eq_false_iff.mp data).2 components.2
        cases head
        cases tail
        rfl
end

/-- The row of a statement's published values, with its checked data schema. -/
def policyRowFrom (position : Nat) : {tys : List Ty} → Domain.PublicBinding.DataSchema tys →
    Values (assignment F G) tys → Row (Payload F G)
  | [], _, .nil => []
  | ty :: _, data, .cons value rest =>
      (toString position, publicValue ty
        (by simpa [Domain.PublicBinding.DataSchema, Domain.dataType] using (Bool.and_eq_true_iff.mp data).1)
        value) :: policyRowFrom (position + 1) (Bool.and_eq_true_iff.mp data).2 rest

theorem policyRowFrom_injective : ∀ (position : Nat) {tys : List Ty}
    (data : Domain.PublicBinding.DataSchema tys),
    Function.Injective (policyRowFrom (F := F) (G := G) position data)
  | _, [], _, .nil, .nil, _ => rfl
  | position, ty :: _, data, .cons value rest, .cons value' rest', same => by
      simp only [policyRowFrom, List.cons.injEq, Prod.mk.injEq, true_and] at same
      rw [publicValue_injective ty _ same.1,
        policyRowFrom_injective (position + 1) (Bool.and_eq_true_iff.mp data).2 same.2]

def policyRow {tys : List Ty} (data : Domain.PublicBinding.DataSchema tys)
    (statement : Values (assignment F G) tys) : Row (Payload F G) :=
  policyRowFrom 0 data statement

theorem policyRow_injective {tys : List Ty} (data : Domain.PublicBinding.DataSchema tys) :
    Function.Injective (policyRow (F := F) (G := G) data) :=
  policyRowFrom_injective 0 data

/-- The policy-derived binding codec requires a handle-free schema. Every raw
value at that schema remains bindable, including malformed relation inputs. -/
def policyCodec (tys : List Ty) (data : Domain.PublicBinding.DataSchema tys) (application : String) :
    BindingCodec (Values (assignment F G) tys) (Event F G) :=
  BindingCodec.single Event.publicBinding (fun _ _ same => by cases same; rfl) application
    (policyRow data) (policyRow_injective data)

theorem policyCodec_encode (tys : List Ty) (data : Domain.PublicBinding.DataSchema tys)
    (application : String) (statement : Values (assignment F G) tys) :
    (policyCodec tys data application).encode statement = [.publicBinding ⟨application, policyRow data statement⟩] :=
  rfl

end ZkcSecurity.Endpoint
