module

public import ZkcSecurity.FiatShamir.Binding
public import Zkc.Construction.Semantics

@[expose] public section

/-! # The policy-derived binding codec

A host binds a policy statement before the first request. The policy-derived
codec (`policyCodec`) binds it as one typed public-value binding event
(`Zkc.Construction.Event.publicBinding`): the application context and a row with
one entry per published input, in policy order, labelled by its position and
holding the input's typed public value (`publicValue`): a scalar for a field,
group or Boolean value, a vector whose length is part of the value for a
vector, and a count for an index. The row is injective on every statement of
the published types, malformed ones included (`policyRow_injective`), and every
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

/-- The typed public value of one published input. -/
def publicValue : (ty : Ty) → assignment F G ty → PublicValue (Payload F G)
  | .boolean, value => .scalar (.boolean value)
  | .index, value => .count value
  | .field domain, value => .scalar (.field domain value)
  | .vector domain, values => .vector (values.map (.field domain))
  | .group domain, value => .scalar (.group domain value)
  | .service _, handle => .count handle

theorem publicValue_injective : ∀ ty : Ty, Function.Injective (publicValue (F := F) (G := G) ty)
  | .boolean, _, _, same => by simpa [publicValue] using same
  | .index, _, _, same => by simpa [publicValue] using same
  | .field _, _, _, same => by simpa [publicValue] using same
  | .vector _, first, second, same => by
      simp only [publicValue, PublicValue.vector.injEq] at same
      exact List.map_injective_iff.mpr (fun _ _ equal => by cases equal; rfl) same
  | .group _, _, _, same => by simpa [publicValue] using same
  | .service _, _, _, same => by simpa [publicValue] using same

/-- The row of a statement's published values from a position on, each labelled
by its position. -/
def policyRowFrom (position : Nat) : {tys : List Ty} → Values (assignment F G) tys → Row (Payload F G)
  | [], .nil => []
  | ty :: _, .cons value rest => (toString position, publicValue ty value) :: policyRowFrom (position + 1) rest

theorem policyRowFrom_injective : ∀ (position : Nat) {tys : List Ty},
    Function.Injective (policyRowFrom (F := F) (G := G) position (tys := tys))
  | _, [], .nil, .nil, _ => rfl
  | position, ty :: _, .cons value rest, .cons value' rest', same => by
      simp only [policyRowFrom, List.cons.injEq, Prod.mk.injEq, true_and] at same
      rw [publicValue_injective ty same.1, policyRowFrom_injective (position + 1) same.2]

/-- The row of a statement's published values, in policy order. -/
def policyRow {tys : List Ty} (statement : Values (assignment F G) tys) : Row (Payload F G) :=
  policyRowFrom 0 statement

theorem policyRow_injective {tys : List Ty} : Function.Injective (policyRow (F := F) (G := G) (tys := tys)) :=
  policyRowFrom_injective 0

/-- The policy-derived binding codec: one typed public-value binding event of the
application context and the statement's row. -/
def policyCodec (tys : List Ty) (application : String) :
    BindingCodec (Values (assignment F G) tys) (Event F G) :=
  BindingCodec.single Event.publicBinding (fun _ _ same => by cases same; rfl) application policyRow
    policyRow_injective

theorem policyCodec_encode (tys : List Ty) (application : String) (statement : Values (assignment F G) tys) :
    (policyCodec tys application).encode statement = [.publicBinding ⟨application, policyRow statement⟩] :=
  rfl

end ZkcSecurity.Endpoint
