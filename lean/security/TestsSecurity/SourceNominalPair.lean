module

public import ZkcSecurity.Bindings.Source.PairRouting

@[expose] public section

/-! Honest messages retain nominal products and groups. Host-type equality
cannot change the message sort, and aggregate capabilities cannot be
smuggled through the data rule. The shared fold law retains the full history. -/
set_option autoImplicit false
namespace TestsSecurity.SourceNominalPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Source

def scope : PairScope := ⟨0, 1, []⟩
variable {carriers : Carriers}

def send (ty : Ty) (value : carriers.Value ty) :
    PIR.Process (Occurrence.signature carriers) Unit :=
  .call (.action (.send (ty := ty) "message" 1 value)) (fun _ => .done ())

def receive (ty : Ty) : PIR.Process (Occurrence.signature carriers) (carriers.Value ty) :=
  .call (.action (.receive ty "message" 0)) .done

theorem message (ty : Ty) (data : ty.isHandle = false) (value : carriers.Value ty) :
    Pair scope (fun _ received => received = value) (send ty value) (receive ty) := by
  apply Pair.message ty "message" 0 1 value data ⟨rfl, rfl⟩
  exact .done rfl

def packet : Ty := .product "test.packet/0" "packet"
  (.cons (.group "curve.g1") (.cons (.sequence (.field "scalar")) .nil))

example (point : carriers.Group "curve.g1") (coefficients : List (carriers.Field "scalar")) :
    Pair scope (fun _ received => received = (point, coefficients, ()))
      (send packet (point, coefficients, ())) (receive packet) :=
  message packet rfl _

private def sentType {A : Type} : PIR.Process (Occurrence.signature carriers) A → Option Ty
  | .call (.action (@Participant.Action.send _ _ _ _ ty _ _ _)) _ => some ty
  | _ => none

private def receivedType {A : Type} : PIR.Process (Occurrence.signature carriers) A → Option Ty
  | .call (.action (.receive ty _ _)) _ => some ty
  | _ => none

private theorem message_boundary {A B : Type} {post : A → B → Prop}
    {left : PIR.Process (Occurrence.signature carriers) A}
    {right : PIR.Process (Occurrence.signature carriers) B} (paired : Pair scope post left right) :
    ∀ ty, sentType left = some ty → ty.isHandle = false ∧ receivedType right = some ty := by
  cases paired <;> simp_all [sentType, receivedType]

/-- Equal host types do not equate nominal group and field messages. -/
theorem distinct_sorts (value : Rat) :
    ¬ Pair scope (fun _ _ => True)
      (send (carriers := uniformCarriers Rat Rat) (.group "same") value)
      (receive (.field "same")) := by
  intro alleged
  have boundary := message_boundary alleged (.group "same") rfl
  cases boundary.2

/-- Service exclusion is recursive through nominal aggregate fields. -/
theorem no_capability_packet (handle : Nat) :
    ¬ Pair scope (fun _ _ => True)
      (send (carriers := uniformCarriers Rat Rat)
        (.product "test.service/0" "packet" (.cons (.service "random.scalar/0") .nil)) (handle, ()))
      (receive (.product "test.service/0" "packet" (.cons (.service "random.scalar/0") .nil))) := by
  intro alleged
  have boundary := message_boundary alleged _ rfl
  cases boundary.1

/-- An empty sequence cannot hide the capability in its element schema. -/
theorem no_empty_oracle_packet :
    ¬ Pair scope (fun _ _ => True)
      (send (carriers := carriers) (.sequence (.oracle (.table (.field "scalar") none))) [])
      (receive (.sequence (.oracle (.table (.field "scalar") none)))) := by
  intro alleged
  have boundary := message_boundary alleged _ rfl
  cases boundary.1

#print axioms message
#print axioms distinct_sorts
#print axioms no_capability_packet
#print axioms no_empty_oracle_packet
#print axioms ZkcSecurity.Source.publicFoldLaws
end TestsSecurity.SourceNominalPair
