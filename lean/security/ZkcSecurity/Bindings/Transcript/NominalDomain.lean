module

public import Zkc.Construction.DomainProducer
public import ZkcSecurity.Bindings.Transcript.LosslessPresentation

public section

/-! A property presentation retaining arbitrary nominal Domain payloads and
request-indexed raw replies. It uses the existing transcript Interface. A
receive checks its origin and exact recursive sort, even when two nominal
domains happen to have the same host carrier.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.NominalDomain
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
variable {carriers : Carriers}

inductive Operation (carriers : Carriers) where
  | receive (ty : Ty) (origin : Origin)
  | deliver (origin : Origin) (payload : Domain.Payload carriers)
  | query (origin : Origin) (supported : Domain.drawRequest origin = true)

abbrev signature (carriers : Carriers) : PIR.Signature where
  Op := Operation carriers
  Reply
    | .receive ty _ => carriers.Value ty
    | .deliver .. => Unit
    | .query origin _ => Domain.Raw (.challenge origin : Domain.Event carriers)

@[expose] def received (ty : Ty) (origin : Origin) :
    Domain.Event carriers → Option (carriers.Value ty)
  | .message actual payload => if actual = origin then payload.value ty else none
  | _ => none

@[expose] def interface : Interface (signature carriers) (Domain.Event carriers)
    (Domain.Payload carriers) Domain.Raw
  | .receive ty origin => .receive (.message origin) (received ty origin)
  | .deliver origin payload => .send (.message origin payload) ()
  | .query origin _ => .query (.challenge origin) some

theorem received_message (ty : Ty) (origin : Origin) (payload : Domain.Payload carriers) :
    received ty origin (.message origin payload) = payload.value ty := by
  simp only [received, ite_true]

/-- Wrong nominal domains and aggregate layouts are refused, independently of
host carrier equality. -/
theorem received_wrong_type (ty : Ty) (origin : Origin) (payload : Domain.Payload carriers)
    (different : payload.ty ≠ ty) : received ty origin (.message origin payload) = none := by
  rw [received_message, Domain.Payload.value_wrong_type different]

theorem received_wrong_origin (ty : Ty) (expected actual : Origin)
    (payload : Domain.Payload carriers) (different : actual ≠ expected) :
    received ty expected (.message actual payload) = none := by
  simp only [received, different, ite_false]

/-- The unrestricted signature is retained. Only data receives have lossless
proof representation; sends and queries already retain all their replies. -/
@[expose] def DataOperation : (signature carriers).Op → Prop
  | .receive ty _ => ty.isHandle = false
  | .deliver .. | .query .. => True

mutual
  /-- A nominal model supplies inhabitants without selecting an extractor. This
  value only distinguishes decoder sorts in the proof of the local law. -/
  def modelValue (model : DomainModel) : (ty : Ty) → model.Value ty
    | .boolean => false
    | .index => 0
    | .field _ => 0
    | .vector _ | .indices | .groups _ => []
    | .group _ => 0
    | .service _ => 0
    | .oracle _ => ⟨⟨0, []⟩, .input 0⟩
    | .oracleSequence .. | .sequence _ => []
    | .product _ _ fields => modelProduct model fields
  def modelProduct (model : DomainModel) : (fields : ProductFields) → model.toCarriers.ProductValue fields
    | .nil => ()
    | .cons ty rest => (modelValue model ty, modelProduct model rest)
end

/-- Exact decoder equations force both the nominal sort and the identity reply
map. In particular, equal host carriers do not authorize another nominal sort. -/
theorem losslessOperation (model : DomainModel) (operation : (signature model.toCarriers).Op)
    (data : DataOperation operation) : Original.LosslessOperation interface operation where
  receive := by
    intro ty event recover reply absorbed decoded
    cases operation with
    | deliver => cases absorbed
    | query => cases absorbed
    | receive declared origin =>
      cases absorbed
      change declared.isHandle = false at data
      let witness : Domain.Payload model.toCarriers := ⟨declared, data, modelValue model declared⟩
      have sameSort : ty = declared := by
        have recognized := congrArg Option.isSome (decoded witness)
        simp only [received_message, Option.isSome_map, Domain.Payload.value_isSome] at recognized
        have same : declared = ty := of_decide_eq_true (by simpa [witness] using recognized.symm)
        exact same.symm
      subst ty
      have identity : ∀ value : model.Value declared, reply value = value := by
        intro value
        have same := decoded ⟨declared, data, value⟩
        simp [received_message, Domain.Payload.value] at same
        exact same.symm
      refine ⟨?_, fun value => ⟨⟨declared, data, value⟩, ?_⟩⟩
      · simpa only [show reply = id from funext identity] using Function.bijective_id
      · simp [Domain.Payload.ofValue, data]
  query := by
    intro origin reply absorbed
    cases operation with
    | receive => cases absorbed
    | deliver => cases absorbed
    | query actual supported =>
      injection absorbed with sameOrigin sameDecoder
      cases sameOrigin
      have identity : reply = id := by
        funext raw
        exact (Option.some.inj (congrFun (eq_of_heq sameDecoder) raw)).symm
      rw [identity]
      exact Function.bijective_id
  send := by
    intro event value absorbed reply
    cases operation with
    | receive => cases absorbed
    | query => cases absorbed
    | deliver => exact Subsingleton.elim reply value

/-- A service or logical oracle handle, including one hidden in a recursive
aggregate, cannot acquire a lossless receive law. The actual decoder has no proof payload for any such typed value. -/
theorem handleReceive_not_lossless (model : DomainModel) (ty : Ty) (origin : Origin)
    (handle : ty.isHandle = true) :
    ¬ Original.LosslessOperation interface (.receive ty origin : Operation model.toCarriers) := by
  intro lossless
  have encoded := (lossless.receive ty (.message origin) (received ty origin) id rfl
    (fun payload => by simpa only [Option.map_id, id_eq] using received_message ty origin payload)).2 (modelValue model ty)
  obtain ⟨payload, impossible⟩ := encoded
  simp only [Domain.Payload.ofValue, handle, Bool.true_eq_false, ↓reduceDIte, reduceCtorEq] at impossible

/-- A global lossless law for the unrestricted nominal signature is false. -/
theorem not_losslessInterface (model : DomainModel) (origin : Origin) :
    ¬ Original.LosslessInterface (interface (carriers := model.toCarriers)) := by
  intro lossless
  exact handleReceive_not_lossless model (.service "capability") origin rfl
    ⟨lossless.receive (.receive (.service "capability") origin),
      lossless.query (.receive (.service "capability") origin),
      lossless.send (.receive (.service "capability") origin)⟩

theorem losslessOn (model : DomainModel) {A : Type}
    (presented : PIR.Process (signature model.toCarriers) A)
    (data : OperationSupport DataOperation presented) : Original.LosslessOn interface presented :=
  data.mono (losslessOperation model)

end ZkcSecurity.FiatShamir.NominalDomain
