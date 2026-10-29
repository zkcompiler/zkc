module

public import Zkc.Construction.OriginalABI
public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! The complete return contract of a source connection.

The source signature and selected construction profile determine this contract
before an alignment certificate is proposed. Every source output is accounted
for, including absent role components. The only extra returned value is the
profile's final transcript. Physical SSA locations are readback evidence, not a
choice of which source results the connection promises to preserve.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

/-- Source-owned data sorts, in source output order. Malformed scope lists and
visible capabilities cannot be represented as physical data outputs. -/
def roleOutputSorts (role : Nat) : List (List Nat) → List Structured.Ty → Option (List ValueSort)
  | [], [] => some []
  | scope :: scopes, ty :: types => do
      let rest ← roleOutputSorts role scopes types
      if role ∈ scope then
        if ty.isHandle then none else some (.data ty :: rest)
      else some rest
  | _, _ => none

/-- Encode the complete optional source tuple. An invisible value must actually
be absent; a visible output must have its declared nominal data encoding. -/
def roleOutputValues (role : Nat) : List (List Nat) → {types : List Structured.Ty} →
    Values (Component carriers.Value) types → Option (Domain.Environment carriers)
  | [], [], .nil => some []
  | scope :: scopes, ty :: _, .cons value values => do
      let rest ← roleOutputValues role scopes values
      if role ∈ scope then
        let actual ← value
        let encoded ← Domain.Value.encode ty actual
        some (encoded :: rest)
      else
        match value with
        | none => some rest
        | some _ => none
  | _, _, _ => none

/-- The complete encoder determines its own nominal schema. This reusable
law discharges loop-result sort obligations without per-protocol tuple proofs. -/
theorem roleOutputValues_sorts (role : Nat) {scopes : List (List Nat)}
    {types : List Structured.Ty} (values : Values (Component carriers.Value) types)
    {encoded : Domain.Environment carriers}
    (found : roleOutputValues role scopes values = some encoded) :
    roleOutputSorts role scopes types = some (encoded.map Domain.Value.sort) := by
  induction values generalizing scopes encoded with
  | nil => cases scopes <;> simp_all [roleOutputValues, roleOutputSorts]
  | @cons ty types value values ih =>
    cases scopes with
    | nil => simp [roleOutputValues] at found
    | cons scope scopes =>
      cases tail : roleOutputValues role scopes values with
      | none => simp [roleOutputValues, tail] at found
      | some rest =>
        have tailSorts := ih tail
        by_cases visible : role ∈ scope
        · cases value with
          | none => simp [roleOutputValues, tail, visible] at found
          | some value =>
            cases head : Domain.Value.encode ty value with
            | none => simp [roleOutputValues, tail, visible, head] at found
            | some actual =>
              have data : ty.isHandle = false := by
                unfold Domain.Value.encode Domain.Payload.ofValue at head
                split at head
                · assumption
                · simp at head
              simp only [roleOutputValues, tail, visible, ↓reduceIte,
                bind, Option.bind, head, Option.some.injEq] at found
              subst encoded
              simp [roleOutputSorts, tailSorts, visible, data, Domain.Value.encode_sort head]
        · cases value with
          | some value => simp [roleOutputValues, tail, visible] at found
          | none =>
            simp only [roleOutputValues, tail, visible, ↓reduceIte, bind, Option.bind,
              Option.some.injEq] at found
            subst encoded
            simp [roleOutputSorts, tailSorts, visible]

/-- A complete encoded role row already obeys the source visibility mask.
The loop invariant therefore survives entry and exit masks structurally. -/
theorem roleOutputValues_mask (role : Nat) {scopes : List (List Nat)}
    {types : List Structured.Ty} (values : Values (Component carriers.Value) types)
    {encoded : Domain.Environment carriers}
    (found : roleOutputValues role scopes values = some encoded) :
    Structured.maskValues role scopes values = values := by
  induction values generalizing scopes encoded with
  | nil => rfl
  | @cons ty types value values ih =>
    cases scopes with
    | nil => simp [roleOutputValues] at found
    | cons scope scopes =>
      cases tail : roleOutputValues role scopes values with
      | none => simp [roleOutputValues, tail] at found
      | some rest =>
        have masked := ih tail
        by_cases visible : role ∈ scope
        · simp [Structured.maskValues, Participant.restrict, visible, masked]
        · cases value with
          | some value => simp [roleOutputValues, tail, visible] at found
          | none => simp [Structured.maskValues, Participant.restrict, masked]

/-- A plain connection has no auxiliary return. Fiat--Shamir returns the
reached transcript under its fixed suite, even when it has no new events. -/
def profileOutputSorts (context : Context) (data : List ValueSort) : List ValueSort :=
  match context.profile with
  | .plain => data
  | .fiatShamir replacement => data ++ [.transcript replacement.suite]

/-- Root returns preserve all data, the exact reached history, and the source
stack. The artifact's own output declarations and selectors must agree too.
Unrelated SSA temporaries remain abstract; they cannot replace a source output.
-/
structure CompleteReturns (signature : Structured.ProtocolSignature) (context : Context)
    (role : Nat) (artifact : Participant)
    (source : Values (Component carriers.Value) signature.outputs × State carriers)
    (target : Domain.Result carriers) : Prop where
  schema : ∃ sorts, roleOutputSorts role signature.outputScopes signature.outputs = some sorts ∧
    artifact.outputs = profileOutputSorts context sorts
  values : ∃ data, roleOutputValues role signature.outputScopes source.1 = some data ∧
    target.values = Domain.inputFrame context data source.2.history
  readback : Domain.read target.environment artifact.returned = some target.values
  sorts : Domain.sortsMatch artifact.outputs target.values = true
  frames : source.2.frames = []

/-- The complete contract fixes output arity independently of the selected
acceptance Boolean. Appending an unclaimed output cannot satisfy it. -/
theorem CompleteReturns.arity {signature : Structured.ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    {source : Values (Component carriers.Value) signature.outputs × State carriers}
    {target : Domain.Result carriers}
    (related : CompleteReturns signature context role artifact source target) :
    target.values.length = artifact.outputs.length := by
  have sorts : target.values.map Domain.Value.sort = artifact.outputs := by
    simpa only [Domain.sortsMatch, beq_iff_eq] using related.sorts
  simpa only [List.length_map] using congrArg List.length sorts

/-- An unchanged source return determines every physical result. This includes
non-Boolean residuals and the final history, not only the acceptance bit. -/
theorem CompleteReturns.values_unique {signature : Structured.ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    {source : Values (Component carriers.Value) signature.outputs × State carriers}
    {left right : Domain.Result carriers}
    (first : CompleteReturns signature context role artifact source left)
    (second : CompleteReturns signature context role artifact source right) :
    left.values = right.values := by
  obtain ⟨data, encoded, returned⟩ := first.values
  obtain ⟨other, otherEncoded, otherReturned⟩ := second.values
  have same : data = other := Option.some.inj (encoded.symm.trans otherEncoded)
  simpa only [same, returned] using otherReturned.symm

/-- A successful root returns to the empty source stack; an unclosed nested
repeat cannot be hidden by projecting its acceptance output. -/
theorem CompleteReturns.closed_frames {signature : Structured.ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    {source : Values (Component carriers.Value) signature.outputs × State carriers}
    {target : Domain.Result carriers}
    (related : CompleteReturns signature context role artifact source target) :
    source.2.frames = [] := related.frames

end Zkc.Construction.Original
