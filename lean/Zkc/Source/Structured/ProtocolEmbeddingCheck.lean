module

public import Zkc.Source.Structured.ProtocolEmbeddingSource

@[expose] public section

/-! A finite syntax check for the exact stored ordinary fragment. Users supply no
helper equations or semantic callbacks to specialize the embedding theorem. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source

mutual
  def checkFragment {d : Dialect} (test : d.Op → Bool) {ts us} : Region d ts us → Bool
    | .ret _ | .stop _ => true
    | .letOp op _ bodies next => test op && checkFragments test bodies && checkFragment test next
    | .bind body next => checkFragment test body && checkFragment test next
  def checkFragments {d : Dialect} (test : d.Op → Bool) {ss} : Regions d ss → Bool
    | .nil => true
    | .cons body rest => checkFragment test body && checkFragments test rest
end

theorem checkFragment_sound {d : Dialect} (test : d.Op → Bool) (allowed : d.Op → Prop)
    (law : ∀ op, test op = true → allowed op) {ts us} (body : Region d ts us)
    (checked : checkFragment test body = true) : Fragment allowed body := by
  induction body using Region.rec
      (motive_2 := fun _ bodies ↦ checkFragments test bodies = true → Fragments allowed bodies) with
  | ret => trivial
  | stop => trivial
  | letOp op args bodies next bodiesIH nextIH =>
    simp only [checkFragment, Bool.and_eq_true] at checked
    exact ⟨law op checked.1.1, bodiesIH checked.1.2, nextIH checked.2⟩
  | bind body next bodyIH nextIH =>
    simp only [checkFragment, Bool.and_eq_true] at checked
    exact ⟨bodyIH checked.1, nextIH checked.2⟩
  | nil => trivial
  | cons body rest bodyIH restIH =>
    rename_i checked
    simp only [checkFragments, Bool.and_eq_true] at checked
    exact ⟨bodyIH checked.1, restIH checked.2⟩

def checkMathOperation (op : Op) : Bool :=
  op.isCalculation || match op with | .mark _ => true | _ => false

theorem checkMathOperation_sound (op : Op) (checked : checkMathOperation op = true) :
    MathOperation op := by
  simp only [checkMathOperation, Bool.or_eq_true] at checked
  rcases checked with calculation | mark
  · exact .inl calculation
  · right
    cases op <;> simp_all

def checkOrdinaryOperation : ProtocolOp → Bool
  | .oracle .. => false
  | _ => true

theorem checkOrdinaryOperation_sound (op : ProtocolOp)
    (checked : checkOrdinaryOperation op = true) : OrdinaryOperation op := by
  cases op <;> simp_all [checkOrdinaryOperation, OrdinaryOperation]

/-- This inspects every retained definition and nested Region, including dormant ones. -/
def checkOrdinaryFragment (payload : UnitPayload) : Bool :=
  payload.definitions.all (fun definition ↦ definition.kind != .math ||
    checkFragment checkMathOperation definition.body) &&
  payload.protocols.all (fun definition ↦ checkFragment checkOrdinaryOperation definition.body)

theorem checkOrdinaryFragment_sound (payload : UnitPayload)
    (checked : checkOrdinaryFragment payload = true) : OrdinaryFragment payload := by
  simp only [checkOrdinaryFragment, Bool.and_eq_true, List.all_eq_true] at checked
  constructor
  · intro definition member math
    have body := checked.1 definition member
    simp only [math, bne_self_eq_false, Bool.false_or] at body
    exact checkFragment_sound _ _ checkMathOperation_sound _ body
  · intro definition member
    exact checkFragment_sound _ _ checkOrdinaryOperation_sound _ (checked.2 definition member)

/-- Canonical imported source, a computable fragment check, and no semantic premises. -/
theorem checked_imported_embedding {snapshot : Snapshot} (imported : Imported snapshot)
    (ordinarySource : snapshot.requiresOracleRuntime = false)
    (checked : checkOrdinaryFragment imported.program.payload = true)
    (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) imported.program.payload.entry.inputs) :
    (imported.program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers) =
      ((imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  imported_embedding imported ordinarySource (checkOrdinaryFragment_sound _ checked)
    model self inputs

/-- Source identity and the ordinary fragment are checked data, not authored denotations. -/
structure OrdinarySource (snapshot : Snapshot) where
  imported : Imported snapshot
  ordinary : snapshot.requiresOracleRuntime = false
  fragment : OrdinaryFragment imported.program.payload

/-- Canonical source admission followed by the finite ordinary-fragment check.
An Oracle source is refused before a witness of ordinary specialization can be returned. -/
def checkOrdinarySource (snapshot : Snapshot) : Except String (OrdinarySource snapshot) := do
  if ordinary : snapshot.requiresOracleRuntime = false then
    match admitted : Structured.check snapshot with
    | .error error => throw error
    | .ok program =>
      if checked : checkOrdinaryFragment program.payload = true then
        return ⟨⟨program, admitted⟩, ordinary, checkOrdinaryFragment_sound _ checked⟩
      else throw "ordinary-embedding-fragment"
  else throw "ordinary-embedding-oracle-source"

theorem OrdinarySource.embedding {snapshot : Snapshot} (source : OrdinarySource snapshot)
    (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    (source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers) =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  imported_embedding source.imported source.ordinary source.fragment model self inputs

/-- The checked source recovers its exact ordinary output and every stopped prefix. -/
theorem OrdinarySource.specialization {snapshot : Snapshot} (source : OrdinarySource snapshot)
    (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs) :
    ((source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers)).bind
        (fun result ↦ .done (ProtocolValue.concreteComponents result)) =
      (source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model) :=
  program_specialization source.imported.program model self source.fragment inputs

/-- No restriction is placed on public replies, handler stops, state or history. -/
theorem OrdinarySource.all_replies {snapshot : Snapshot} (source : OrdinarySource snapshot)
    (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) source.imported.program.payload.entry.inputs)
    {S E : Type} (handler : PIR.Handler (OracleProtocol.Interface model) S E) (state : S) :
    (((source.imported.program.oracleParticipant model self
      (ProtocolValue.embedComponents inputs)).interpret (eraseInternal model.toCarriers)).bind
        (fun result ↦ .done (ProtocolValue.concreteComponents result))).run handler state =
      ((source.imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).run handler state :=
  program_specialization_run source.imported.program model self source.fragment inputs handler state

end Zkc.Source.Structured.ProtocolEmbedding
