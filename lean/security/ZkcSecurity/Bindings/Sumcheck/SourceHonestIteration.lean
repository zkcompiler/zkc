module

public import ZkcSecurity.Bindings.Sumcheck.SourceIteration

@[expose] public section

/-! Honest symbolic repetition of the same actual source callback used by the
No/collision consumer. Concrete handler replies, states and event prefixes are
explicit; an honest rejection never satisfies the successful-return contract. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceIteration
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame H E : Type}

def honestMessage {n : Nat} (reference : PrefixState (model.Field field) Frame (n+1)) : model.Field field × model.Field field :=
  ((((layout model).entries reference).take (((layout model).entries reference).length/2)).sum,
    (((layout model).entries reference).drop (((layout model).entries reference).length/2)).sum)

/-- Six successful actual operations, with their exact residual handler state.
The challenge can depend on the reached handler state and earlier messages. -/
structure HonestTrace (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (ctx : ProtocolContext) (handle index : Nat) {n : Nat}
    (reference : PrefixState (model.Field field) Frame (n+1)) (initial : H) where
  challenge : model.Field field
  h1 : H
  h2 : H
  h3 : H
  h4 : H
  h5 : H
  final : H
  e0 : List E
  e1 : List E
  e2 : List E
  e3 : List E
  e4 : List E
  e5 : List E
  entered : handler (.enter ⟨repeatSite ctx, index⟩) initial = ⟨.returned (), h1, e0⟩
  low : handler (SourceRound.lowOp model ctx) h1 = ⟨.returned (honestMessage model reference).1, h2, e1⟩
  high : handler (SourceRound.highOp model ctx) h2 = ⟨.returned (honestMessage model reference).2, h3, e2⟩
  queried : handler (SourceRound.queryOp model ctx handle) h3 = ⟨.returned challenge, h4, e3⟩
  delivered : handler (SourceRound.deliveryOp model ctx challenge) h4 = ⟨.returned (), h5, e4⟩
  left : handler (.leave ⟨repeatSite ctx, index⟩) h5 = ⟨.returned (), final, e5⟩

def HonestTrace.events {handler : PIR.Handler (Occurrence.signature model.toCarriers) H E}
    {ctx : ProtocolContext} {handle index n : Nat}
    {reference : PrefixState (model.Field field) Frame (n+1)} {initial : H}
    (trace : HonestTrace model handler ctx handle index reference initial) : List E :=
  trace.e0 ++ (trace.e1 ++ (trace.e2 ++ (trace.e3 ++ (trace.e4 ++ trace.e5))))

private theorem advance_table {n : Nat} (reference : PrefixState (model.Field field) Frame (n+1))
    (message : model.Field field × model.Field field) (r : model.Field field) :
    (layout model).table (reference.advance message r) =
      (TableReference.data (model.Field field)).restrict ((layout model).table reference) r := by
  apply Option.some.inj
  rw [← (layout model).decoded]
  change Zkc.Polynomial.Multilinear.ofList? n (reference.advance message r).entries = _
  rw [PrefixState.advance_entries]
  exact Zkc.Polynomial.Multilinear.ofList?_restrictValues _ _ r ((layout model).decoded reference)

theorem advance_yes {n : Nat} (reference : PrefixState (model.Field field) Frame (n+1))
    (r : model.Field field) :
    (layout model).representation.Yes (reference.advance (honestMessage model reference) r) := by
  have delivered := SourceRound.producer_polynomial model (layout model) reference
  have math := honest_round TableReference.laws Message.endpoints_laws
    ((layout model).table reference) trivial (honestMessage model reference) delivered r r rfl
  change True ∧ _
  refine ⟨trivial, ?_⟩
  change (Message.endpoints (model.Field field)).evaluate (honestMessage model reference) r =
    (TableReference.data (model.Field field)).total ((layout model).table (reference.advance _ r))
  rw [advance_table model]
  exact math.2.1

variable (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
  (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
  (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat)
include linked bodies distinct

theorem honest_step_run {n : Nat} (index : Nat)
    (reference : PrefixState (model.Field field) Frame (n+1))
    (yes : (layout model).representation.Yes reference)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E) (initial : H)
    (trace : HonestTrace model handler ctx handle index reference initial) :
    (step model definitions protocols ctx handle (encode model index reference)).run handler initial =
      ⟨.returned (encode model (index+1)
        (reference.advance (honestMessage model reference) trace.challenge)), trace.final, trace.events⟩ := by
  have delivered := SourceRound.producer_polynomial model (layout model) reference
  have math := honest_round TableReference.laws Message.endpoints_laws
    ((layout model).table reference) trivial (honestMessage model reference) delivered
    trace.challenge trace.challenge rfl
  have checked : reference.scalar = (honestMessage model reference).1 + (honestMessage model reference).2 :=
    yes.2.trans math.1.symm
  simp only [step, Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [round_reference model definitions linked bodies protocols ctx distinct handle]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, encode,
    SumcheckReferenceInstallation.reference, PIR.Process.run, trace.entered,
    trace.low, trace.high, checked, ↓reduceIte, trace.queried, trace.delivered, trace.left,
    PIR.Execution.follow, List.append_nil]
  rfl

/-- Handler synchronization is separate from table truth and source shape. -/
def honest (good : List E → Runtime model Frame → H → Prop)
    (original : List (model.Field field)) (callerFrame : Frame)
    (history : List E) (n : Nat) (runtime : Runtime model Frame) (handlerState : H) : Prop :=
  ∃ reference : PrefixState (model.Field field) Frame n,
    reference.original = original ∧ reference.frame = callerFrame ∧
      runtime = encode model runtime.index reference ∧
      (layout model).representation.Yes reference ∧ good history runtime handlerState

/-- Ordinary successful handler laws suffice; no whole-source equation is a
premise. The stop postcondition of this contract is literally False. -/
theorem honest_contract (original : List (model.Field field)) (callerFrame : Frame)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (schedule : ∀ reached n index (reference : PrefixState (model.Field field) Frame (n+1)) h,
      reference.original = original → reference.frame = callerFrame →
      (layout model).representation.Yes reference → good reached (encode model index reference) h →
      ∃ trace : HonestTrace model handler ctx handle index reference h,
        good (reached ++ trace.events)
          (encode model (index+1) (reference.advance (honestMessage model reference) trace.challenge)) trace.final) :
    RepeatedComponent.HonestContract (component model definitions protocols ctx handle) handler
      (honest model good original callerFrame) := by
  intro history n runtime h valid
  obtain ⟨reference, same, retained, encoded, yes, valid⟩ := valid
  rw [encoded] at valid ⊢
  obtain ⟨trace, next⟩ := schedule history n runtime.index reference h same retained yes valid
  change PIR.WeakestPrecondition.satisfies
    ((step model definitions protocols ctx handle (encode model runtime.index reference)).run handler h) _ _ _
  rw [honest_step_run model definitions linked bodies protocols ctx distinct handle runtime.index reference yes handler h trace]
  exact ⟨reference.advance (honestMessage model reference) trace.challenge, same, retained, rfl,
    advance_yes model reference trace.challenge, next⟩

omit linked bodies distinct in
theorem honest_repeat (original : List (model.Field field)) (callerFrame : Frame)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract (component model definitions protocols ctx handle) handler
      (honest model good original callerFrame))
    (count : Nat) (history : List E) (runtime : Runtime model Frame) (h : H)
    (initial : honest model good original callerFrame history count runtime h) :
    PIR.WeakestPrecondition.satisfies
      ((PIR.repeatN count (step model definitions protocols ctx handle) runtime).run handler h)
      (fun returned final reached => honest model good original callerFrame reached 0 returned final)
      (fun _ _ _ => False) history :=
  RepeatedComponent.honest_repeatN _ handler _ steps count history runtime h initial

end ZkcSecurity.Realizations.Sumcheck.SourceIteration
