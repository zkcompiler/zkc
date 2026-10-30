module

public import ZkcSecurity.Bindings.Participants.DomainExecutionProjection
public import Zkc.Transcript.Interface

@[expose] public section

/-! A checked handler reading of an existing nominal Domain Process into the
existing transcript transform. This is a proof relation, not an evaluator.
Every query must use precisely the accumulated history and nominal origin.
The separate DomainCoherence module checks actual observation prefixes.
Silent checkpoints and observations retain their operational meaning in the
whole Process binding; this reading concerns outcome and unread proof only.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction Zkc.Transcript

variable {carriers : Structured.Carriers} {I : PIR.Signature} {A B : Type}

inductive ReadingTo
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (Post : Domain.History carriers → A → Prop) :
    Domain.History carriers → PIR.Process (Domain.effects carriers) A → PIR.Process I A → Prop
  | done (history) (value : A) : Post history value → ReadingTo absorb Post history (.done value) (.done value)
  | halt (history) (reason : PIR.Stop) :
      ReadingTo absorb Post history (.halt reason) (.halt reason)
  | checkpoint {history left right} (environment : Domain.Environment carriers) :
      ReadingTo absorb Post history left right →
      ReadingTo absorb Post history (.call (.checkpoint environment) (fun _ => left)) right
  | observe {history left right} (event : Domain.Event carriers) :
      ReadingTo absorb Post history left right →
      ReadingTo absorb Post history (.call (.observe event) (fun _ => left)) right
  | send {history left right} (site schema peer : String) (payload : Domain.Payload carriers) :
      ReadingTo absorb Post history left right →
      ReadingTo absorb Post history (.call (.send site schema peer payload) (fun _ => left)) right
  | absorbSend {history left} (operation : I.Op)
      (next : I.Reply operation → PIR.Process I A)
      (event : Domain.Event carriers) (value : I.Reply operation)
      (absorbed : absorb operation = .send event value) :
      ReadingTo absorb Post (history ++ [event]) left (next value) →
      ReadingTo absorb Post history left (.call operation next)
  | receive {history} (ty : Structured.Ty) (site schema peer : String)
      (left : carriers.Value ty → PIR.Process (Domain.effects carriers) A)
      (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
      (event : Domain.Payload carriers → Domain.Event carriers)
      (recover : Domain.Event carriers → Option (I.Reply operation))
      (reply : carriers.Value ty → I.Reply operation)
      (absorbed : absorb operation = .receive event recover)
      (decoded : ∀ payload, recover (event payload) = (payload.value ty).map reply) :
      (∀ payload value, payload.value ty = some value →
        ReadingTo absorb Post (history ++ [event payload]) (left value) (next (reply value))) →
      ReadingTo absorb Post history (.call (.receive ty site schema peer) left)
        (.call operation next)
  | query (history : Domain.History carriers) (origin : Origin)
      (left : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) A)
      (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
      (reply : Domain.Raw (.challenge origin : Domain.Event carriers) → I.Reply operation)
      (supported : Domain.drawRequest origin = true)
      (absorbed : absorb operation = .query (.challenge origin) (some ∘ reply)) :
      (∀ raw, ReadingTo absorb Post (history ++ [.challenge origin])
        (left raw) (next (reply raw))) →
      ReadingTo absorb Post history (.call (.query history origin) left) (.call operation next)

namespace ReadingTo

/-- Weaken a returned-state fact while retaining the identical checked effects,
query keys, nominal decoders and continuations. -/
theorem weaken
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    {Post Next : Domain.History carriers → A → Prop}
    {history : Domain.History carriers} {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process I A} (reading : ReadingTo absorb Post history left right)
    (implies : ∀ reached value, Post reached value → Next reached value) :
    ReadingTo absorb Next history left right := by
  induction reading with
  | done history value holds => exact .done history value (implies history value holds)
  | halt history reason => exact .halt history reason
  | checkpoint environment _ ih => exact .checkpoint environment ih
  | observe event _ ih => exact .observe event ih
  | send site schema peer payload _ ih => exact .send site schema peer payload ih
  | absorbSend operation next event value absorbed _ ih =>
      exact .absorbSend operation next event value absorbed ih
  | receive ty site schema peer left operation next event recover reply absorbed decoded _ ih =>
      exact .receive ty site schema peer left operation next event recover reply absorbed decoded ih
  | query history origin left operation next reply supported absorbed _ ih =>
      exact .query history origin left operation next reply supported absorbed ih

/-- Actual proof decoding and explicit-history queries agree in every monad.
This equality transfers both ordinary and complete acceptance, including all
malformed proof heads, stopped paths, and unread suffixes. -/
theorem run
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    {Post : Domain.History carriers → A → Prop}
    {history : Domain.History carriers} {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process I A} (reading : ReadingTo absorb Post history left right)
    {m : Type → Type} [Monad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (proof : Domain.Proof carriers) :
    ZkcSecurity.Endpoint.Domain.readExecution query left proof =
      Zkc.Transcript.transform absorb query right history proof := by
  induction reading generalizing proof with
  | done => rfl
  | halt => rfl
  | checkpoint environment reading ih => exact ih proof
  | observe event reading ih => exact ih proof
  | send site schema peer payload reading ih => exact ih proof
  | absorbSend operation next event value absorbed reading ih =>
      rw [transform_send absorb query absorbed]
      exact ih proof
  | receive ty site schema peer left operation next event recover reply absorbed decoded reading ih =>
      cases proof with
      | nil => simp only [ZkcSecurity.Endpoint.Domain.readExecution, Zkc.Transcript.transform, absorbed]
      | cons payload unread =>
          simp only [ZkcSecurity.Endpoint.Domain.readExecution, Zkc.Transcript.transform, absorbed, decoded]
          cases head : payload.value ty with
          | none => rfl
          | some value => exact ih payload value head unread
  | query history origin left operation next reply supported absorbed reading ih =>
      simp only [ZkcSecurity.Endpoint.Domain.readExecution, supported, ite_true,
        Zkc.Transcript.transform, absorbed, Function.comp_apply]
      exact congrArg (fun continuation => query history (.challenge origin) >>= continuation)
        (funext fun raw => ih raw proof)

/-- Sequential continuation reading carries full returned data to both callers;
the next child's proof starts at the reached transcript history. -/
theorem bind
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    {Post : Domain.History carriers → A → Prop}
    {history : Domain.History carriers} {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process I A} (reading : ReadingTo absorb Post history left right)
    {PostNext : Domain.History carriers → B → Prop}
    (nextLeft : A → PIR.Process (Domain.effects carriers) B)
    (nextRight : A → PIR.Process I B)
    (next : ∀ reached value, Post reached value →
      ReadingTo absorb PostNext reached (nextLeft value) (nextRight value)) :
    ReadingTo absorb PostNext history (left.bind nextLeft) (right.bind nextRight) := by
  induction reading with
  | done history value holds => exact next history value holds
  | halt history reason => exact .halt history reason
  | checkpoint environment _ ih => exact .checkpoint environment ih
  | observe event _ ih => exact .observe event ih
  | send site schema peer payload _ ih => exact .send site schema peer payload ih
  | absorbSend operation after event value absorbed _ ih =>
      exact .absorbSend operation _ event value absorbed ih
  | receive ty site schema peer left operation after event recover reply absorbed decoded _ ih =>
      exact .receive ty site schema peer _ operation _ event recover reply absorbed decoded ih
  | query history origin left operation after reply supported absorbed _ ih =>
      exact .query history origin _ operation _ reply supported absorbed ih

/-- History-indexed loop invariants are carried through each returned state.
The zero case is a checked return and performs no effects. -/
theorem repeatN
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    (invariant : Domain.History carriers → Nat → A → Prop)
    (left : A → PIR.Process (Domain.effects carriers) A)
    (right : A → PIR.Process I A)
    (body : ∀ history remaining value, invariant history (remaining + 1) value →
      ReadingTo absorb (fun reached => invariant reached remaining) history
        (left value) (right value))
    (count : Nat) (history : Domain.History carriers) (value : A)
    (holds : invariant history count value) :
    ReadingTo absorb (fun reached => invariant reached 0) history
      (PIR.repeatN count left value) (PIR.repeatN count right value) := by
  induction count generalizing history value with
  | zero => exact .done history value holds
  | succ count ih => exact (body history count value holds).bind _ _ ih

/-- The actual constructed loop keeps immutable captures, indices, yielded
references and sort checks. The body law is needed at every adaptive carried
state; a failed read/sort check preserves the actual refusal. -/
theorem iterate
    {absorb : Interface (Domain.effects carriers) (Domain.Event carriers)
      (Domain.Payload carriers) Domain.Raw}
    (left right : Domain.Environment carriers →
      PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (outer : Domain.Environment carriers) (yielded : List Nat)
    (declared : List ValueSort)
    (invariant : Domain.History carriers → List Nat → Domain.Environment carriers → Prop)
    (body : ∀ history index rest carried, invariant history (index :: rest) carried →
      ReadingTo absorb
        (fun reached final => ∀ next, Domain.read final yielded = some next →
          Domain.sortsMatch declared next = true → invariant reached rest next)
        history (left (outer ++ .data (.index index) :: carried))
          (right (outer ++ .data (.index index) :: carried)))
    (indices : List Nat) (history : Domain.History carriers) (carried : Domain.Environment carriers)
    (holds : invariant history indices carried) :
    ReadingTo absorb (fun reached => invariant reached []) history
      (Domain.iterate left outer yielded declared indices carried)
      (Domain.iterate right outer yielded declared indices carried) := by
  induction indices generalizing history carried with
  | nil => exact .done history carried holds
  | cons index rest ih =>
    apply (body history index rest carried holds).bind
    intro reached final preserved
    cases found : Domain.read final yielded with
    | none => exact .halt reached .refused
    | some next =>
      dsimp only
      split
      · exact ih reached next (preserved next found (by assumption))
      · exact .halt reached .refused

/-- This is precisely the endpoint projection of the actual handler. The full
execution and its state/events remain owned by Domain.run. -/
theorem handler
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    {Post : Domain.History carriers → A → Prop}
    {history : Domain.History carriers} {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process I A} (reading : ReadingTo absorb Post history left right)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (state : Domain.RuntimeState carriers Unit) :
    (fun result => (result.outcome, result.state.proof)) <$>
      Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle query) left state =
        Zkc.Transcript.transform absorb query right history state.proof := by
  rw [ZkcSecurity.Endpoint.Domain.readExecution_eq]
  exact reading.run query state.proof

end ReadingTo

/-- The unrefined endpoint reading. Use ReadingTo for history-dependent bind
and loop seams. -/
abbrev Reading
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw) :=
  ReadingTo (A := A) absorb (fun _ _ => True)

end ZkcSecurity.FiatShamir.DomainReduction
