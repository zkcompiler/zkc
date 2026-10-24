module

public import Zkc.Construction.OriginalCorrespondence
public import ZkcSecurity.FiatShamir.DomainReduction
public import ZkcSecurity.Obligations.Derivation

@[expose] public section

/-! Consumption of complete original/artifact simulations. The endpoint reading
is transported from an existing reading and a checked simulation; it is not
an evaluator or an artifact instruction recognizer. Return relations remain
parameters of the full simulation, including its independent frame obligations.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Original
open Zkc.Source Zkc.Construction Zkc.Transcript
open DomainReduction

variable {I : PIR.Signature} {A B : Type}

/-- The same nominal operations, dependent replies and stops, with a relation
on complete returned values. There is no acceptance-only constructor. -/
inductive Alignment (returns : A → B → Prop) : PIR.Process I A → PIR.Process I B → Prop
  | done {a b} : returns a b → Alignment returns (.done a) (.done b)
  | halt (reason) : Alignment returns (.halt reason) (.halt reason)
  | call (operation : I.Op) {left : I.Reply operation → PIR.Process I A}
      {right : I.Reply operation → PIR.Process I B} :
      (∀ reply, Alignment returns (left reply) (right reply)) →
      Alignment returns (.call operation left) (.call operation right)

namespace Alignment
variable {E P : Type} {Raw : E → Type} {absorb : Interface I E P Raw}
  {returns : A → B → Prop} {left : PIR.Process I A} {right : PIR.Process I B}

/-- Every reached charge occurrence is retained, including repeated keys. -/
theorem cost (aligned : Alignment returns left right)
    {charge : List E → E → ENNReal} {history : List E} {budget : ENNReal}
    (bounded : Typed.ChargedCostBound absorb charge left history budget) :
    Typed.ChargedCostBound absorb charge right history budget := by
  induction aligned generalizing history budget with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
      ⟨event, decode⟩ | _
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact fun message value decoded => ih value (bounded message value decoded)
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact ih value bounded
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      obtain ⟨remaining, charged, suffix⟩ := bounded
      exact ⟨remaining, charged, fun value => ih value (suffix value)⟩
    · simp only [Typed.ChargedCostBound, absorbed]

/-- A local escape proof transports with its exact exceptional sets and
histories. Only the terminal consequence uses the full return relation. -/
theorem derivation {escape : Zkc.Transcript.EscapeJudgment E Raw}
    {Post : List E → A → Prop} {Next : List E → B → Prop} {history : List E}
    (proof : Zkc.Obligations.Derivation absorb escape Post history left)
    (aligned : Alignment returns left right)
    (terminal : ∀ reached a b, returns a b → Post reached a → Next reached b) :
    Nonempty (Zkc.Obligations.Derivation absorb escape Next history right) := by
  induction proof generalizing right with
  | done holds =>
    cases aligned with
    | done related => exact ⟨.done (terminal _ _ _ related holds)⟩
  | halt reason => cases aligned; exact ⟨.halt reason⟩
  | receive absorbed continuations ih =>
    cases aligned with
    | call operation next =>
      exact ⟨.receive absorbed fun message value decoded =>
        Classical.choice (ih message value decoded (next value))⟩
  | send absorbed continuation ih =>
    cases aligned with
    | call operation next => exact ⟨.send absorbed (Classical.choice (ih (next _)))⟩
  | query absorbed bad bounded continuations ih =>
    cases aligned with
    | call operation next =>
      exact ⟨.query absorbed bad bounded fun raw value decoded outside =>
        Classical.choice (ih raw value decoded outside (next value))⟩
  | refuse absorbed => cases aligned; exact ⟨.refuse absorbed⟩

end Alignment

variable {carriers : Structured.Carriers}
variable {returns : A → B → Prop}
variable {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
variable {source : PIR.Process (Domain.effects carriers) A}
variable {target : PIR.Process (Domain.effects carriers) B}

/-- Coherence follows every actual observation and query, retaining the
source's terminal fact and complete return relation. -/
theorem coherent (simulation : Zkc.Construction.Original.Simulation returns live source target)
    {Post : Domain.History carriers → A → Prop} {history : Domain.History carriers}
    (sourceCoherent : CoherentTo Post history source) :
    CoherentTo (fun reached b => ∃ a, Post reached a ∧ returns a b) history target := by
  induction simulation generalizing history with
  | done related =>
    cases sourceCoherent with
    | done history value holds => exact .done history _ ⟨_, holds, related⟩
  | halt reason => exact .halt history reason
  | call operation next ih =>
    cases sourceCoherent with
    | checkpoint environment suffix => exact .checkpoint environment (ih () suffix)
    | observe event suffix => exact .observe event (ih () suffix)
    | send site schema peer payload suffix => exact .send site schema peer payload (ih () suffix)
    | receive ty site schema peer next suffix =>
      exact .receive ty site schema peer _ (fun reply => ih reply (suffix reply))
    | query history origin next supported suffix =>
      exact .query history origin _ supported (fun reply => ih reply (suffix reply))
  | checkpoint frame related next ih => exact .checkpoint frame (ih sourceCoherent)

/-- Endpoint observation is a consequence of the complete simulation. This
uses the existing endpoint reading; the simulation itself still fixes all
operations, physical frames, full returns and failed/stopped prefixes. -/
theorem readExecution {C : Type}
    (simulation : Zkc.Construction.Original.Simulation returns live source target)
    (sourceView : A → C) (targetView : B → C)
    (agrees : ∀ a b, returns a b → sourceView a = targetView b)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (proof : Domain.Proof carriers) :
    (fun result => (mapOutcome targetView result.1, result.2)) <$>
        ZkcSecurity.Endpoint.Domain.readExecution query target proof =
      (fun result => (mapOutcome sourceView result.1, result.2)) <$>
        ZkcSecurity.Endpoint.Domain.readExecution query source proof := by
  induction simulation generalizing proof with
  | done related => simp [ZkcSecurity.Endpoint.Domain.readExecution, mapOutcome, agrees _ _ related]
  | halt reason => simp [ZkcSecurity.Endpoint.Domain.readExecution, mapOutcome]
  | checkpoint frame related next ih => exact ih proof
  | call operation next ih =>
    cases operation with
    | checkpoint => exact ih () proof
    | send => exact ih () proof
    | observe => exact ih () proof
    | localService => simp [ZkcSecurity.Endpoint.Domain.readExecution, mapOutcome]
    | receive ty site schema peer =>
      cases proof with
      | nil => simp [ZkcSecurity.Endpoint.Domain.readExecution, mapOutcome]
      | cons payload unread =>
        simp only [ZkcSecurity.Endpoint.Domain.readExecution]
        cases decoded : payload.value ty with
        | none => simp [mapOutcome]
        | some value => exact ih value unread
    | query history origin =>
      simp only [ZkcSecurity.Endpoint.Domain.readExecution]
      split
      · simp only [map_bind]
        exact congrArg (Bind.bind (query history (.challenge origin)))
          (funext fun raw => ih raw proof)
      · simp [mapOutcome]

/-- A relational nominal bridge consumes the already proved source reading
and the independent full artifact certificate. No root equality is assumed. -/
structure Bridge
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (Post : Domain.History carriers → A → Prop) (history : Domain.History carriers)
    (source : PIR.Process (Domain.effects carriers) A) (actual : PIR.Process (Domain.effects carriers) B)
    (presented : PIR.Process I A) (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop) where
  sourceReading : DomainReduction.Bridge absorb Post history source presented
  simulation : Zkc.Construction.Original.Simulation returns live source actual

namespace Bridge
variable {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {Post : Domain.History carriers → A → Prop} {history : Domain.History carriers}
variable {presented : PIR.Process I A}

/-- An exact existing bridge is a special case. Matched checkpoint operations
are retained on both sides; no live-frame premise is discarded or invented. -/
def ofExact (bridge : DomainReduction.Bridge absorb Post history source presented)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop) :
    Bridge absorb Post history source source presented Eq live where
  sourceReading := bridge
  simulation := identity source
where
  identity (process : PIR.Process (Domain.effects carriers) A) :
      Zkc.Construction.Original.Simulation Eq live process process :=
    match process with
    | .done _ => .done rfl
    | .halt reason => .halt reason
    | .call operation next => .call operation fun reply => identity (next reply)

/-- Exact computation image, with the same oracle and unread suffix. -/
theorem run {C : Type} (bridge : Bridge absorb Post history source target presented returns live)
    (sourceView : A → C) (targetView : B → C)
    (agrees : ∀ a b, returns a b → sourceView a = targetView b)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (proof : Domain.Proof carriers) :
    (fun result => (mapOutcome targetView result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution query target proof =
    (fun result => (mapOutcome sourceView result.1, result.2)) <$>
      transform absorb query presented history proof := by
  rw [readExecution bridge.simulation sourceView targetView agrees, bridge.sourceReading.reading.run]

/-- Observation coherence is also installed on the actual artifact. -/
theorem actualCoherent (bridge : Bridge absorb Post history source target presented returns live) :
    CoherentTo (fun reached b => ∃ a, Post reached a ∧ returns a b) history target :=
  coherent bridge.simulation bridge.sourceReading.coherent

end Bridge
end ZkcSecurity.FiatShamir.Original
