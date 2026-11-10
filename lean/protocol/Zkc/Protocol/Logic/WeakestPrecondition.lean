module

public import Zkc.Protocol.Construction.Truth
public import Zkc.Protocol.Obligations.Bounded
public import Zkc.Protocol.Logic.Transcript.Interface
public import Std.WP
public import Std.Tactic.Do

@[expose] public section

/-! Proposition-valued interpretations of the existing validator process.
The charged reading certifies rejection with abstract escape obligations; the
cost reading bounds every admissible path, including history-dependent prices.
They share the process, not a global WP instance. Each is a local `WPMonad`
whose assertions are `ProtocolProof.Truth`, so the common constructor composes
them as it composes quantitative potentials. The folds `chargedWP`, `costWP`
and `costNode` are the semantic content; adequacy below connects each reading
to its existing judgment, so endpoint statements never mention the carrier.
Stops are explicit exception postconditions; allowing a stop in rejection or
cost does not establish honest completeness.
-/

set_option autoImplicit false
namespace ZkcSecurity.Obligations.WeakestPrecondition
open Std.WP Lean.Order Zkc.Transcript Zkc.Obligations ZkcSecurity.FiatShamir ProtocolProof

variable {I : PIR.Signature} {E P : Type} {Raw : E → Type}

/-- The process constructors are definitionally the monad operations. These
specs let vcgen consume imported process syntax without unfolding recursion. -/
@[spec] theorem done_spec {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (PIR.Process I) Pred EPred] {A : Type} (value : A)
    (post : A → Pred) (epost : EPred) :
    Triple (PIR.Process.done value : PIR.Process I A) (post value) post epost :=
  Spec.pure (m := PIR.Process I) (post := post) (epost := epost) value

@[spec] theorem bind_spec {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (PIR.Process I) Pred EPred] {A B : Type} (process : PIR.Process I A)
    (next : A → PIR.Process I B) (post : B → Pred) (epost : EPred) :
    Triple (process.bind next) (wp process (fun value => wp (next value) post epost) epost) post epost :=
  Spec.bind process next

/-! ## The charged reading -/

/-- The charged reading with the stop postcondition exposed as an exception postcondition:
`halt reason` reads as `epost.1 reason`. zkc's `Charged` is the instance `epost.1 = ⊤`. -/
def chargedWP (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw) {A : Type}
    (process : PIR.Process I A) (post : A → List E → Prop)
    (epost : EStack⟨PIR.Stop → List E → Prop⟩) : List E → Prop :=
  process.foldReplies post epost.1 fun operation next => (absorb operation).ChargedNode escape next

theorem chargedWP_mono (absorb : Interface I E P Raw) {escape : EscapeJudgment E Raw}
    (antitone : escape.Antitone) {A : Type} (process : PIR.Process I A)
    {post post' : A → List E → Prop} {epost epost' : EStack⟨PIR.Stop → List E → Prop⟩}
    (stops : ∀ reason history, epost.1 reason history → epost'.1 reason history)
    (returns : ∀ value history, post value history → post' value history) :
    chargedWP absorb escape process post epost ≤ chargedWP absorb escape process post' epost' :=
  PIR.Process.foldReplies_mono (absorb.chargedNode_monotone antitone)
    (fun value reached inside => returns value reached inside)
    (fun reason reached inside => stops reason reached inside) process

theorem chargedWP_bind (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    {A B : Type} (x : PIR.Process I A) (f : A → PIR.Process I B) post epost :
    chargedWP absorb escape (x.bind f) post epost =
      chargedWP absorb escape x (fun a => chargedWP absorb escape (f a) post epost) epost :=
  PIR.Process.foldReplies_bind _ _ _ x f

/-- The charged weakest-precondition monad on proposition-valued assertions. `absorb` and
`escape` are not determined by the program type, so this is a definition to be installed as a
local instance. Every escape judgment gives an instance; the endpoints use the exact judgment
below and the bounded judgment of `Zkc.Protocol.Obligations.Bounded`. The definition is
instance-reducible, so a client's instance unifies with the primitive rules below argument by
argument, including the antitonicity proof. -/
@[instance_reducible] noncomputable def chargedMonad (absorb : Interface I E P Raw)
    (escape : EscapeJudgment E Raw) (antitone : escape.Antitone) :
    WPMonad (PIR.Process I) (Assert E) (StopAssert E) where
  toWP _ := {
    wpTrans := fun process => ⟨fun post stopped history =>
      ⟨chargedWP absorb escape process (fun value reached => (post value reached).holds)
        estack⟨fun reason reached => (stopped.1 reason reached).holds⟩ history⟩⟩
    wp_trans_monotone := fun process _ _ _ _ stops returns history =>
      chargedWP_mono absorb antitone process (fun reason reached => stops.1 reason reached)
        (fun value reached => returns value reached) history }
  pure_le_wp_pure _ _ _ := fun _ holds => holds
  bind_le_wp_bind process next post stopped := by
    intro history holds
    change chargedWP absorb escape (process.bind next) _ _ history
    rw [chargedWP_bind]
    exact holds

/-- A charged triple, under the local instance of `absorb` and `escape`. -/
abbrev ChargedTriple (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    (antitone : escape.Antitone) {A : Type} (process : PIR.Process I A) (pre : Assert E)
    (post : A → Assert E) (stopped : StopAssert E) : Prop :=
  letI := chargedMonad absorb escape antitone
  Triple process pre post stopped

section Adequacy
variable (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
  (antitone : escape.Antitone)

/-- Adequacy, part 1: the WP at the soundness stop postcondition is zkc's `Charged`. -/
theorem wp_eq_charged {A : Type} (Post : List E → A → Prop) (process : PIR.Process I A)
    (history : List E) :
    (letI := chargedMonad absorb escape antitone
     wp process (fun value reached => ⟨Post reached value⟩) estack⟨fun _ _ => ⟨True⟩⟩ history).holds =
      absorb.Charged escape Post process history := rfl

/-- Adequacy, part 2: a triple with the soundness stop postcondition is exactly a
`Derivation` from every history satisfying the precondition. -/
theorem triple_iff_derivation {A : Type} (pre : Assert E) (Post : List E → A → Prop)
    (process : PIR.Process I A) :
    ChargedTriple absorb escape antitone process pre (fun value reached => ⟨Post reached value⟩)
        estack⟨fun _ _ => ⟨True⟩⟩ ↔
      ∀ history, (pre history).holds → Nonempty (Derivation absorb escape Post history process) := by
  let := chargedMonad absorb escape antitone
  constructor
  · intro triple history holds
    exact (Derivation.nonempty_iff_charged antitone).mpr (triple.le_wp history holds)
  · intro derive
    exact ⟨fun history holds => (Derivation.nonempty_iff_charged antitone).mp (derive history holds)⟩

/-- Adequacy in the form endpoints consume. A triple whose postcondition is `Post` gives the
charged reading from every history satisfying its precondition; a stronger stop postcondition
only weakens to the soundness one. -/
theorem charged_of_triple {A : Type} {process : PIR.Process I A} {pre : Assert E}
    {Post : List E → A → Prop} {stopped : StopAssert E}
    (triple : ChargedTriple absorb escape antitone process pre
      (fun value reached => ⟨Post reached value⟩) stopped)
    (history : List E) (holds : (pre history).holds) :
    absorb.Charged escape Post process history := by
  let := chargedMonad absorb escape antitone
  exact chargedWP_mono absorb antitone process (post' := fun value reached => Post reached value)
    (epost' := estack⟨fun _ _ => True⟩) (fun _ _ _ => trivial) (fun _ _ inside => inside) history
    (triple.le_wp history holds)

/-- Recover the existing proof object from a checked triple. This does not run
proof search or choose a knowledge extractor. -/
noncomputable def ofTriple {A : Type} {pre : Assert E} {Post : List E → A → Prop}
    {process : PIR.Process I A}
    (proof : ChargedTriple absorb escape antitone process pre
      (fun value reached => ⟨Post reached value⟩) estack⟨fun _ _ => ⟨True⟩⟩)
    (history : List E) (holds : (pre history).holds) : Derivation absorb escape Post history process :=
  Classical.choice ((triple_iff_derivation absorb escape antitone pre Post process).mp proof history holds)

end Adequacy

section ChargedSpecs
variable (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
  (antitone : escape.Antitone)

/-- The primitive call rule of every charged reading: the precondition is the node obligation of
the operation's absorption. One rule serves every interface and escape judgment. -/
@[spec] theorem call_spec (operation : I.Op) (post : I.Reply operation → Assert E)
    (stopped : StopAssert E) :
    @Triple _ _ _ _ _ _ (PIR.Process.call operation .done)
      ((chargedMonad absorb escape antitone).toWP (I.Reply operation))
      (fun history => ⟨(absorb operation).ChargedNode escape
        (fun reply reached => (post reply reached).holds) history⟩) post stopped := by
  let := chargedMonad absorb escape antitone
  exact ⟨fun _ holds => holds⟩

/-- A stop reads as the stop postcondition. -/
@[spec] theorem halt_spec {A : Type} (reason : PIR.Stop) (post : A → Assert E)
    (stopped : StopAssert E) :
    @Triple _ _ _ _ _ _ (PIR.Process.halt reason : PIR.Process I A)
      ((chargedMonad absorb escape antitone).toWP A) (stopped.1 reason) post stopped := by
  let := chargedMonad absorb escape antitone
  exact ⟨fun _ holds => holds⟩

/-- Reuse a component's checked contract as a WP specification. The returned
value and the reached history remain available to the continuation. -/
theorem derivation_spec {A : Type} (process : PIR.Process I A)
    (pre : Assert E) (Post : List E → A → Prop)
    (derive : ∀ history, (pre history).holds → Derivation absorb escape Post history process) :
    ChargedTriple absorb escape antitone process pre (fun value reached => ⟨Post reached value⟩)
      estack⟨fun _ _ => ⟨True⟩⟩ :=
  (triple_iff_derivation absorb escape antitone pre Post process).mpr
    fun history holds => ⟨derive history holds⟩

/-- A received value is arbitrary subject only to the actual recovery equation. -/
theorem receive_spec (operation : I.Op) (event : P → E)
    (recover : E → Option (I.Reply operation))
    (absorbed : absorb operation = .receive event recover)
    (post : I.Reply operation → Assert E) (stopped : StopAssert E) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => ⟨∀ message value, recover (event message) = some value →
        (post value (history ++ [event message])).holds⟩) post stopped := by
  let := chargedMonad absorb escape antitone
  refine ⟨fun history holds => ?_⟩
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  exact holds

/-- Sending changes the transcript even though it consumes no proof message. -/
theorem send_spec (operation : I.Op) (event : E) (value : I.Reply operation)
    (absorbed : absorb operation = .send event value)
    (post : I.Reply operation → Assert E) (stopped : StopAssert E) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => post value (history ++ [event])) post stopped := by
  let := chargedMonad absorb escape antitone
  refine ⟨fun history holds => ?_⟩
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  exact holds

/-- The cut is a raw-answer event, fixed before this query. All successful
actual decodings outside the cut must satisfy the continuation. -/
theorem query_spec (operation : I.Op) (event : E)
    (decode : Raw event → Option (I.Reply operation))
    (absorbed : absorb operation = .query event decode) (bad : Raw event → Prop)
    (post : I.Reply operation → Assert E) (stopped : StopAssert E) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => ⟨escape history event bad ∧ ∀ raw value, decode raw = some value → ¬ bad raw →
        (post value (history ++ [event])).holds⟩) post stopped := by
  let := chargedMonad absorb escape antitone
  refine ⟨fun history holds => ?_⟩
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  refine antitone history event _ bad ?_ holds.1
  rintro raw ⟨value, decoded, outside⟩
  exact Classical.byContradiction fun good => outside (holds.2 raw value decoded good)

/-- An invariant specification for bounded loops; the zero case is a separate
postcondition, so no body assumption can be used for an empty loop. -/
theorem repeat_spec {A : Type} (step : A → PIR.Process I A)
    (invariant : Nat → A → Assert E)
    (body : ∀ remaining value, ChargedTriple absorb escape antitone (step value)
      (invariant (remaining + 1) value) (invariant remaining) estack⟨fun _ _ => ⟨True⟩⟩)
    (count : Nat) (value : A) :
    ChargedTriple absorb escape antitone (PIR.repeatN count step value) (invariant count value)
      (invariant 0) estack⟨fun _ _ => ⟨True⟩⟩ := by
  let := chargedMonad absorb escape antitone
  refine ⟨fun history holds => ?_⟩
  have preserved : ∀ remaining value,
      (fun reached => (invariant (remaining + 1) value reached).holds) ≤
        (step value).foldReplies (fun value reached => (invariant remaining value reached).holds)
          (fun _ _ => True) fun operation next => (absorb operation).ChargedNode escape next :=
    fun remaining value reached inside => (body remaining value).le_wp reached inside
  exact PIR.Process.le_foldReplies_repeatN (absorb.chargedNode_monotone antitone) step
    (fun remaining value reached => (invariant remaining value reached).holds) preserved
    count value history holds

end ChargedSpecs

/-! ## The exact reading

The exact reading is the charged reading at the escape judgment that excludes no reply. Its
triples hold on every run, for every reply: their postconditions characterize the returned value
and the reached history of every returning run. -/

section Exact

/-- No reply may be excluded at a query. -/
def exactEscape : EscapeJudgment E Raw := fun _ _ bad => ∀ raw, ¬ bad raw

theorem exactEscape_antitone : (exactEscape (E := E) (Raw := Raw)).Antitone :=
  fun _ _ _ _ included none raw smaller => none raw (included raw smaller)

/-- One node of the charged reading is monotone in the escape judgment. -/
theorem chargedNode_mapEscape {Reply : Type} {escape target : EscapeJudgment E Raw}
    (antitone : target.Antitone)
    (law : ∀ history event bad, escape history event bad → target history event bad)
    (absorption : Absorption E P Raw Reply) {lower upper : Reply → List E → Prop}
    (included : ∀ reply history, lower reply history → upper reply history) (history : List E)
    (holds : absorption.ChargedNode escape lower history) :
    absorption.ChargedNode target upper history := by
  cases absorption with
  | receive event recover =>
      exact fun message value recovered => included _ _ (holds message value recovered)
  | send event value => exact included _ _ holds
  | query event decode =>
      refine antitone history event _ _ ?_ (law history event _ holds)
      rintro raw ⟨value, decoded, outside⟩
      exact ⟨value, decoded, fun inside => outside (included _ _ inside)⟩
  | refuse => trivial

/-- The charged reading is monotone in its escape judgment. -/
theorem charged_mapEscape (absorb : Interface I E P Raw) {escape target : EscapeJudgment E Raw}
    (antitone : target.Antitone)
    (law : ∀ history event bad, escape history event bad → target history event bad)
    {A : Type} (Post : List E → A → Prop) :
    ∀ (process : PIR.Process I A) (history : List E),
      absorb.Charged escape Post process history → absorb.Charged target Post process history
  | .done _, _, holds => holds
  | .halt _, _, holds => holds
  | .call operation next, history, holds =>
      chargedNode_mapEscape antitone law (absorb operation)
        (fun reply after inside => charged_mapEscape absorb antitone law Post (next reply) after inside)
        history holds

/-- Exact evidence is charged evidence for every antitone judgment that accepts the empty
exceptional event. -/
theorem charged_of_exact (absorb : Interface I E P Raw) {target : EscapeJudgment E Raw}
    (antitone : target.Antitone) (empty : ∀ history event, target history event fun _ => False)
    {A : Type} {Post : List E → A → Prop} {process : PIR.Process I A} {history : List E}
    (holds : absorb.Charged exactEscape Post process history) :
    absorb.Charged target Post process history :=
  charged_mapEscape absorb antitone
    (fun history event bad none => antitone history event bad (fun _ => False)
      (fun raw inside => none raw inside) (empty history event))
    Post process history holds

/-- Exact evidence is charged evidence for every bounded judgment: an empty exceptional event
has probability zero. -/
theorem bounded_of_exact [∀ event, SampleableType (Raw event)] (absorb : Interface I E P Raw)
    (charge : List E → E → ENNReal) {A : Type} {Post : List E → A → Prop}
    {process : PIR.Process I A} {history : List E}
    (holds : absorb.Charged exactEscape Post process history) :
    absorb.Charged (boundedEscape charge) Post process history :=
  charged_of_exact absorb (boundedEscape_antitone charge)
    (fun history event => by
      change Pr{let _ ← $ᵗ (Raw event)}[False] ≤ charge history event
      simp) holds

end Exact

/-! ## Node obligations

What remains of a primitive call after construction is the node obligation of its absorption.
These equations state it for each absorption kind; under the exact judgment a query constrains
every decoded reply, and under a bounded judgment it is a probability bound for the replies that
escape. -/

section Nodes
variable {Reply : Type} (escape : EscapeJudgment E Raw) (next : Reply → List E → Prop)
  (history : List E)

theorem chargedNode_receive (event : P → E) (recover : E → Option Reply) :
    (Absorption.receive event recover : Absorption E P Raw Reply).ChargedNode escape next history =
      ∀ message value, recover (event message) = some value →
        next value (history ++ [event message]) := rfl

theorem chargedNode_send (event : E) (value : Reply) :
    (Absorption.send event value : Absorption E P Raw Reply).ChargedNode escape next history =
      next value (history ++ [event]) := rfl

/-- A query under any escape judgment: the judgment of the decoded replies whose continuation
fails. `chargedNode_query_exact` and `chargedNode_query_bounded` state it at the two judgments the
endpoints use; a reading at another judgment can register this form locally. -/
theorem chargedNode_query (event : E) (decode : Raw event → Option Reply) :
    (Absorption.query event decode : Absorption E P Raw Reply).ChargedNode escape next history =
      escape history event fun raw => ∃ value, decode raw = some value ∧
        ¬ next value (history ++ [event]) := rfl

theorem chargedNode_refuse :
    (Absorption.refuse : Absorption E P Raw Reply).ChargedNode escape next history = True := rfl

theorem chargedNode_query_exact (event : E) (decode : Raw event → Option Reply) :
    (Absorption.query event decode : Absorption E P Raw Reply).ChargedNode exactEscape next
        history =
      ∀ raw value, decode raw = some value → next value (history ++ [event]) := by
  refine propext ⟨fun none raw value decoded => ?_, fun every raw escaped => ?_⟩
  · exact Classical.byContradiction fun outside => none raw ⟨value, decoded, outside⟩
  · obtain ⟨value, decoded, outside⟩ := escaped
    exact outside (every raw value decoded)

/-- Under a bounded judgment a query is a probability bound for the replies that escape. -/
theorem chargedNode_query_bounded [∀ event, SampleableType (Raw event)]
    (charge : List E → E → ENNReal) (event : E) (decode : Raw event → Option Reply) :
    (Absorption.query event decode : Absorption E P Raw Reply).ChargedNode (boundedEscape charge)
        next history =
      (Pr{let raw ← $ᵗ (Raw event)}[∃ value, decode raw = some value ∧
        ¬ next value (history ++ [event])] ≤ charge history event) := rfl

end Nodes

/-! ## The cost reading -/

/-- One node of the cost reading; the assertion state is (history, remaining budget). -/
def costNode (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) (operation : I.Op)
    (next : I.Reply operation → List E → ENNReal → Prop) (history : List E) (cost : ENNReal) : Prop :=
  match absorb operation with
  | .receive event recover =>
      ∀ message value, recover (event message) = some value → next value (history ++ [event message]) cost
  | .send event value => next value (history ++ [event]) cost
  | .query event _ =>
      ∃ remaining, charge history event + remaining ≤ cost ∧ ∀ value, next value (history ++ [event]) remaining
  | .refuse => True

def costWP (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) {A : Type}
    (process : PIR.Process I A) (post : A → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) : List E → ENNReal → Prop :=
  process.foldReplies post epost.1 (costNode absorb charge)

theorem costNode_mono (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) :
    PIR.Process.MonotoneNode (L := List E → ENNReal → Prop) (costNode absorb charge) := by
  intro operation lower upper le history cost
  rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ | ⟨event, decode⟩ | _ <;>
    simp only [costNode, absorbed]
  · exact fun holds message value recovered => le _ _ _ (holds message value recovered)
  · exact fun holds => le _ _ _ holds
  · rintro ⟨remaining, charged, rest⟩
    exact ⟨remaining, charged, fun value => le _ _ _ (rest value)⟩
  · exact fun holds => holds

section CostNodes
variable (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) (operation : I.Op)
  (next : I.Reply operation → List E → ENNReal → Prop) (history : List E) (cost : ENNReal)

theorem costNode_receive {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) :
    costNode absorb charge operation next history cost =
      ∀ message value, recover (event message) = some value →
        next value (history ++ [event message]) cost := by
  simp only [costNode, absorbed]

theorem costNode_send {event : E} {value : I.Reply operation}
    (absorbed : absorb operation = .send event value) :
    costNode absorb charge operation next history cost = next value (history ++ [event]) cost := by
  simp only [costNode, absorbed]

theorem costNode_query {event : E} {decode : Raw event → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) :
    costNode absorb charge operation next history cost =
      ∃ remaining, charge history event + remaining ≤ cost ∧
        ∀ value, next value (history ++ [event]) remaining := by
  simp only [costNode, absorbed]

end CostNodes

/-- The cost weakest-precondition monad on proposition-valued assertions. -/
@[instance_reducible] noncomputable def costMonad (absorb : Interface I E P Raw)
    (charge : List E → E → ENNReal) :
    WPMonad (PIR.Process I) (CostAssert E) (CostStopAssert E) where
  toWP _ := {
    wpTrans := fun process => ⟨fun post stopped history cost =>
      ⟨costWP absorb charge process (fun value reached remaining => (post value reached remaining).holds)
        estack⟨fun reason reached remaining => (stopped.1 reason reached remaining).holds⟩
        history cost⟩⟩
    wp_trans_monotone := fun process _ _ _ _ stops returns history cost inside =>
      PIR.Process.foldReplies_mono (costNode_mono absorb charge)
        (fun value reached remaining holds => returns value reached remaining holds)
        (fun reason reached remaining holds => stops.1 reason reached remaining holds)
        process history cost inside }
  pure_le_wp_pure _ _ _ := fun _ _ holds => holds
  bind_le_wp_bind process next post stopped := by
    intro history cost holds
    change costWP absorb charge (process.bind next) _ _ history cost
    unfold costWP
    rw [PIR.Process.foldReplies_bind]
    exact holds

/-- A cost triple, under the local instance of `absorb` and `charge`. -/
abbrev CostTriple (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) {A : Type}
    (process : PIR.Process I A) (pre : CostAssert E) (post : A → CostAssert E)
    (stopped : CostStopAssert E) : Prop :=
  letI := costMonad absorb charge
  Triple process pre post stopped

/-- Adequacy: the cost WP at the trivial postconditions is zkc's `ChargedCostBound`. -/
theorem costWP_iff (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) {A : Type} :
    ∀ (process : PIR.Process I A) (history : List E) (cost : ENNReal),
      costWP absorb charge process (fun _ _ _ => True) estack⟨fun _ _ _ => True⟩ history cost ↔
        Typed.ChargedCostBound absorb charge process history cost
  | .done _, _, _ => Iff.rfl
  | .halt _, _, _ => Iff.rfl
  | .call operation next, history, cost => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ | ⟨event, decode⟩ | _ <;>
        simp only [costWP, PIR.Process.foldReplies, costNode, Typed.ChargedCostBound, absorbed]
      · exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => costWP_iff absorb charge _ _ _
      · exact costWP_iff absorb charge _ _ _
      · exact exists_congr fun _ => and_congr_right fun _ => forall_congr' fun _ => costWP_iff absorb charge _ _ _

section CostSpecs
variable (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)

/-- The primitive call rule of the cost reading: the precondition is the cost node of the
operation's absorption. -/
@[spec] theorem call_cost (operation : I.Op) (post : I.Reply operation → CostAssert E)
    (stopped : CostStopAssert E) :
    @Triple _ _ _ _ _ _ (PIR.Process.call operation .done)
      ((costMonad absorb charge).toWP (I.Reply operation))
      (fun history cost => ⟨costNode absorb charge operation
        (fun reply reached remaining => (post reply reached remaining).holds) history cost⟩)
      post stopped := by
  let := costMonad absorb charge
  exact ⟨fun _ _ holds => holds⟩

/-- A stop reads as the stop postcondition. -/
@[spec] theorem halt_cost {A : Type} (reason : PIR.Stop) (post : A → CostAssert E)
    (stopped : CostStopAssert E) :
    @Triple _ _ _ _ _ _ (PIR.Process.halt reason : PIR.Process I A)
      ((costMonad absorb charge).toWP A) (stopped.1 reason) post stopped := by
  let := costMonad absorb charge
  exact ⟨fun _ _ holds => holds⟩

/-- Adequacy in the form endpoints consume: a cost triple bounds the pathwise cost from every
state satisfying its precondition, whatever its postconditions. -/
theorem costBound_of_triple {A : Type} {process : PIR.Process I A} {pre : CostAssert E}
    {post : A → CostAssert E} {stopped : CostStopAssert E}
    (triple : CostTriple absorb charge process pre post stopped)
    (history : List E) (cost : ENNReal) (holds : (pre history cost).holds) :
    Typed.ChargedCostBound absorb charge process history cost := by
  let := costMonad absorb charge
  exact (costWP_iff absorb charge process history cost).mp
    (PIR.Process.foldReplies_mono (costNode_mono absorb charge) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) process history cost (triple.le_wp history cost holds))

/-- The cost triple's accepted boundary is precisely the existing pathwise bound. -/
theorem cost_of_triple {A : Type} {process : PIR.Process I A} {pre : CostAssert E}
    (proof : CostTriple absorb charge process pre (fun _ _ _ => ⟨True⟩) estack⟨fun _ _ _ => ⟨True⟩⟩)
    (history : List E) (cost : ENNReal) (holds : (pre history cost).holds) :
    Typed.ChargedCostBound absorb charge process history cost :=
  costBound_of_triple absorb charge proof history cost holds

theorem receive_cost (operation : I.Op) (event : P → E)
    (recover : E → Option (I.Reply operation)) (absorbed : absorb operation = .receive event recover)
    (post : I.Reply operation → CostAssert E) (stopped : CostStopAssert E) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => ⟨∀ message value, recover (event message) = some value →
        (post value (history ++ [event message]) cost).holds⟩) post stopped := by
  let := costMonad absorb charge
  refine ⟨fun history cost holds => ?_⟩
  change costNode absorb charge operation _ history cost
  rw [costNode_receive absorb charge operation _ history cost absorbed]
  exact holds

theorem send_cost (operation : I.Op) (event : E) (value : I.Reply operation)
    (absorbed : absorb operation = .send event value)
    (post : I.Reply operation → CostAssert E) (stopped : CostStopAssert E) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => post value (history ++ [event]) cost) post stopped := by
  let := costMonad absorb charge
  refine ⟨fun history cost holds => ?_⟩
  change costNode absorb charge operation _ history cost
  rw [costNode_send absorb charge operation _ history cost absorbed]
  exact holds

/-- Pay at the reached history, without subtracting infinities or assuming a
finite price. The continuation budget is explicit, and covers every reply. -/
theorem query_cost (operation : I.Op) (event : E)
    (decode : Raw event → Option (I.Reply operation)) (absorbed : absorb operation = .query event decode)
    (remaining : ENNReal) (post : I.Reply operation → CostAssert E) (stopped : CostStopAssert E) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => ⟨charge history event + remaining ≤ cost ∧
        ∀ value, (post value (history ++ [event]) remaining).holds⟩) post stopped := by
  let := costMonad absorb charge
  refine ⟨fun history cost holds => ?_⟩
  change costNode absorb charge operation _ history cost
  rw [costNode_query absorb charge operation _ history cost absorbed]
  exact ⟨remaining, holds.1, holds.2⟩

/-- The old pathwise cost bound can reserve budget for an arbitrary suffix.
No expectation bound, independence or finiteness assumption is introduced. -/
theorem reserve {A : Type} (remaining : ENNReal) :
    ∀ (process : PIR.Process I A) (history : List E) (bound cost : ENNReal),
      Typed.ChargedCostBound absorb charge process history bound → bound + remaining ≤ cost →
      costWP absorb charge process (fun _ _ available => remaining ≤ available)
        estack⟨fun _ _ _ => True⟩ history cost
  | .done _, _, _, _, _, enough => le_trans le_add_self enough
  | .halt _, _, _, _, _, _ => trivial
  | .call operation next, history, bound, cost, bounded, enough => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ | ⟨event, decode⟩ | _ <;>
        simp only [costWP, PIR.Process.foldReplies, costNode, Typed.ChargedCostBound, absorbed] at *
      · exact fun message value recovered => reserve remaining _ _ _ _ (bounded message value recovered) enough
      · exact reserve remaining _ _ _ _ bounded enough
      · obtain ⟨rest, paid, suffix⟩ := bounded
        refine ⟨rest + remaining, ?_, fun value => reserve remaining _ _ _ _ (suffix value) le_rfl⟩
        have paidMore : charge history event + (rest + remaining) ≤ bound + remaining := by
          simpa only [add_assoc] using _root_.add_le_add paid (le_refl remaining)
        exact paidMore.trans enough

/-- Lift a reusable component budget into a continuation-sensitive WP spec.
The suffix receives every returned value/history and at least its reservation. -/
theorem bound_spec {A : Type} (process : PIR.Process I A) (bound remaining : ENNReal)
    (bounded : ∀ history, Typed.ChargedCostBound absorb charge process history bound)
    (post : A → CostAssert E) :
    CostTriple absorb charge process
      (fun _ cost => ⟨bound + remaining ≤ cost ∧
        ∀ value reached available, remaining ≤ available → (post value reached available).holds⟩)
      post estack⟨fun _ _ _ => ⟨True⟩⟩ := by
  let := costMonad absorb charge
  refine ⟨fun history cost holds => ?_⟩
  exact PIR.Process.foldReplies_mono (costNode_mono absorb charge)
    (fun value reached available enough => holds.2 value reached available enough)
    (fun _ _ _ inside => inside) process history cost
    (reserve absorb charge remaining process history bound cost (bounded history) holds.1)

/-- A resource invariant for a bounded loop. A body specification is used only
at a positive remaining count; the terminal invariant supplies the zero case. -/
theorem repeat_cost_spec {A : Type} (step : A → PIR.Process I A)
    (invariant : Nat → A → CostAssert E)
    (body : ∀ remaining value, CostTriple absorb charge (step value)
      (invariant (remaining + 1) value) (invariant remaining) estack⟨fun _ _ _ => ⟨True⟩⟩)
    (count : Nat) (value : A) :
    CostTriple absorb charge (PIR.repeatN count step value) (invariant count value)
      (invariant 0) estack⟨fun _ _ _ => ⟨True⟩⟩ := by
  let := costMonad absorb charge
  refine ⟨fun history cost holds => ?_⟩
  have preserved : ∀ remaining value,
      (fun reached available => (invariant (remaining + 1) value reached available).holds) ≤
        (step value).foldReplies
          (fun value reached available => (invariant remaining value reached available).holds)
          (fun _ _ _ => True) (costNode absorb charge) :=
    fun remaining value reached available inside => (body remaining value).le_wp reached available inside
  exact PIR.Process.le_foldReplies_repeatN (costNode_mono absorb charge) step
    (fun remaining value reached available => (invariant remaining value reached available).holds)
    preserved count value history cost holds

end CostSpecs

end ZkcSecurity.Obligations.WeakestPrecondition
