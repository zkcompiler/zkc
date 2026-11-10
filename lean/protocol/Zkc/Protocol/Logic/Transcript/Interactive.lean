module

public import Zkc.Protocol.Logic.WeakestPrecondition
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

/-! The interactive experiment of a validator over a transcript interface.

The Fiat–Shamir endpoint answers every query by a random oracle keyed by the absorbed history,
which the prover may query first. A secret setup value, or a verifier challenge in an interactive
protocol, is instead a fresh uniform sample that the adversary meets only after committing to its
earlier messages. `interact` runs any `Process` over any `Interface` against an adversary strategy:
a receive is answered by the strategy, which sees the absorbed history and the raw answer of every
earlier draw; a query is answered by a fresh uniform raw answer of its occurrence, decoded by the
site. Each operation is absorbed, and each stop reason arises, as in `Zkc.Transcript.transform`;
`interact` returns the reached history where `transform` returns the unread proof suffix.

The endpoint consumes the same two premises as the Fiat–Shamir endpoint: the charged reading at
the bounded judgment and a pathwise charged cost bound. Together they bound the probability that a
run returns a value violating the postcondition by the cost, with no adversary-query term. A
strategy with a smaller view, such as a prover that never sees a setup secret, is an instance.
-/

set_option autoImplicit false
namespace ZkcSecurity.Interactive
open OracleComp OracleSpec Zkc.Transcript ZkcSecurity.Obligations ZkcSecurity.FiatShamir.Typed
open ZkcSecurity.Obligations.WeakestPrecondition ProtocolProof

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]

/-- An adversary strategy: the next proof message, from the absorbed history and the raw answer
of every draw so far. A strategy that ignores the second argument never sees a draw. -/
abbrev Strategy (E P : Type) (Raw : E → Type) := List E → List (Sigma Raw) → P

/-- The interactive experiment of a process: a receive is answered by the strategy, a query by a
fresh uniform raw answer of its occurrence. It returns the outcome with the reached history: the
given history extended by every absorbed event, including the event of a query whose raw answer
does not decode. `Zkc.Transcript.transform` instead returns the unread proof suffix. The stops are
those of `transform`: an unrecovered message and a refused operation stop `refused`, an undecodable
raw answer stops `exhausted`. `transform` also stops `refused` when its proof runs out; here the
strategy always supplies a message. -/
def interact (absorb : Interface I E P Raw) (strategy : Strategy E P Raw) :
    PIR.Process I A → List E → List (Sigma Raw) → ProbComp (PIR.Outcome A × List E)
  | .done value, history, _ => pure (.returned value, history)
  | .halt stop, history, _ => pure (.stopped stop, history)
  | .call operation next, history, draws =>
      match absorb operation with
      | .receive event recover =>
          match recover (event (strategy history draws)) with
          | some value =>
              interact absorb strategy (next value)
                (history ++ [event (strategy history draws)]) draws
          | none => pure (.stopped .refused, history)
      | .send event value => interact absorb strategy (next value) (history ++ [event]) draws
      | .query event decode => do
          let raw ← $ᵗ (Raw event)
          match decode raw with
          | some value =>
              interact absorb strategy (next value) (history ++ [event]) (draws ++ [⟨event, raw⟩])
          | none => pure (.stopped .exhausted, history ++ [event])
      | .refuse => pure (.stopped .refused, history)

section Equations
variable (absorb : Interface I E P Raw) (strategy : Strategy E P Raw)

theorem interact_receive {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E)
    (draws : List (Sigma Raw)) :
    interact absorb strategy (.call operation next) history draws =
      match recover (event (strategy history draws)) with
      | some value =>
          interact absorb strategy (next value)
            (history ++ [event (strategy history draws)]) draws
      | none => pure (.stopped .refused, history) := by
  simp only [interact, absorbed]

theorem interact_send {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : E} {value : I.Reply operation} (absorbed : absorb operation = .send event value)
    (history : List E) (draws : List (Sigma Raw)) :
    interact absorb strategy (.call operation next) history draws =
      interact absorb strategy (next value) (history ++ [event]) draws := by
  simp only [interact, absorbed]

theorem interact_query {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : E} {decode : Raw event → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) (history : List E)
    (draws : List (Sigma Raw)) :
    interact absorb strategy (.call operation next) history draws =
      ($ᵗ (Raw event)) >>= fun raw =>
        match decode raw with
        | some value =>
            interact absorb strategy (next value) (history ++ [event]) (draws ++ [⟨event, raw⟩])
        | none => pure (.stopped .exhausted, history ++ [event]) := by
  simp only [interact, absorbed]

theorem interact_refuse {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    (absorbed : absorb operation = .refuse) (history : List E) (draws : List (Sigma Raw)) :
    interact absorb strategy (.call operation next) history draws =
      pure (.stopped .refused, history) := by
  simp only [interact, absorbed]

end Equations

/-- A run violates the postcondition when it returns a value that fails it at the reached
history. Stops never violate. -/
def Violates (Post : List E → A → Prop) (result : PIR.Outcome A × List E) : Prop :=
  match result.1 with
  | .returned value => ¬ Post result.2 value
  | .stopped _ => False

private theorem prEvent_pure_eq_zero {α : Type} (value : α) (event : α → Prop)
    (fails : ¬ event value) :
    Pr{let result ← (pure value : ProbComp α)}[event result] = 0 := by
  classical
  simp [fails]

variable (absorb : Interface I E P Raw)

/-- **Interactive soundness.** The charged reading of a process at the bounded judgment and a
pathwise charged cost bound, both from `history`, bound the probability that the interactive run
against any strategy returns a value violating `Post` by `cost`. The earlier draws are
arbitrary. -/
theorem soundness (strategy : Strategy E P Raw) (charge : List E → E → ENNReal)
    (Post : List E → A → Prop) :
    ∀ (process : PIR.Process I A) (history : List E) (draws : List (Sigma Raw)) (cost : ENNReal),
      absorb.Charged (boundedEscape charge) Post process history →
      ChargedCostBound absorb charge process history cost →
      Pr{let result ← interact absorb strategy process history draws}[Violates Post result] ≤
        cost := by
  intro process
  induction process with
  | done value =>
      intro history draws cost charged _
      exact (prEvent_pure_eq_zero _ _ (fun violated => violated charged)).le.trans zero_le
  | halt stop =>
      intro history draws cost _ _
      exact (prEvent_pure_eq_zero _ _ (fun violated => violated)).le.trans zero_le
  | call operation next ih =>
      intro history draws cost charged priced
      rw [Interface.charged_call] at charged
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        rw [interact_receive absorb strategy absorbed]
        cases recovered : recover (event (strategy history draws)) with
        | none => exact (prEvent_pure_eq_zero _ _ (fun violated => violated)).le.trans zero_le
        | some value =>
            exact ih value _ _ _ (charged _ value recovered) (priced _ value recovered)
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        rw [interact_send absorb strategy absorbed]
        exact ih value _ _ _ charged priced
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        obtain ⟨remaining, within, rest⟩ := priced
        rw [interact_query absorb strategy absorbed]
        refine (prEvent_bind_le_prEvent_add _ _
          (fun raw => ∃ value, decode raw = some value ∧
            ¬ absorb.Charged (boundedEscape charge) Post (next value) (history ++ [event]))
          _ (ε := remaining) ?_).trans ((add_le_add_left charged _).trans within)
        intro raw outside
        cases decoded : decode raw with
        | none => exact (prEvent_pure_eq_zero _ _ (fun violated => violated)).le.trans zero_le
        | some value =>
            exact ih value _ _ _
              (Classical.byContradiction fun missing => outside ⟨value, decoded, missing⟩)
              (rest value)
      · rw [interact_refuse absorb strategy absorbed]
        exact (prEvent_pure_eq_zero _ _ (fun violated => violated)).le.trans zero_le

/-- The endpoint in the vocabulary of the Fiat–Shamir endpoint: an acceptance predicate that the
postcondition excludes is met with probability at most the cost. -/
theorem soundness_accepted (strategy : Strategy E P Raw) (charge : List E → E → ENNReal)
    (Post : List E → A → Prop) (accepts : A → Prop)
    (terminal : ∀ history value, Post history value → ¬ accepts value)
    (process : PIR.Process I A) (history : List E)
    (charged : absorb.Charged (boundedEscape charge) Post process history) (cost : ENNReal)
    (priced : ChargedCostBound absorb charge process history cost) :
    Pr{let result ← interact absorb strategy process history []}[Accepted accepts result.1] ≤
      cost := by
  refine (prEvent_mono _ _ (Violates Post) ?_).trans
    (soundness absorb strategy charge Post process history [] cost charged priced)
  rintro ⟨outcome, reached⟩ accepted
  cases outcome with
  | returned value => exact fun holds => terminal reached value holds accepted
  | stopped stop => exact accepted

/-- A randomized adversary is a distribution over strategies, sampled before the run. -/
theorem soundness_randomized (charge : List E → E → ENNReal)
    (Post : List E → A → Prop) (accepts : A → Prop)
    (terminal : ∀ history value, Post history value → ¬ accepts value)
    (process : PIR.Process I A) (history : List E)
    (charged : absorb.Charged (boundedEscape charge) Post process history) (cost : ENNReal)
    (priced : ChargedCostBound absorb charge process history cost)
    (strategies : ProbComp (Strategy E P Raw)) :
    Pr{let result ← strategies >>= fun strategy => interact absorb strategy process history []}[
      Accepted accepts result.1] ≤ cost :=
  prEvent_bind_le_of_forall_le _ _ _ fun strategy =>
    soundness_accepted absorb strategy charge Post accepts terminal process history charged cost
      priced

/-- The transform `Zkc.Transcript.transform` with fresh uniform sampling as its oracle is the
experiment of a prover that fixes its whole proof in advance; the same two premises bound it by
the cost. -/
theorem fresh_transform_soundness (charge : List E → E → ENNReal) (Post : List E → A → Prop)
    (accepts : A → Prop) (terminal : ∀ history value, Post history value → ¬ accepts value) :
    ∀ (process : PIR.Process I A) (history : List E) (proof : List P) (cost : ENNReal),
      absorb.Charged (boundedEscape charge) Post process history →
      ChargedCostBound absorb charge process history cost →
      Pr{let result ← transform absorb (fun _ event => $ᵗ (Raw event)) process history proof}[
        Accepted accepts result.1] ≤ cost := by
  intro process
  induction process with
  | done value =>
      intro history proof cost charged _
      exact (prEvent_pure_eq_zero _ _ (terminal history value charged)).le.trans zero_le
  | halt stop =>
      intro history proof cost _ _
      exact (prEvent_pure_eq_zero _ _ id).le.trans zero_le
  | call operation next ih =>
      intro history proof cost charged priced
      rw [Interface.charged_call] at charged
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        cases proof with
        | nil =>
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            exact (prEvent_pure_eq_zero _ _ id).le.trans zero_le
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recovered : recover (event message) with
            | none => exact (prEvent_pure_eq_zero _ _ id).le.trans zero_le
            | some value =>
                exact ih value _ _ _ (charged message value recovered)
                  (priced message value recovered)
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        rw [Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value _ _ _ charged priced
      · rw [absorbed] at charged
        simp only [ChargedCostBound, absorbed] at priced
        obtain ⟨remaining, within, rest⟩ := priced
        rw [Zkc.Transcript.transform_query absorb _ absorbed]
        refine (prEvent_bind_le_prEvent_add _ _
          (fun raw => ∃ value, decode raw = some value ∧
            ¬ absorb.Charged (boundedEscape charge) Post (next value) (history ++ [event]))
          _ (ε := remaining) ?_).trans ((add_le_add_left charged _).trans within)
        intro raw outside
        cases decoded : decode raw with
        | none => exact (prEvent_pure_eq_zero _ _ id).le.trans zero_le
        | some value =>
            exact ih value _ _ _
              (Classical.byContradiction fun missing => outside ⟨value, decoded, missing⟩)
              (rest value)
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed]
        exact (prEvent_pure_eq_zero _ _ id).le.trans zero_le

/-! ### The completeness boundary

The readings bound acceptance; a charged triple alone does not show that a run returns. An
interface may refuse an operation and a decoder may reject every raw answer; both stop the run,
and the charged reading accepts every stop. Over an interface that admits every operation, an
exact triple whose stop assertion is false for every reason does show it. -/

/-- An interface admits every operation: it refuses none, every received message recovers a reply
and every raw answer of a query decodes. -/
def Total (absorb : Interface I E P Raw) : Prop :=
  ∀ operation, match absorb operation with
    | .receive event recover => ∀ message, (recover (event message)).isSome
    | .send _ _ => True
    | .query _ decode => ∀ raw, (decode raw).isSome
    | .refuse => False

/-- Over a total interface, the exact reading with false stop assertions forces every run of the
interactive experiment, against any strategy, to return a value satisfying the postcondition. -/
private theorem returns_of_chargedWP (strategy : Strategy E P Raw) (total : Total absorb)
    (Post : List E → A → Prop) :
    ∀ (process : PIR.Process I A) (history : List E) (draws : List (Sigma Raw)),
      chargedWP absorb exactEscape process (fun value reached => Post reached value)
        estack⟨fun _ _ => False⟩ history →
      ∀ result ∈ support (interact absorb strategy process history draws),
        ∃ value, result.1 = .returned value ∧ Post result.2 value := by
  intro process
  induction process with
  | done value =>
      intro history draws holds result member
      obtain rfl := eq_of_mem_support_pure member
      exact ⟨value, rfl, holds⟩
  | halt stop =>
      intro history draws holds
      exact holds.elim
  | call operation next ih =>
      intro history draws holds result member
      have node := total operation
      change (absorb operation).ChargedNode exactEscape _ history at holds
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _ <;> simp only [absorbed] at node <;> rw [absorbed] at holds
      -- A refusal contradicts totality; `node` is already `False` there.
      · rw [interact_receive absorb strategy absorbed] at member
        obtain ⟨value, recovered⟩ := Option.isSome_iff_exists.mp (node (strategy history draws))
        rw [recovered] at member
        exact ih value _ _ (holds _ value recovered) result member
      · rw [interact_send absorb strategy absorbed] at member
        exact ih value _ _ holds result member
      · rw [interact_query absorb strategy absorbed] at member
        obtain ⟨raw, -, member⟩ := support_bind_exists member
        obtain ⟨value, decoded⟩ := Option.isSome_iff_exists.mp (node raw)
        rw [decoded] at member
        exact ih value _ _
          (Classical.byContradiction fun missing => holds raw ⟨value, decoded, missing⟩) result member

/-- Over a total interface, an exact triple whose stop assertion is false for every reason makes
every run of the interactive experiment from a history satisfying its precondition, against any
strategy, return a value satisfying its postcondition. -/
theorem returns_of_exact (strategy : Strategy E P Raw) (total : Total absorb)
    {process : PIR.Process I A} {pre : Assert E} {Post : List E → A → Prop}
    (triple : ChargedTriple absorb exactEscape exactEscape_antitone process pre
      (fun value reached => ⟨Post reached value⟩) estack⟨fun _ _ => ⟨False⟩⟩)
    (history : List E) (holds : (pre history).holds) (draws : List (Sigma Raw)) :
    ∀ result ∈ support (interact absorb strategy process history draws),
      ∃ value, result.1 = .returned value ∧ Post result.2 value := by
  let := chargedMonad absorb exactEscape exactEscape_antitone
  exact returns_of_chargedWP absorb strategy total Post process history draws
    (triple.le_wp history holds)

end ZkcSecurity.Interactive
