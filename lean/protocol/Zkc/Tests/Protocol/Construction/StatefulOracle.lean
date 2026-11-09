module

public import Zkc.Tools.Protocol.Construction
public import Zkc.Protocol.Claims.Assembly

/-! A finite oracle experiment with persistent publications and adaptive decoded reads.
The first sampled cell determines the second query's position. Both publications remain in
one append-only store. Invalid handles, positions and encodings stop with their reached state
and complete observation history. The numerical event is fixed before proof construction.
-/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP MeasureTheory ProbabilityTheory

namespace ProtocolProofExamples.StatefulOracle

abbrev Word := Nat × Nat
abbrev Store := List Word
abbrev Event := Nat × Nat × Nat

inductive Operation
  | publish (word : Word)
  | sample
  | read (handle position : Nat)

abbrev Service : Signature := ⟨Operation, fun _ => Nat⟩
def half : ENNReal := 1 / 2
theorem halves : half + half = 1 := ENNReal.add_halves 1

def cell (word : Word) (index : Bool) : Nat := if index then word.2 else word.1
def decode (value : Nat) : Option Bool := if value < 2 then some (value == 1) else none

/-- The sample parameter is ignored by every deterministic operation. -/
def transition (sample : Bool) (operation : Operation) (store : Store) :
    Execution Store Event Nat :=
  match operation with
  | .publish word => ⟨.returned store.length, store ++ [word], [(0, store.length, 0)]⟩
  | .sample => ⟨.returned sample.toNat, store, [(1, sample.toNat, 0)]⟩
  | .read handle position =>
    match store[handle]? with
    | none => ⟨.stopped .refused, store, [(2, handle, position)]⟩
    | some word =>
      if position < 2 then
        ⟨.returned (cell word (position == 1)), store, [(2, handle, position)]⟩
      else ⟨.stopped .refused, store, [(2, handle, position)]⟩

def evaluate (operation : Operation) (sample : Bool)
    (post : Outcome Nat → Potential Store Event) (current : Store × List Event) : ENNReal :=
  let out := transition sample operation current.1
  post out.outcome (out.state, current.2 ++ out.events)

def spec : OperationSpec Service Store Event := fun operation post current =>
  match operation with
  | .sample => half * evaluate operation false post current + half * evaluate operation true post current
  | _ => evaluate operation false post current

theorem spec_mono : spec.Monotone := by
  intro operation post post' h current
  cases operation with
  | publish word => exact h _ _
  | read handle position => exact h _ _
  | sample => exact add_le_add (mul_le_mul_right (h _ _) half) (mul_le_mul_right (h _ _) half)

noncomputable def operations : (op : Service.Op) → Kernel Store (Execution Store Event (Service.Reply op))
  | .sample =>
    ⟨fun store => half • Measure.dirac (transition false .sample store) +
      half • Measure.dirac (transition true .sample store), measurable_of_countable _⟩
  | operation => Kernel.deterministic (transition false operation) (measurable_of_countable _)

structure Configuration where
  first : Word
  second : Word
  claim : Bool

noncomputable def system : System Configuration Service Store Event where
  operations _ := operations
  initial _ := Measure.dirac []
  operation_mass _ operation store := by
    cases operation <;> simp [operations, halves]
  initial_probability _ := inferInstance

theorem operation_expectation (e : Configuration) (operation : Operation)
    (post : Outcome Nat → Potential Store Event) (current : Store × List Event) :
    opExpectation (I := Service) (system.accumulatedOperations e) operation post current =
      spec operation post current := by
  change (∫⁻ out, post out.1 out.2 ∂system.accumulatedOperations e operation current) = _
  rw [system.accumulatedOperations_apply]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  cases operation <;>
    simp [system, operations, spec, evaluate, lintegral_add_measure, lintegral_smul_measure]

inductive Ty | word | number | bit deriving DecidableEq
inductive Op | publish | sample | read | decode | index | agrees | both

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .publish => [.word]
    | .sample => []
    | .read => [.number, .number]
    | .decode => [.number]
    | .index | .agrees => [.bit]
    | .both => [.bit, .bit]
  result
    | .publish | .sample | .read | .index => .number
    | .decode | .agrees | .both => .bit
  condition := .bit

abbrev meaning (claim : Bool) : Interpretation language Service where
  Value | .word => Word | .number => Nat | .bit => Bool
  condition := id
  operation
    | .publish, .cons word .nil => .call (.publish word) .done
    | .sample, .nil => .call .sample .done
    | .read, .cons handle (.cons position .nil) => .call (.read handle position) .done
    | .decode, .cons raw .nil =>
      if raw < 2 then .done (raw == 1) else .halt .refused
    | .index, .cons bit .nil => .done bit.toNat
    | .agrees, .cons bit .nil => .done (bit == claim)
    | .both, .cons left (.cons right .nil) => .done (left && right)

/-- The same decoded-read body is used twice with different live arguments. -/
def read : Region (scalarDialect language) [.number, .number] [.bit] :=
  .letOp (.ordinary .read) (.cons .here (.cons (.there .here) .nil)) .nil
    (.letOp (.ordinary .decode) (.cons .here .nil) .nil (.ret (.cons .here .nil)))

def source : Region (scalarDialect language) [.word, .word] [.bit] :=
  .letOp (.ordinary .publish) (.cons .here .nil) .nil
    (.letOp (.ordinary .publish) (.cons (.there (.there .here)) .nil) .nil
      (.letOp (.ordinary .sample) .nil .nil
        (.bind (read.rename (Values.cons (.there (.there .here))
            (Values.cons .here .nil) : Operands [Ty.number, .number, .number, .word, .word]
              [.number, .number]).get)
          (.letOp (.ordinary .index) (.cons .here .nil) .nil
            (.bind (read.rename (Values.cons (.there (.there (.there .here)))
                (Values.cons .here .nil) : Operands [Ty.number, .bit, .number, .number, .number, .word, .word]
                  [.number, .number]).get)
              (.letOp (.ordinary .agrees) (.cons (.there (.there .here)) .nil) .nil
                (.letOp (.ordinary .agrees) (.cons (.there .here) .nil) .nil
                  (.letOp (.ordinary .both) (.cons .here (.cons (.there .here) .nil)) .nil
                    (.ret (.cons .here .nil))))))))))

def game (e : Configuration) : Process Service Bool :=
  (source.denote (meaning e.claim).regionMeaning
    (Values.cons e.first (Values.cons e.second .nil)).get).bind fun values => .done (values.get .here)

/-- Independent mathematical event: decode the sampled first cell, then use its value
as the second position. Failure is rejection, with no conditioning on successful decoding. -/
def acceptedAt (e : Configuration) (index : Bool) : Bool :=
  match decode (cell e.first index) with
  | none => false
  | some bit =>
    match decode (cell e.second bit) with
    | none => false
    | some other => (bit == e.claim) && (other == e.claim)

def weight (accepted : Bool) (value : ENNReal) : ENNReal := if accepted then value else 0
def acceptance (e : Configuration) : ENNReal :=
  half * weight (acceptedAt e false) 1 + half * weight (acceptedAt e true) 1

/-- The provider's mathematical read law preserves the full state and observation prefix.
The same law applies to every stored word and both query occurrences. -/
theorem decoded_read (store : Store) (history : List Event) (handle : Nat) (word : Word)
    (found : store[handle]? = some word) (position : Bool)
    (post : Bool → Potential Store Event) (stopped : Stop → Potential Store Event) :
    evaluate (.read handle position.toNat) false
      (fun outcome => match outcome with
        | .stopped reason => stopped reason
        | .returned raw => match decode raw with | some bit => post bit | none => stopped .refused)
      (store, history) =
      match decode (cell word position) with
      | some bit => post bit (store, history ++ [(2, handle, position.toNat)])
      | none => stopped .refused (store, history ++ [(2, handle, position.toNat)]) := by
  cases position <;> simp [evaluate, transition, found]
  all_goals split <;> simp_all

abbrev upperLogic : WPMonad (Process Service)
    (Potential Store Event)ᵒᵈ (Stop → Potential Store Event)ᵒᵈ := spec.toUpperWPMonad spec_mono
attribute [local instance] upperLogic

@[spec] theorem publish_rule (claim : Bool) (word : Word) :
    (meaning claim).operation .publish (.cons word .nil) = .call (.publish word) .done := rfl
@[spec] theorem sample_rule (claim : Bool) :
    (meaning claim).operation .sample .nil = .call .sample .done := rfl
@[spec] theorem read_rule (claim : Bool) (handle position : Nat) :
    (meaning claim).operation .read (.cons handle (.cons position .nil)) =
      .call (.read handle position) .done := rfl
@[spec] theorem decode_rule (claim : Bool) (raw : Nat) :
    (meaning claim).operation .decode (.cons raw .nil) =
      (if raw < 2 then .done (raw == 1) else .halt .refused) := rfl
@[spec] theorem index_rule (claim bit : Bool) :
    (meaning claim).operation .index (.cons bit .nil) = .done bit.toNat := rfl
@[spec] theorem agrees_rule (claim bit : Bool) :
    (meaning claim).operation .agrees (.cons bit .nil) = .done (bit == claim) := rfl
@[spec] theorem both_rule (claim left right : Bool) :
    (meaning claim).operation .both (.cons left (.cons right .nil)) = .done (left && right) := rfl


def decodedPost (post : Bool → Potential Store Event) (stopped : Stop → Potential Store Event) :
    Outcome Nat → Potential Store Event
  | .stopped reason => stopped reason
  | .returned raw => match decode raw with | some bit => post bit | none => stopped .refused

example (handle position : Nat) (post : Outcome Nat → Potential Store Event) :
    spec (.read handle position) post = evaluate (.read handle position) false post := rfl

@[spec high] theorem read_upper (claim : Bool)
    (env : Environment (meaning claim).Value [.number, .number])
    (post : Values (meaning claim).Value [.bit] → (Potential Store Event)ᵒᵈ)
    (stopped : (Stop → Potential Store Event)ᵒᵈ) :
    ⦃OrderDual.toDual (evaluate (.read (env .here) (env (.there .here))) false
      (decodedPost (fun bit => OrderDual.ofDual (post (.singleton bit))) (OrderDual.ofDual stopped)))⦄
      read.denote (meaning claim).regionMeaning env ⦃post; stopped⦄ := by
  unfold read
  construct_region
  change ∀ current, _ ≤ _
  intro current
  simp only [spec, evaluate, decodedPost, decode]
  cases (transition false (.read (env .here) (env (.there .here))) current.1).outcome with
  | stopped reason => simp [OperationSpec.outcomePost]
  | returned raw =>
    by_cases valid : raw < 2 <;> simp [OperationSpec.outcomePost, valid]



/-- The complete source, including both publications and the adaptive second read. -/
theorem game_upper (e : Configuration) :
    ⦃OrderDual.toDual (fun _ : Store × List Event => acceptance e)⦄ game e
    ⦃fun accepted => OrderDual.toDual (fun _ => weight accepted 1);
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold game source
  construct_region
  change ∀ current, _ ≤ _
  rintro ⟨store, history⟩
  cases claim : e.claim <;> simp [claim, spec, evaluate, transition, OperationSpec.outcomePost, decodedPost,
    acceptance, acceptedAt, cell, decode, Bool.and_comm]
  all_goals split_ifs <;> simp_all [evaluate, transition, decodedPost, cell, decode,
    weight, Bool.and_comm, Bool.toNat_le]
  all_goals split_ifs <;> simp_all [Bool.and_comm]


abbrev lowerLogic : WPMonad (Process Service)
    (Potential Store Event) (Stop → Potential Store Event) := spec.toWPMonad spec_mono

section Lower
attribute [local instance] lowerLogic

@[spec high] theorem read_lower (claim : Bool)
    (env : Environment (meaning claim).Value [.number, .number])
    (post : Values (meaning claim).Value [.bit] → Potential Store Event)
    (stopped : Stop → Potential Store Event) :
    ⦃evaluate (.read (env .here) (env (.there .here))) false
      (decodedPost (fun bit => post (.singleton bit)) stopped)⦄
      read.denote (meaning claim).regionMeaning env ⦃post; stopped⦄ := by
  unfold read
  construct_region
  change (_ : ENNReal) ≤ _
  rename_i current
  simp only [spec, evaluate, decodedPost, decode]
  cases (transition false (.read (env .here) (env (.there .here))) current.1).outcome with
  | stopped reason => simp [OperationSpec.outcomePost]
  | returned raw =>
    by_cases valid : raw < 2 <;> simp [OperationSpec.outcomePost, valid]



theorem game_lower (e : Configuration) :
    ⦃fun _ : Store × List Event => acceptance e⦄ game e
    ⦃fun accepted => (fun _ => weight accepted 1);
      (fun _ _ => 0)⦄ := by
  unfold game source
  construct_region
  change (_ : ENNReal) ≤ _
  rename_i current
  rcases current with ⟨store, history⟩
  cases claim : e.claim <;> simp [claim, spec, evaluate, transition, OperationSpec.outcomePost, decodedPost,
    acceptance, acceptedAt, cell, decode, Bool.and_comm]
  all_goals split_ifs <;> simp_all [weight, Bool.and_comm, Bool.toNat_le]
  all_goals split_ifs <;> simp_all [Bool.and_comm]


end Lower

/-- The event observes the complete execution; every stopped outcome is non-accepting. -/
def accepting : Set (Execution Store Event Bool) := {out | out.outcome = .returned true}

theorem acceptance_reward (outcome : Outcome Bool) (current : Store × List Event) :
    accepting.indicator 1 ⟨outcome, current.1, current.2⟩ =
      OperationSpec.outcomePost (fun accepted _ => weight accepted 1)
        (fun _ _ => 0) outcome current := by
  cases outcome with
  | stopped reason => simp [accepting, OperationSpec.outcomePost]
  | returned accepted => cases accepted <;> simp [accepting, OperationSpec.outcomePost, weight]

noncomputable def upperRequest : UpperRequest Configuration (Execution Store Event Bool) where
  experiment := system.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound := acceptance

noncomputable def lowerRequest : LowerRequest Configuration (Execution Store Event Bool) where
  experiment := system.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound := acceptance

theorem complete_upper (e : Configuration) :
    UpperBound spec (game e)
      (fun out state => accepting.indicator 1 ⟨out, state.1, state.2⟩)
      (fun _ => acceptance e) := by
  simp only [acceptance_reward]
  exact (spec.upperBound_iff_triple spec_mono _ _ _ _).mpr (game_upper e)

theorem complete_lower (e : Configuration) :
    LowerBound spec (game e)
      (fun out state => accepting.indicator 1 ⟨out, state.1, state.2⟩)
      (fun _ => acceptance e) := by
  simp only [acceptance_reward]
  exact (spec.lowerBound_iff_triple spec_mono _ _ _ _).mpr (game_lower e)

noncomputable def upperEvidence :
    UpperEvidence upperRequest system system game (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).le
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential e _ := acceptance e
  mathematics e _ := complete_upper e
  budget _ _ := by simp [System.initialWithEvents, system, upperRequest]

noncomputable def lowerEvidence :
    LowerEvidence lowerRequest system system game (fun _ s t => s = t) where
  subject := rfl
  installation := Installation.reflexive system _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).ge
  model_event _ := accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential e _ := acceptance e
  mathematics e _ := complete_lower e
  budget _ _ := by simp [System.initialWithEvents, system, lowerRequest]

theorem oracle_upper : upperRequest.Holds := upperEvidence.establish
theorem oracle_lower : lowerRequest.Holds := lowerEvidence.establish

theorem oracle_acceptance (e : Configuration) :
    (system.experiment game).run e accepting = acceptance e :=
  le_antisymm (oracle_upper e trivial) (oracle_lower e trivial)

/-- One rejecting sampled position bounds acceptance by one half, without conditioning
on successful replies or assuming that the second query is independent. -/
theorem proximity (e : Configuration)
    (far : acceptedAt e false = false ∨ acceptedAt e true = false) :
    (system.experiment game).run e accepting ≤ half := by
  rw [oracle_acceptance]
  rcases far with far | far <;>
    simp [acceptance, far, weight] <;> split <;> simp

/-- Constant valid encodings have probability-one honest acceptance. -/
theorem honest_completeness (claim : Bool) :
    (system.experiment game).run
      ⟨(claim.toNat, claim.toNat), (claim.toNat, claim.toNat), claim⟩ accepting = 1 := by
  rw [oracle_acceptance]
  cases claim <;> simp [acceptance, acceptedAt, cell, decode, weight, halves]

/-- Failed reads retain the reached store and append their exact observation. -/
theorem stale_handle (store : Store) (position : Nat) :
    transition false (.read store.length position) store =
      ⟨.stopped .refused, store, [(2, store.length, position)]⟩ := by
  simp [transition]

theorem invalid_position (word : Word) :
    transition false (.read 0 2) [word] =
      ⟨.stopped .refused, [word], [(2, 0, 2)]⟩ := rfl

/-- The installed decoded-read law observes a malformed published cell as a refusal. -/
theorem malformed_encoding (history : List Event)
    (post : Bool → Potential Store Event) (stopped : Stop → Potential Store Event) :
    evaluate (.read 0 0) false (decodedPost post stopped) ([(2, 0)], history) =
      stopped .refused ([(2, 0)], history ++ [(2, 0, 0)]) := by
  exact decoded_read [(2, 0)] history 0 (2, 0) rfl false post stopped

/-- Same-typed handle exchange changes the actual publication read. -/
theorem handle_association :
    transition false (.read 0 0) [(0, 0), (1, 1)] ≠
      transition false (.read 1 0) [(0, 0), (1, 1)] := by
  intro same
  have bad := congrArg Execution.outcome same
  cases bad

end ProtocolProofExamples.StatefulOracle
