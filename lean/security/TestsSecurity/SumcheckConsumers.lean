import ZkcSecurity.Families.Sumcheck.Composition
import ZkcSecurity.Families.Sumcheck.TableReference
import ZkcSecurity.Families.Sumcheck.FactorReference
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SumcheckConsumers
open ZkcSecurity.Algebra.Polynomial
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.Consumers
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations OracleComp OracleSpec

variable {F : Type} [Field F]

inductive Operation (F : Type) where
  | receive (context remaining : Nat)
  | challenge (context remaining : Nat)
  | deliver (context remaining : Nat) (challenge : F)

abbrev signature (F M : Type) : PIR.Signature where
  Op := Operation F
  Reply
    | .receive _ _ => Option M
    | .challenge _ _ => F
    | .deliver _ _ _ => PUnit

inductive Event (M : Type) where
  | received (context remaining : Nat) (payload : Option M)
  | queried (context remaining : Nat)
  | delivered (context remaining : Nat)

abbrev raw (F M : Type) : Event M → Type
  | .received _ _ _ => Unit
  | .queried _ _ => F
  | .delivered _ _ => Unit

def absorb (F M : Type) : Interface (signature F M) (Event M) (Option M) (raw F M)
  | .receive context remaining => .receive (Event.received context remaining) fun event =>
      match event with
      | .received _ _ payload => some payload
      | .queried _ _ => none
      | .delivered _ _ => none
  | .challenge context remaining => .query (.queried context remaining) some
  | .deliver context remaining _ => .send (.delivered context remaining) ()

instance rawSampleable {M : Type} [SampleableType F] (event : Event M) :
    SampleableType (raw F M event) := by
  cases event with
  | received => exact inferInstanceAs (SampleableType Unit)
  | queried => exact inferInstanceAs (SampleableType F)
  | delivered => exact inferInstanceAs (SampleableType Unit)

structure State (reference : Reference F) (n : Nat) where
  claim : F
  object : reference.State n
  challengePrefix : List F
  privateFrame : Nat

def program (message : Message F) (reference : Reference F) :
    Program (signature F message.Carrier) Nat (State reference) message where
  claim s := s.claim
  receive {n} context _ := .call (.receive context (n + 1)) .done
  query {n} context _ _ := .challenge context (n + 1)
  challenge _ _ _ reply := reply
  deliver {n} context _ _ r := .call (.deliver context (n + 1) r) .done
  advance _ s m r := ⟨message.evaluate m r, reference.restrict s.object r,
    s.challengePrefix ++ [r], s.privateFrame⟩

def representation (message : Message F) (reference : Reference F) :
    Representation (program message reference) reference where
  state s := s.object
  advance _ _ _ _ := rfl
  claim _ _ _ _ := rfl

def queries (message : Message F) (reference : Reference F) :
    QueryInterface (program message reference) (absorb F message.Carrier) where
  event {n} context _ _ := .queried context (n + 1)
  decode _ _ _ := some
  challenge _ _ _ raw := raw
  absorbed _ _ _ := rfl
  decoded _ _ _ _ _ decoded := (Option.some.inj decoded).symm

theorem uniform_bound [Fintype F] [DecidableEq F] [SampleableType F]
    (message : Message F) (reference : Reference F) (messageDegree referenceDegree : Nat) :
    (queries message reference).ConditionalBound (representation message reference)
      messageDegree referenceDegree
      (fun _ _ => (max messageDegree referenceDegree : Nat) / (Fintype.card F : ENNReal)) := by
  exact QueryInterface.conditional_of_uniform _ _ _ _ (fun _ _ _ _ => rfl)

/-- Real degree-one tables and degree-two factors use exactly the same
arbitrary-message, whole-Process consumer, including partial execution. -/
theorem endpoint_residual [Fintype F] [DecidableEq F] [SampleableType F]
    {n : Nat} (count context : Nat) (s : State (TableReference.data F) (n + count))
    (history : List (Event (F × F)))
    (wrong : (representation (Message.endpoints F) (TableReference.data F)).No s) :
    (reduction (absorb F (F × F))
      (fun _ result => (representation (Message.endpoints F) (TableReference.data F)).No result)
      (fun _ _ => 1 / (Fintype.card F : ENNReal))).doomed history
      ((program (Message.endpoints F) (TableReference.data F)).remaining count context s) := by
  exact residual_doomed
    (representation (Message.endpoints F) (TableReference.data F))
    Message.endpoints_laws TableReference.laws (queries _ _)
    (by
      intro k context state allowed m reached p q different left right
      change Pr{let r ← $ᵗ F}[p.eval r = q.eval r] ≤ 1 / (Fintype.card F : ENNReal)
      simpa only [max_self, Nat.cast_one] using agreement_uniform_le p q different left right)
    count context s history wrong

theorem coefficient_residual [Fintype F] [DecidableEq F] [SampleableType F]
    {n : Nat} (count context : Nat) (s : State (FactorReference.data F) (n + count))
    (history : List (Event (F × F × F)))
    (wrong : (representation (Message.coefficientTriples F) (FactorReference.data F)).No s) :
    (reduction (absorb F (F × F × F))
      (fun _ result => (representation (Message.coefficientTriples F) (FactorReference.data F)).No result)
      (fun _ _ => 2 / (Fintype.card F : ENNReal))).doomed history
      ((program (Message.coefficientTriples F) (FactorReference.data F)).remaining count context s) := by
  simpa only [max_self, Nat.cast_ofNat] using residual_doomed
    (representation (Message.coefficientTriples F) (FactorReference.data F))
    Message.coefficientTriples_laws FactorReference.laws (queries _ _)
    (uniform_bound (Message.coefficientTriples F) (FactorReference.data F) 2 2)
    count context s history wrong

/-- Future-prefix closure uses exact dimension-indexed reference data. -/
theorem closed_dimension {n : Nat} (count : Nat)
    (s : (FactorReference.data F).State (n + count)) (challenges : Fin count → F) :
    (FactorReference.data F).admissible
      ((FactorReference.data F).restrictPrefix count s challenges) :=
  Reference.admissible_restrictPrefix FactorReference.laws count s challenges trivial

theorem closed_flat_dimension {n : Nat} (values fixed : List F)
    (shape : values.length = 2 ^ (n + fixed.length)) :
    (Zkc.Polynomial.Multilinear.restrictPrefixValues values fixed).length = 2 ^ n :=
  TableReference.prefix_shape values fixed shape

def zeroReference (F : Type) [Field F] : Reference F where
  State _ := Unit
  total _ := 0
  restrict _ _ := ()
  polynomial _ := 0
  admissible _ := True

theorem zeroLaws (degree : Nat) : ReferenceLaws (zeroReference F) degree where
  degree_le _ _ := by simp [zeroReference]
  boundary_eq _ _ := by simp [zeroReference, boundaryPoly]
  evaluation_eq _ _ _ := by simp [zeroReference]
  restriction_closed _ _ _ := trivial

def honestHandler (message : Message F) (honest : message.Carrier) (r : F) :
    PIR.Handler (signature F message.Carrier) Nat (Event message.Carrier)
  | .receive context remaining, counter =>
      ⟨.returned (some honest), counter + 1, [.received context remaining (some honest)]⟩
  | .challenge context remaining, counter =>
      ⟨.returned r, counter + 1, [.queried context remaining]⟩
  | .deliver context remaining _, counter =>
      ⟨.returned (), counter + 1, [.delivered context remaining]⟩

def ready (message : Message F) (honest : message.Carrier) (_ : Nat) {n : Nat}
    (_ : Nat) (_ : State (zeroReference F) (n + 1)) (m : message.Carrier) (_ : Nat) : Prop := m = honest

theorem honestExecution (message : Message F) (honest : message.Carrier) (r : F) :
    HonestRunLaws (program message (zeroReference F)) (honestHandler message honest r)
      (fun _ {_} _ _ _ => True) (ready message honest) where
  receive _count {_n} context _s h _ := ⟨honest, h + 1, [.received context _ (some honest)], rfl, rfl⟩
  query _count {_n} context _s _m h _delivered :=
    ⟨r, h + 1, [.queried context _], h + 2, [.delivered context _], rfl, rfl, trivial⟩

theorem endpoints_honest_message :
    HonestMessageLaw (representation (Message.endpoints F) (zeroReference F))
      (ready (Message.endpoints F) (0, 0)) := by
  intro count n context s m h delivered
  cases delivered
  simp [Message.endpoints, Message.endpointPolynomial, zeroReference]

theorem coefficients_honest_message :
    HonestMessageLaw (representation (Message.coefficientTriples F) (zeroReference F))
      (ready (Message.coefficientTriples F) (0, 0, 0)) := by
  intro count n context s m h delivered
  cases delivered
  simp [Message.coefficientTriples, Message.coefficients, Message.ofTriple,
    Zkc.Protocols.Sumcheck.messagePolynomial, zeroReference]

theorem endpoint_honest_execution [DecidableEq F] {n : Nat} (count context : Nat)
    (s : State (zeroReference F) (n + count)) (h : Nat) (r : F)
    (yes : (representation (Message.endpoints F) (zeroReference F)).Yes s) :
    ∃ result final events,
      ((program (Message.endpoints F) (zeroReference F)).remaining count context s).run
        (honestHandler (Message.endpoints F) (0, 0) r) h = ⟨.returned result, final, events⟩ ∧
      (representation (Message.endpoints F) (zeroReference F)).Yes result ∧ True :=
  honest_run (representation _ _) Message.endpoints_laws (zeroLaws 1) _ _ _
    (honestExecution _ _ _) endpoints_honest_message count context s h yes trivial

theorem coefficient_honest_execution [DecidableEq F] {n : Nat} (count context : Nat)
    (s : State (zeroReference F) (n + count)) (h : Nat) (r : F)
    (yes : (representation (Message.coefficientTriples F) (zeroReference F)).Yes s) :
    ∃ result final events,
      ((program (Message.coefficientTriples F) (zeroReference F)).remaining count context s).run
        (honestHandler (Message.coefficientTriples F) (0, 0, 0) r) h = ⟨.returned result, final, events⟩ ∧
      (representation (Message.coefficientTriples F) (zeroReference F)).Yes result ∧ True :=
  honest_run (representation _ _) Message.coefficientTriples_laws (zeroLaws 2) _ _ _
    (honestExecution _ _ _) coefficients_honest_message count context s h yes trivial

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev K := ZMod 7
local instance : SampleableType K := SampleableType.ofFintype K
abbrev endpoints := Message.endpoints K
abbrev reference := zeroReference K
abbrev component := program endpoints reference
abbrev rep := representation endpoints reference
abbrev events := Event (K × K)

theorem small_uniform_bound : (queries endpoints reference).ConditionalBound rep 1 1
    (fun _ _ => 1 / (7 : ENNReal)) := by
  intro k context state allowed m reached p q different left right
  change Pr{let r ← $ᵗ K}[p.eval r = q.eval r] ≤ 1 / (7 : ENNReal)
  simpa only [max_self, Nat.cast_one, ZMod.card, Nat.cast_ofNat] using
    agreement_uniform_le p q different left right

def start (n : Nat) (claim : K) : State reference n := ⟨claim, (), [3], 91⟩

theorem even_length_is_insufficient :
    (List.replicate 6 (0 : K)).length % 2 = 0 ∧
      ¬ ∃ table : Zkc.Polynomial.Multilinear.Table K 2,
        Zkc.Polynomial.Multilinear.ofList? 2 (List.replicate 6 (0 : K)) = some table := by
  constructor
  · rfl
  · rintro ⟨table, decoded⟩
    have shape := Zkc.Polynomial.Multilinear.ofList?_length _ table decoded
    norm_num at shape

theorem zero_rounds_full_return :
    component.remaining 0 17 (start 3 1) = .done (start 3 1) := rfl

/-- No query or delivery theorem is needed for the zero-round derivation. -/
def zero_rounds_derived :
    Derivation (absorb K (K × K)) (boundedEscape (fun _ _ => 0))
      (fun _ result => rep.No result) [] (component.remaining 0 17 (start 3 1)) :=
  .done ⟨trivial, by decide +kernel⟩

theorem malformed_typed_reply :
    component.remaining 1 17 (start 1 0) =
      .call (.receive 17 1) (fun decoded => match decoded with
        | none => .halt .refused
        | some m => if endpoints.boundary m = (0 : K) then
            .call (.challenge 17 1) (fun r =>
              .call (.deliver 17 1 r) (fun _ => .done
                (component.advance 17 (start 1 0) m r)))
          else .halt .reject) := by
  norm_num [component, Program.remaining, program, PIR.Process.bind, start]
  dsimp only [component, program, start]
  funext decoded
  cases decoded <;> simp

/-- This accepted boundary is not an honest zero message. -/
theorem adversarial_message_is_covered :
    endpoints.boundary (0, 1) = (1 : K) ∧
      endpoints.polynomial (0, 1) ≠ reference.polynomial (n := 0) () := by
  constructor
  · decide +kernel
  · exact checked_polynomial_ne (zeroLaws 1) Message.endpoints_laws (n := 0)
      () trivial 1 (by decide +kernel) (0, 1) (by decide +kernel)

theorem receive_cannot_assume_honesty :
    ¬ Nonempty (Derivation (absorb K (K × K)) (boundedEscape (fun _ _ => 0))
      (fun _ result => result = some (0, 0)) []
      (component.receive 17 (start 1 1))) := by
  rintro ⟨proof⟩
  have all := derived_doomed proof
  change ∀ payload value, some payload = some value → value = some (0, 0) at all
  have impossible := all (some (0, 1)) (some (0, 1)) rfl
  exact (by decide +kernel : some ((0, 1) : K × K) ≠ some (0, 0)) impossible

theorem terminal_false_requires_adequacy :
    rep.No (start 0 1) ∧ ¬ (component.claim (start 0 1) = reference.total (n := 0) ()) :=
  ⟨⟨trivial, by decide +kernel⟩, by decide +kernel⟩

theorem invalid_terminal_adequacy_refused :
    ¬ (∀ result : State reference 0, rep.No result → ¬ True) := by
  intro proposed
  exact proposed (start 0 1) terminal_false_requires_adequacy.1 trivial

theorem coefficient_honesty_is_nonvacuous :
    ∃ result final events,
      ((program (Message.coefficientTriples K) reference).remaining 2 17 (start 2 0)).run
        (honestHandler (Message.coefficientTriples K) (0, 0, 0) 2) 4 =
        ⟨.returned result, final, events⟩ ∧
      (representation (Message.coefficientTriples K) reference).Yes result ∧ True :=
  coefficient_honest_execution 2 17 (start 2 0) 4 2 ⟨trivial, rfl⟩

/-- One exact whole-Process equation transports both distinct properties.
The caller shape and mathematical reference are identical in both clauses. -/
theorem one_binding_two_consumers {n : Nat} (count context : Nat)
    (s : State reference (n + count)) (history : List events)
    (actual : PIR.Process (signature K (K × K)) (State reference n))
    (binding : actual = component.remaining count context s) :
    (rep.No s → (reduction (absorb K (K × K)) (fun _ result => rep.No result)
      (fun _ _ => 1 / (7 : ENNReal))).doomed history actual) ∧
    (rep.Yes s → ∃ result final observed,
      actual.run (honestHandler endpoints (0, 0) 2) 0 = ⟨.returned result, final, observed⟩ ∧
      rep.Yes result ∧ True) := by
  constructor
  · intro wrong
    apply derived_doomed
    exact boundResidual rep Message.endpoints_laws (zeroLaws 1) (queries _ _) @small_uniform_bound
      count context s actual binding history wrong
  · intro yes
    exact bound_honest_run rep Message.endpoints_laws (zeroLaws 1) _ _ _
      (honestExecution _ _ _) endpoints_honest_message count context s 0 actual binding yes trivial

def stoppedHandler : PIR.Handler (signature K (K × K)) Nat events
  | .receive context remaining, h => ⟨.stopped .abort, h + 1, [.received context remaining none]⟩
  | .challenge context remaining, h => ⟨.stopped .abort, h + 1, [.queried context remaining]⟩
  | .deliver context remaining _, h => ⟨.stopped .abort, h + 1, [.delivered context remaining]⟩

def oracle (_ : List events) : (event : events) → Id (raw K (K × K) event)
  | .received _ _ _ => pure ()
  | .queried _ _ => pure 2
  | .delivered _ _ => pure ()

def refusingQueryAbsorb : Interface (signature K (K × K)) events (Option (K × K)) (raw K (K × K))
  | .receive context remaining => absorb K (K × K) (.receive context remaining)
  | .challenge context remaining => .query (.queried context remaining) (fun _ => none)
  | .deliver context remaining r => absorb K (K × K) (.deliver context remaining r)

theorem zero_honest_needs_no_services :
    ∃ result final observed,
      (component.remaining 0 17 (start 3 0)).run stoppedHandler 8 = ⟨.returned result, final, observed⟩ ∧
      rep.Yes result ∧ (0 : Nat) = 0 := by
  let inv := fun (remaining : Nat) {n : Nat} (_ : Nat) (_ : State reference n) (_ : Nat) => remaining = 0
  let delivery := fun (_ : Nat) {n : Nat} (_ : Nat) (_ : State reference (n + 1)) (_ : K × K) (_ : Nat) => False
  have sites : HonestRunLaws component stoppedHandler inv delivery := by
    constructor
    · intro remaining n context s h impossible
      exact (Nat.succ_ne_zero remaining impossible).elim
    · intro remaining n context s m h impossible
      exact impossible.elim
  have messages : HonestMessageLaw rep delivery := by
    intro remaining n context s m h impossible
    exact impossible.elim
  exact honest_run rep Message.endpoints_laws (zeroLaws 1) stoppedHandler inv delivery
    sites messages 0 17 (start 3 0) 8 ⟨trivial, rfl⟩ rfl

theorem stop_preserves_prefix :
    (component.remaining 2 17 (start 2 0)).run stoppedHandler 8 =
      ⟨.stopped .abort, 9, [.received 17 2 none]⟩ := rfl

theorem malformed_transform_stops :
    transform (m := Id) (absorb K (K × K)) oracle
      (component.remaining 1 17 (start 1 0)) [] [none] = (.stopped .refused, []) := rfl

theorem missing_message_stops :
    transform (m := Id) (absorb K (K × K)) oracle
      (component.remaining 1 17 (start 1 0)) [] [] = (.stopped .refused, []) := rfl

theorem raw_decode_failure_stops :
    transform (m := Id) refusingQueryAbsorb oracle
      (component.remaining 1 17 (start 1 0)) [] [some (0, 0)] = (.stopped .exhausted, []) := rfl

theorem rejection_precedes_query :
    (component.remaining 1 17 (start 1 0)).run (honestHandler endpoints (1, 0) 2) 4 =
      ⟨.stopped .reject, 5, [.received 17 1 (some (1, 0))]⟩ := rfl

theorem partial_round_keeps_private_state :
    (component.remaining 1 17 (start 3 0)).run (honestHandler endpoints (0, 0) 2) 4 =
      ⟨.returned ⟨0, (), [3, 2], 91⟩, 7,
        [.received 17 3 (some (0, 0)), .queried 17 3, .delivered 17 3]⟩ := rfl

def stoppedDeliveryHandler : PIR.Handler (signature K (K × K)) Nat events
  | .deliver context remaining _, h =>
      ⟨.stopped .abort, h + 1, [.delivered context remaining]⟩
  | operation, h => honestHandler endpoints (0, 0) 2 operation h

theorem delivery_stop_keeps_query_and_prefix :
    (component.remaining 1 17 (start 3 0)).run stoppedDeliveryHandler 4 =
      ⟨.stopped .abort, 7,
        [.received 17 3 (some (0, 0)), .queried 17 3, .delivered 17 3]⟩ := rfl

def withoutDelivery : Program (signature K (K × K)) Nat (State reference) endpoints :=
  { component with deliver := fun _ _ _ _ => .done () }

/-- Even equal final mathematical states do not justify dropping a real send. -/
theorem delivery_cannot_be_erased :
    component.remaining 1 17 (start 3 0) ≠ withoutDelivery.remaining 1 17 (start 3 0) := by
  intro erased
  have counters := congrArg (fun process =>
    (process.run (honestHandler endpoints (0, 0) 2) 4).state) erased
  change (7 : Nat) = 6 at counters
  omega

def historyOracle (history : List events) : (event : events) → Id (raw K (K × K) event)
  | .received _ _ _ => pure ()
  | .queried _ _ => pure (history.length : K)
  | .delivered _ _ => pure ()

/-- The second query sees the first actual delivery as part of its history. -/
theorem delivery_reaches_next_query_history :
    transform (m := Id) (absorb K (K × K)) historyOracle
      (component.remaining 2 17 (start 2 0)) [] [some (0, 0), some (0, 0)] =
      (.returned ⟨0, (), [3, 1, 4], 91⟩, []) := rfl

def interaction : PIR.Interaction (signature K (K × K)) where
  Role := Unit
  Phase := Unit
  owner _ := ()
  enabled _ _ := True
  advance _ _ _ := ()

theorem private_frame_returns {n : Nat} (count context : Nat) (s : State reference (n + count)) :
    PIR.Boundary.Returns interaction (fun result _ => result.privateFrame = s.privateFrame)
      (component.remaining count context s) () :=
  component.returns interaction (fun result => result.privateFrame = s.privateFrame)
    (fun _ _ before _ _ => before) count context s () rfl

def residual_with_private_frame {n : Nat} (count context : Nat)
    (s : State reference (n + count)) (history : List events) (wrong : rep.No s) :
    Derivation (absorb K (K × K)) (boundedEscape (fun _ _ => 1 / (7 : ENNReal)))
      (fun _ result => rep.No result ∧ result.privateFrame = s.privateFrame)
      history (component.remaining count context s) := by
  apply Derivation.frameReturns interaction (fun result => result.privateFrame = s.privateFrame)
    (residual rep Message.endpoints_laws (zeroLaws 1) (queries _ _) @small_uniform_bound count context s history wrong)
    () (private_frame_returns count context s)

/-- The first call leaves two dimensions; the second consumes one more. Both
seams preserve the same private frame and the actual reached history. -/
def two_sequential_calls :
    Derivation (absorb K (K × K)) (boundedEscape (fun _ _ => 1 / (7 : ENNReal)))
      (fun _ result => rep.No result ∧ result.privateFrame = 91) []
      ((component.remaining 1 17 (start 3 1)).bind fun first =>
        component.remaining 1 23 first) := by
  apply (residual_with_private_frame 1 17 (start 3 1) [] ⟨trivial, by decide +kernel⟩).bind
  intro reached first held
  exact (residual_with_private_frame 1 23 first reached held.1).consequence
    (fun _ result next => ⟨next.1, next.2.trans held.2⟩)

def privateToken (n : Nat) : Token (State reference n) :=
  Token.exact (fun s => s.privateFrame = 0)

/-- Falsity can reside solely in the private caller frame while the public
Sumcheck claim is true. The exact callee preserves that residual obligation. -/
def private_residual_call :
    Derivation (absorb K (K × K)) (boundedEscape (fun _ _ => (0 : ENNReal)))
      (fun _ value => Bundle.Doomed [privateToken 2] value) []
      ((component.remaining 1 17 (start 3 0)).bind .done) := by
  apply Derivation.callTokens (before := []) (frameBefore := [privateToken 3])
    (after := []) (frameAfter := [privateToken 2]) rfl
    (fun _ old new => new.privateFrame = old.privateFrame)
    (fun _ _ _ _ _ => Bundle.liveSafe_nil _)
    (fun _ old new same safe token member bad => by
      have tokenEq := List.mem_singleton.mp member
      subst token
      apply safe (privateToken 2) (by simp)
      change new.privateFrame ≠ 0
      rw [same]
      exact bad)
    (start 3 0) ⟨privateToken 3, by simp, by change ¬ (91 = 0); omega⟩ []
    ((Derivation.frameReturns interaction (fun result => result.privateFrame = (start 3 0).privateFrame)
      (ZkcSecurity.Obligations.unrestricted (component.remaining 1 17 (start 3 0)) []) ()
      (private_frame_returns 1 17 (start 3 0))).consequence (fun _ _ holds => holds.2))
  intro reached value bad
  exact .done bad

theorem receive_budget (context : Nat) {n : Nat} (s : State reference (n + 1)) (history : List events) :
    ((absorb K (K × K)).walk ((absorb K (K × K)).lossCharge
      (fun _ _ => 1 / (7 : ENNReal)))).Bound (component.receive context s) history 0 := by
  exact ⟨trivial, (0 : ENNReal), by change (0 : ENNReal) + 0 ≤ 0; simp,
    fun _ _ _ => trivial⟩

theorem delivery_budget (context : Nat) {n : Nat} (s : State reference (n + 1))
    (m : K × K) (r : K) (history : List events) :
    ((absorb K (K × K)).walk ((absorb K (K × K)).lossCharge
      (fun _ _ => 1 / (7 : ENNReal)))).Bound (component.deliver context s m r) history 0 := by
  exact ⟨trivial, (0 : ENNReal), by change (0 : ENNReal) + 0 ≤ 0; simp,
    fun _ _ _ => trivial⟩

theorem actual_schedule_cost {n : Nat} (count context : Nat)
    (s : State reference (n + count)) (history : List events) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound (absorb K (K × K))
      (fun _ _ => 1 / (7 : ENNReal)) (component.remaining count context s) history
      (count • (1 / (7 : ENNReal))) := by
  simpa only [zero_add, add_zero] using Cost.remaining (queries endpoints reference)
    (fun _ _ => 1 / (7 : ENNReal)) 0 (1 / (7 : ENNReal)) 0
    (fun context s history => receive_budget context s history)
    (fun _ _ _ _ => le_rfl) (fun context s m r history => delivery_budget context s m r history)
    count context s history

/-- The return-sensitive cost rule ignores an unreachable expensive suffix. -/
theorem return_sensitive_cost :
    ((absorb K (K × K)).walk ((absorb K (K × K)).lossCharge
      (fun _ _ => (1 : ENNReal)))).Bound
      ((PIR.Process.done true).bind fun flag => if flag then .done true else
        .call (.challenge 17 1) (fun _ => .done false)) [] 0 := by
  exact Walk.Bound.bind_of_returns
    ((absorb K (K × K)).walk ((absorb K (K × K)).lossCharge (fun _ _ => (1 : ENNReal))))
    (fun _ => bot_le) interaction (fun flag _ => flag = true)
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (fun flag => if flag then .done true else .call (.challenge 17 1) (fun _ => .done false))
    (second := 0) (fun flag _ _ same _ => by cases same; trivial)
    (.done true) () [] 0 rfl trivial trivial

theorem wrong_cost_refused :
    ¬ ZkcSecurity.FiatShamir.Typed.ChargedCostBound (absorb K (K × K))
      (fun _ _ => (1 : ENNReal))
      (.call (.challenge 17 1) (fun _ => .done true)) [] 0 := by
  rintro ⟨remaining, bounded, _⟩
  have impossible : (1 : ENNReal) ≤ 0 := (le_add_of_nonneg_right (show (0 : ENNReal) ≤ remaining from bot_le)).trans bounded
  exact (by simp : ¬ (1 : ENNReal) ≤ 0) impossible

theorem shared_challenge_union_is_not_max :
    ¬ Pr{let r ← $ᵗ K}[r = 0 ∨ r = 1] ≤ max (1 / (7 : ENNReal)) (1 / (7 : ENNReal)) := by
  rw [max_self, SampleableType.prEvent_uniformSample]
  have card : (Finset.univ.filter (fun r : K => r = 0 ∨ r = 1)).card = 2 := by decide +kernel
  rw [card, ZMod.card]
  norm_num
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

theorem shared_challenge_union_bound :
    Pr{let r ← $ᵗ K}[r = 0 ∨ r = 1] ≤ 1 / (7 : ENNReal) + 1 / (7 : ENNReal) := by
  apply shared_challenge_union_le
  · rw [SampleableType.prEvent_uniformSample]
    have card : (Finset.univ.filter (fun r : K => r = 0)).card = 1 := by decide +kernel
    rw [card, Nat.cast_one, ZMod.card]
    norm_num
  · rw [SampleableType.prEvent_uniformSample]
    have card : (Finset.univ.filter (fun r : K => r = 1)).card = 1 := by decide +kernel
    rw [card, Nat.cast_one, ZMod.card]
    norm_num

/-- The actual absorbed decoder maps every fresh raw field sample to zero. -/
def biasedAbsorb : Interface (signature K (K × K)) events (Option (K × K)) (raw K (K × K))
  | .challenge context remaining => .query (.queried context remaining) (fun _ => some 0)
  | operation => absorb K (K × K) operation

def biasedQueries : QueryInterface component biasedAbsorb where
  event {n} context _ _ := .queried context (n + 1)
  decode _ _ _ _ := some (0 : K)
  challenge _ _ _ _ := 0
  absorbed _ _ _ := rfl
  decoded _ _ _ _ _ decoded := (Option.some.inj decoded).symm

/-- A well-typed query/decoder is insufficient: a constant pushforward fails
    the advertised 1/7 collision charge. -/
theorem biased_challenge_refused :
    ¬ biasedQueries.ConditionalBound rep 1 1
      (fun _ _ => 1 / (7 : ENNReal)) := by
  intro bound
  have bad := bound 17 (start 1 1) trivial (0, 1) []
    (Polynomial.X : Polynomial K) 0 Polynomial.X_ne_zero (by simp) (by simp)
  change Pr{let _ ← $ᵗ K}[(Polynomial.X : Polynomial K).eval 0 = (0 : Polynomial K).eval 0]
    ≤ 1 / (7 : ENNReal) at bad
  simp only [Polynomial.eval_X, Polynomial.eval_zero] at bad
  rw [prEvent_true_eq_one] at bad
  norm_num at bad

/-- An honest handler cannot admit a reached delivery that stops, regardless
    of how its ready/invariant predicates are named. -/
theorem stopped_delivery_laws_refused :
    ¬ ∃ invariant ready,
      HonestRunLaws component stoppedDeliveryHandler invariant ready ∧
      invariant 1 17 (start 3 0) 4 := by
  rintro ⟨invariant, ready, laws, initial⟩
  obtain ⟨m, received, receiveEvents, _, delivered⟩ := laws.receive 0 17 (start 3 0) 4 initial
  obtain ⟨reply, queried, queryEvents, next, deliveryEvents, _, deliveryEq, _⟩ :=
    laws.query 0 17 (start 3 0) m received delivered
  have impossible := congrArg PIR.Execution.outcome deliveryEq
  change PIR.Outcome.stopped PIR.Stop.abort = PIR.Outcome.returned () at impossible
  cases impossible

/-- The argument of the actual delivery operation is observable. -/
def deliveryObservingHandler : PIR.Handler (signature K (K × K)) (List K) K
  | .receive _ _, h => ⟨.returned (some (0, 0)), h, []⟩
  | .challenge _ _, h => ⟨.returned 2, h, []⟩
  | .deliver _ _ r, h => ⟨.returned (), h ++ [r], [r]⟩

def wrongDeliveryPayload : Program (signature K (K × K)) Nat (State reference) endpoints :=
  { component with deliver := fun {n} context _ _ _ => .call (.deliver context (n + 1) 0) .done }

theorem wrong_delivery_payload_refused :
    component.remaining 1 17 (start 1 0) ≠ wrongDeliveryPayload.remaining 1 17 (start 1 0) := by
  intro equality
  have observed := congrArg (fun p => (p.run deliveryObservingHandler []).state) equality
  change [(2 : K)] = [0] at observed
  exact (by decide +kernel : (2 : K) ≠ 0) (List.cons.inj observed).1

#print axioms biased_challenge_refused
#print axioms stopped_delivery_laws_refused
#print axioms wrong_delivery_payload_refused
#print axioms ZkcSecurity.Obligations.unrestricted
#print axioms Derivation.frameReturns

#print axioms residual
#print axioms honest_run
#print axioms Cost.remaining
#print axioms Walk.Bound.bind_of_returns
#print axioms two_sequential_calls
#print axioms private_residual_call
#print axioms coefficient_honest_execution
#print axioms shared_challenge_union_is_not_max
#print axioms one_binding_two_consumers

end TestsSecurity.SumcheckConsumers
