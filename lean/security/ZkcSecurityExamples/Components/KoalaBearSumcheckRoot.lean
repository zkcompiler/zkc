module

public import ZkcSecurityExamples.Components.KoalaBearSumcheckRootSource
public import ZkcSecurityExamples.Components.KoalaBearSumcheckHonest

@[expose] public section

/-! Complete source root acceptance. The same actual/readback equation used by
the family contract is composed with a pure terminal component through Connection.
All parameters are actual base inputs; the challenge is arbitrary in Octic. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 400000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Domains.KoalaBear (Base Octic q embed)
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity)
open ZkcSecurity.Examples.Components.KoalaBearSumcheck

local instance : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event) := rawSampleable
local instance : SampleableType Octic := sampleable octicIdentity
local instance : DecidableEq (model.Field octicIdentity) := model.fieldDecEq octicIdentity

def initialClaim {Frame : Type} (a b claim : Base) (frame : Frame) : State Frame 1 :=
  EmbeddingPrefix.State.initial [a, b] 1 (embed claim) frame rfl

def verifier (a b claim : Base) (handle : Nat) : PIR.Process I (Option Bool) :=
  (KoalaBearSumcheckSource.rootVerifier a b claim handle).bind (fun out => .done (out.get .here))

def producer (a b : Base) := KoalaBearSumcheckSource.rootProducer a b

def finish {Frame : Type} (state : State Frame 0) : PIR.Process I (Option Bool) :=
  .done (some (decide (state.scalar = (layout.entries state).sum)))

/-- The embedded base table is restricted at the actual octic challenge. -/
theorem terminal_entries {Frame : Type} (a b claim : Base) (frame : Frame)
    (message : Octic × Octic) (r : Octic) :
    (layout.entries ((initialClaim a b claim frame).advance message r)).sum =
      embed a + (embed b - embed a) * r := by
  change (((initialClaim a b claim frame).advance message r).entries embed).sum = _
  rw [EmbeddingPrefix.State.advance_entries]
  change (Zkc.Polynomial.Multilinear.restrictValues [embed a, embed b] r).sum = _
  simp [Zkc.Polynomial.Multilinear.restrictValues]

/-- Complete open Process equation, including every received pair, reply and
failure. No truth premise and no table argument to the Round verifier. -/
theorem binding {Frame : Type} (a b claim : Base) (frame : Frame) (handle : Nat) :
    verifier a b claim handle = (actual (handle, initialClaim a b claim frame)).bind finish := by
  rw [verifier, KoalaBearSumcheckSource.root_verifier_equation]
  change ((KoalaBearSumcheckSource.verifier [] (embed claim) handle).bind (KoalaBearSumcheckSource.terminal a b)).bind
      (fun out => .done (out.get .here)) =
    ((KoalaBearSumcheckSource.verifier [] (embed claim) handle).bind (readback (initialClaim a b claim frame))).bind finish
  simp_rw [KoalaBearSumcheckSource.verifier_equation, PIR.Process.bind_assoc]
  simp only [KoalaBearSumcheckSource.verifierView, PIR.Process.bind]
  apply PIR.Process.call_congr
  intro low
  change Octic at low
  apply PIR.Process.call_congr
  intro high
  change Octic at high
  by_cases boundary : low + high = embed claim
  · simp only [ite_eq_left boundary, PIR.Process.bind]
    apply PIR.Process.call_congr
    intro r
    change Octic at r
    apply PIR.Process.call_congr
    intro delivered
    have rb := readback_complete (initialClaim a b claim frame) (low + (high - low) * r) r
    have advanced := EmbeddingPrefix.State.readback_advance (initialClaim a b claim frame) low high r
    have final : finish ((initialClaim a b claim frame).advance (low, high) r) =
        PIR.Process.done (some (decide (low + (high - low) * r = embed a + (embed b - embed a) * r))) := by
      unfold finish
      rw [terminal_entries a b claim frame (low, high) r,
        congrArg (fun state : State Frame 0 => state.scalar) advanced.symm]
    calc
      _ = PIR.Process.done (some (decide (low + (high - low) * r = embed a + (embed b - embed a) * r))) := by
        rw [KoalaBearSumcheckSource.terminal_complete a b (low + (high - low) * r) r]
        rfl
      _ = finish ((initialClaim a b claim frame).advance (low, high) r) := final.symm
      _ = finish { (initialClaim a b claim frame).advance (0, 0) r with scalar := low + (high - low) * r } :=
        congrArg finish advanced.symm
      _ = (readback (initialClaim a b claim frame)
          (.cons (some (low + (high - low) * r)) (.cons (some r) .nil))).bind finish :=
        (congrArg (fun process => process.bind finish) rb).symm

  · simp only [ite_eq_right boundary, PIR.Process.bind]

def acceptedRelation : ClaimRelation (Option Bool) Unit where
  Holds decision _ := decision = some true
  No decision := decision ≠ some true
  no_excludes _ _ no yes := no yes

def terminalComponent {Frame : Type} : ComponentInterface I Event (State Frame 0) (Option Bool) where
  Parameters := Unit
  Input := State Frame 0
  InputWitness := Unit
  Output := Option Bool
  OutputWitness := Unit
  input := representation.relation 0
  output := acceptedRelation
  body := finish
  Scope _ _ _ := True
  inputView _ state _ := some state
  outputView _ _ _ result := some result

def terminal_soundness {Frame : Type} : SoundnessContract (terminalComponent (Frame := Frame)) absorb
    (ZkcSecurity.Obligations.boundedEscape (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal))) := by
  intro parameters state history scope wrong
  have no : representation.No state := ReadbackHolds.some.mp wrong
  have unequal := (layout.no_iff state).mp no
  change state.scalar ≠ (layout.entries state).sum at unequal
  apply Derivation.done
  refine ⟨_, rfl, ?_⟩
  change some (decide (state.scalar = (layout.entries state).sum)) ≠ some true
  intro same
  exact unequal (of_decide_eq_true (Option.some.inj same))

def connection {Frame : Type} : Connection
    (Contract.component (representation (Frame := Frame)) 0 1 actual) (terminalComponent (Frame := Frame)) where
  parameters := id
  route _ state := state
  map := id
  square _ _ _ _ _ same := by cases Option.some.inj same; rfl

/-- False input is exactly the complement of the actual source relation. -/
theorem initial_no {Frame : Type} (a b claim : Base) (frame : Frame)
    (wrong : ¬ KoalaBearSumcheckSource.sumRelation a b claim) : representation.No (initialClaim a b claim frame) := by
  apply (layout.no_iff _).mpr
  change embed claim ≠ (embed a + (embed b + 0))
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using (mt (KoalaBearSumcheckSource.sumRelation_embedded a b claim).mpr wrong)

/-- The unchanged family contract plus the exact terminal connection give full
root rejection at the exact octic charge. No family induction is repeated. -/
def soundness (a b claim : Base) (handle : Nat) (history : List Event)
    (wrong : ¬ KoalaBearSumcheckSource.sumRelation a b claim) :
    Derivation absorb
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal)))
      (fun _ decision => decision ≠ some true) history (verifier a b claim handle) := by
  let runtime := (handle, initialClaim a b claim ())
  have derived := connection.bind (ClaimRelation.SoundLink.id _)
    (octic_soundness 0) terminal_soundness () runtime history trivial
    (ReadbackHolds.some.mpr (initial_no a b claim () wrong))
    (fun _ _ _ => trivial) (fun _ decision => decision ≠ some true)
    (fun _ _ decision no => by
      change ReadbackHolds (fun out : Option Bool => out ≠ some true) (some decision) at no
      exact (ReadbackHolds.some (predicate := fun out : Option Bool => out ≠ some true)).mp no)
  exact derived.transport (binding a b claim () handle)

/-- A nominal source endpoint export, anchored to the complete actual process.
This is deliberately distinct from a compiled-pair fixed receipt. -/
def soundnessExport (a b claim : Base) (handle : Nat) (history : List Event)
    (wrong : ¬ KoalaBearSumcheckSource.sumRelation a b claim) :=
  ZkcSecurity.Obligations.exportCapability (soundness a b claim handle history wrong)

/-- Every path through the actual root makes at most one ideal octic query. -/
theorem query_bound (a b claim : Base) (handle : Nat) :
    ZkcSecurity.FiatShamir.Typed.QueryBound absorb (verifier a b claim handle) 1 := by
  rw [verifier, KoalaBearSumcheckSource.root_verifier_equation,
    KoalaBearSumcheckSource.verifier_equation]
  intro low high
  change Octic at low high
  simp_rw [PIR.Process.bind_ite]
  by_cases boundary : low + high = embed claim
  · simp only [ite_eq_left boundary]
    change 0 < 1 ∧ ∀ _r : Octic, True
    exact ⟨by decide, fun _ => trivial⟩
  · simp only [ite_eq_right boundary]
    trivial

/-- Reusable nominal source endpoint. Its terminal adequacy is the complete
root acceptance predicate, and its price is the selected octic sampler's. -/
def sourceCertificate : ZkcSecurity.FiatShamir.Typed.ChargedCertificate absorb
    (fun decision : Option Bool => decision = some true)
    (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal)) :=
  (ZkcSecurity.Obligations.reduction absorb
    (fun (_ : List Event) (decision : Option Bool) => decision ≠ some true)
    (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal))).toCertificate absorb
      (fun _ _ no => no)

theorem source_certificate_association : sourceCertificate.doomed =
    (ZkcSecurity.Obligations.reduction absorb
      (fun (_ : List Event) (decision : Option Bool) => decision ≠ some true)
      (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal))).doomed := by
  kernel_rfl

/-- The adapter is independent of the selected source body. -/
theorem source_certificate_from_derivation (history : List Event)
    (process : PIR.Process I (Option Bool))
    (derivation : Derivation absorb
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal)))
      (fun _ decision => decision ≠ some true) history process) :
    sourceCertificate.doomed history process := by
  rw [source_certificate_association]
  exact ZkcSecurity.Obligations.derived_doomed derivation

attribute [local irreducible] verifier

/-- Canonical subject association remains external; this theorem is anchored
to the admitted source Process, with no compiled-artifact assertion. -/
theorem source_doomed (a b claim : Base) (handle : Nat) (history : List Event)
    (wrong : ¬ KoalaBearSumcheckSource.sumRelation a b claim) :
    sourceCertificate.doomed history (verifier a b claim handle) := by
  have reading := soundness a b claim handle history wrong
  have derived := source_certificate_from_derivation history (verifier a b claim handle) reading
  exact derived

/-- Actual Root producer sends the same endpoint packets as its admitted Round. -/
theorem producer_run (a b : Base) (r : Octic) :
    (producer a b).run (producerHandler r) () =
      ⟨.returned (.cons none .nil), (), packets (embed a, embed b)⟩ := by
  rw [producer, KoalaBearSumcheckSource.root_producer_equation, PIR.run_bind, KoalaBearSumcheck.producer_run]
  rfl

/-- Full root acceptance from the actual producer, for all actual inputs and
all octic challenges, retaining the handler's complete execution and events. -/
theorem completeness {Frame : Type} (a b : Base) (frame : Frame) (handle : Nat) (r : Octic) :
    ∃ events,
      (verifier a b (a + b) handle).run handler
        (((producer a b).run (producerHandler r) ()).events, [r]) =
        ⟨.returned (some true), ([], []), events⟩ := by
  rw [binding a b (a + b) frame handle, producer_run]
  have initialEq : initialClaim a b (a + b) frame = initial a b frame := rfl
  rw [initialEq]
  obtain ⟨result, events, ran, yes⟩ := honest_run handle (initial a b frame) r
    (by simpa only [initial, List.sum_cons, List.sum_nil, add_zero] using
      (initial_yes [a, b] 1 frame rfl))
  refine ⟨events, ?_⟩
  change ((actual (handle, initial a b frame)).bind finish).run handler (packets (embed a, embed b), [r]) = _
  rw [← initial_endpoints a b frame, PIR.run_bind, ran]
  have truth := (layout.yes_iff result).mp yes
  change result.scalar = (layout.entries result).sum at truth
  simp only [PIR.Execution.follow, PIR.Process.run, finish, List.append_nil]
  simp only [truth, decide_true]

end ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot
