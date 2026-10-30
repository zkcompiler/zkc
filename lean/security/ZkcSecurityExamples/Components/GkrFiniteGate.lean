module

public import ZkcSecurityExamples.Components.GkrRoundsResidual
public import ZkcSecurityExamples.Components.GkrFiniteCircuit
public import ZkcSecurity.Families.Sumcheck.Completeness

@[expose] public section
noncomputable section

/-! A finite gate-checking component, not the complete multilayer GKR caller.
The imported Rounds verifier runs every variable of the four-factor circuit
reference. The terminal check restricts the original flat factors at the
returned point and compares their gate value with the returned claim. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrFiniteGate
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Polynomial.Multilinear Zkc.Protocols.AlgebraicRounds
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization GkrRoundsGateRealization GkrRoundsResidual
open ZkcExamples.Structured.Generated.Bindings.GkrRounds

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def restrictList (raw : RawState F) (point : List F) : RawState F :=
  point.foldl RawState.restrict raw

def terminalValue (raw : RawState F) : F :=
  Gate.value (raw.add.headD 0) (raw.mul.headD 0) (raw.left.headD 0) (raw.right.headD 0)

/-- The terminal algorithm has no ghost reference argument. -/
def finish (count : Nat) (raw : RawState F)
    (output : Values (Component (assignment F G)) GkrRoundsBinding.spec.state) :
    PIR.Process (participantInterface F G) Bool :=
  match output.get (.there (.there (.there (.there (.there .here))))),
      output.get (.there (.there (.there (.there (.there (.there .here)))))) with
  | some point, some claim =>
    if point.length = count then .done (decide (claim = terminalValue (restrictList raw point)))
    else .halt .refused
  | _, _ => .halt .incomplete

/-- The selected scope is the entire imported Rounds process and this terminal
algorithm. The multilayer caller's remaining continuation is outside it. -/
def verifier (count : Nat) (ctx : ProtocolContext) (service : Nat)
    (raw : RawState F) (claim : F) : PIR.Process (participantInterface F G) Bool :=
  (protocol0Role1Process ctx none none none none (some []) (some claim) (some count) (some service)).bind
    (finish count raw)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem prefix_raw {dimension n : Nat} (raw : RawState F)
    (reference : GkrRoundsReference.State F dimension) (claim : F)
    (s : GkrRoundsBinding.State F n)
    (reachedPrefix : Prefix (GkrRoundsBinding.initial raw reference claim) s) :
    s.raw = restrictList raw s.point := by
  induction reachedPrefix with
  | initial => rfl
  | step s m r _ ih =>
    simp only [GkrRoundsBinding.advance, restrictList, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at *
    rw [← ih]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem terminal_value (raw : RawState F) (reference : GkrRoundsReference.State F 0)
    (decoded : Decodes raw reference) : terminalValue raw = GkrRoundsReference.total reference := by
  have entry (values : List F) (table : Table F 0) (h : ofList? 0 values = some table) :
      values.headD 0 = table Fin.elim0 := by
    have same := ofList?_entry values table h (⟨0, by decide⟩ : Fin (2 ^ 0))
    cases values with
    | nil => simp at same
    | cons a rest => exact Option.some.inj same
  simp only [terminalValue, entry _ _ decoded.1, entry _ _ decoded.2.1,
    entry _ _ decoded.2.2.1, entry _ _ decoded.2.2.2, GkrRoundsReference.total, booleanSum]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Terminal adequacy is derived from the anchored restriction trace. -/
theorem finish_prefix {count : Nat} (raw : RawState F)
    (reference : GkrRoundsReference.State F (0 + count)) (claim : F)
    (represented : Represents raw reference) (s : GkrRoundsBinding.State F 0)
    (reachedPrefix : Prefix (GkrRoundsBinding.initial raw reference claim) s) :
    finish count raw (GkrRoundsBinding.carried (G := G) s) =
      .done (decide (s.claim = GkrRoundsReference.total s.reference)) := by
  have length := prefix_length (GkrRoundsBinding.initial raw reference claim) s reachedPrefix
  have decoded := prefix_representation _ s represented reachedPrefix
  simp only [GkrRoundsBinding.initial, List.length_nil, zero_add, Nat.add_zero] at length
  simp only [finish, GkrRoundsBinding.carried, GkrRoundsBinding.runtime, Values.get,
    length, ite_true]
  rw [← prefix_raw raw reference claim s reachedPrefix, terminal_value s.raw s.reference decoded.1]

/-- One all-answer equation serves honest execution and false-claim reduction.
The source maximum, masks, effects and stops remain operational. -/
theorem binding (count : Nat) (bounded : count ≤ 4) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (service : Nat) (raw : RawState F)
    (reference : GkrRoundsReference.State F (0 + count)) (claim : F)
    (represented : Represents raw reference) :
    verifier (G := G) count ctx service raw claim =
      ((GkrRoundsBinding.program service).remaining (n := 0) count ctx
        (GkrRoundsBinding.initial raw reference claim)).bind
        (fun s => .done (decide (s.claim = GkrRoundsReference.total s.reference))) := by
  unfold verifier
  rw [GkrRoundsBinding.verifier_binding ctx distinct none none none none claim service count bounded
    (n := 0) raw reference, PIR.Process.bind_assoc]
  exact PIR.Boundary.bind_congr_returns interaction _ _ ()
    (returns_prefix service ctx interaction (GkrRoundsBinding.initial raw reference claim) count
      (GkrRoundsBinding.initial raw reference claim) .initial ()) _ _
    (fun s _ reachedPrefix => finish_prefix raw reference claim represented s reachedPrefix)

variable {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
  {absorb : Zkc.Transcript.Interface (participantInterface F G) E P Raw}
  {charge : List E → E → ENNReal}

/-- Arbitrary received triples; only the actual conditional collision law is
assumed. There is no abstract terminal continuation premise. -/
def rejected (count : Nat) (bounded : count ≤ 4) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (service : Nat) (raw : RawState F)
    (reference : GkrRoundsReference.State F (0 + count)) (claim : F)
    (represented : Represents raw reference) (wrong : claim ≠ GkrRoundsReference.total reference)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (history : List E) :
    Zkc.Obligations.Derivation absorb (ZkcSecurity.Obligations.boundedEscape charge)
      (fun _ accepted => accepted = false) history (verifier count ctx service raw claim) := by
  rw [binding count bounded ctx distinct service raw reference claim represented]
  exact (Consumers.residual (GkrRoundsBinding.representation service) Message.coefficientTriples_laws
    GkrRoundsReference.laws queries sampling count ctx (GkrRoundsBinding.initial raw reference claim)
    history ⟨represented.2.1, wrong⟩).bind _
      (fun _ s no => by
        have different : s.claim ≠ GkrRoundsReference.total s.reference := no.2
        exact .done (decide_eq_false different))

/-- Honest handler laws retain actual delivery, resources, state and events. -/
theorem honest_run {H O : Type} (count : Nat) (bounded : count ≤ 4) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (service : Nat) (raw : RawState F)
    (reference : GkrRoundsReference.State F (0 + count)) (claim : F)
    (represented : Represents raw reference) (correct : claim = GkrRoundsReference.total reference)
    (handler : PIR.Handler (participantInterface F G) H O)
    (invariant : Nat → {n : Nat} → ProtocolContext → GkrRoundsBinding.State F n → H → Prop)
    (ready : Nat → {n : Nat} → ProtocolContext → GkrRoundsBinding.State F (n + 1) →
      (F × F × F) → H → Prop)
    (execution : HonestRunLaws (GkrRoundsBinding.program service) handler invariant ready)
    (messages : HonestMessageLaw (GkrRoundsBinding.representation (G := G) service) ready)
    (h : H) (initial : invariant count ctx (GkrRoundsBinding.initial raw reference claim) h) :
    ∃ final events, (verifier (G := G) count ctx service raw claim).run handler h =
      ⟨.returned true, final, events⟩ := by
  rw [binding count bounded ctx distinct service raw reference claim represented]
  obtain ⟨s, final, events, run, yes, _⟩ := Consumers.honest_run
    (GkrRoundsBinding.representation (G := G) service) Message.coefficientTriples_laws
    GkrRoundsReference.laws handler invariant ready execution messages count ctx
    (GkrRoundsBinding.initial raw reference claim) h ⟨represented.2.1, correct⟩ initial
  refine ⟨final, events, ?_⟩
  have equal : s.claim = GkrRoundsReference.total s.reference := yes.2
  simp only [PIR.run_bind, run, PIR.Execution.follow, PIR.Process.run, equal, decide_true,
    List.append_nil]

omit [DecidableEq F] in
/-- Concrete two-wire circuit instance at every field point. -/
theorem circuit_reference (rho : F) :
    Represents (GkrCallerRealization.raw rho) (GkrCallerRealization.reference rho) ∧
    GkrCallerRealization.honestClaim rho =
      GkrRoundsReference.total (GkrCallerRealization.reference rho) :=
  ⟨GkrCallerRealization.represented rho, GkrCallerRealization.honest_control rho⟩

end ZkcSecurity.Examples.Components.GkrFiniteGate
