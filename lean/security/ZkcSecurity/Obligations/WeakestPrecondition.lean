module

public import ZkcSecurity.FiatShamir.Interface
public import Zkc.Obligations.Derivation
public import Std.WP
public import Std.Tactic.Do

@[expose] public section

/-! Local predicate-transformer interpretations of the existing validator process.
The charged reading certifies rejection with abstract escape obligations; the
cost reading bounds every admissible path, including history-dependent prices.
They share the process, not a global WP instance. Adequacy below connects each
reading to its existing judgment. Stops are explicit exception postconditions;
allowing a stop in rejection or cost does not establish honest completeness.
-/

set_option autoImplicit false
namespace ZkcSecurity.Obligations.WeakestPrecondition
open Std.WP Lean.Order Zkc.Transcript Zkc.Obligations ZkcSecurity.FiatShamir

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

/-- The charged reading with the stop postcondition exposed as an exception postcondition:
`halt reason` reads as `epost.1 reason`. zkc's `Charged` is the instance `epost.1 = ⊤`. -/
def chargedWP (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw) {A : Type}
    (process : PIR.Process I A) (post : A → List E → Prop)
    (epost : EStack⟨PIR.Stop → List E → Prop⟩) : List E → Prop :=
  process.foldReplies post epost.1 fun operation next => (absorb operation).ChargedNode escape next

theorem chargedWP_mono (absorb : Interface I E P Raw) {escape : EscapeJudgment E Raw}
    (antitone : escape.Antitone) {A : Type} (process : PIR.Process I A) :
    (⟨chargedWP absorb escape process⟩ : PredTrans (List E → Prop) EStack⟨PIR.Stop → List E → Prop⟩ A).monotone := by
  intro post post' epost epost' hE hP
  exact PIR.Process.foldReplies_mono (absorb.chargedNode_monotone antitone)
    (fun value history inside => hP value history inside)
    (fun reason history inside => hE.1 reason history inside) process

theorem chargedWP_bind (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    {A B : Type} (x : PIR.Process I A) (f : A → PIR.Process I B) post epost :
    chargedWP absorb escape (x.bind f) post epost =
      chargedWP absorb escape x (fun a => chargedWP absorb escape (f a) post epost) epost :=
  PIR.Process.foldReplies_bind _ _ _ x f

/-- The weakest-precondition monad. `absorb` and `escape` are not determined by the program
type, so this is a definition to be installed as a local instance. -/
@[reducible] noncomputable def chargedMonad (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    (antitone : escape.Antitone) :
    WPMonad (PIR.Process I) (List E → Prop) EStack⟨PIR.Stop → List E → Prop⟩ where
  toWP _ := { wpTrans := fun x => ⟨chargedWP absorb escape x⟩,
              wp_trans_monotone := chargedWP_mono absorb antitone }
  pure_le_wp_pure _ _ _ := fun _ h => h
  bind_le_wp_bind x f post epost := by
    intro history h
    change chargedWP absorb escape (x.bind f) post epost history
    rw [chargedWP_bind]; exact h

section Adequacy
variable (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
  (antitone : escape.Antitone)

/-- Adequacy, part 1: the WP at the soundness stop postcondition `⊤` is zkc's `Charged`. -/
theorem wp_eq_charged {A : Type} (Post : List E → A → Prop) (process : PIR.Process I A) :
    (letI := chargedMonad absorb escape antitone
     wp process (fun a h => Post h a) estack⟨fun _ _ => True⟩) =
      absorb.Charged escape Post process := rfl

/-- Adequacy, part 2: a triple with the soundness stop postcondition is exactly a
`Derivation` from every history satisfying the precondition. -/
theorem triple_iff_derivation {A : Type} (pre : List E → Prop) (Post : List E → A → Prop)
    (process : PIR.Process I A) :
    (letI := chargedMonad absorb escape antitone
     Triple process pre (fun a h => Post h a) estack⟨fun _ _ => True⟩) ↔
      ∀ history, pre history → Nonempty (Derivation absorb escape Post history process) := by
  let := chargedMonad absorb escape antitone
  constructor
  · intro ⟨le⟩ history holds
    exact (Derivation.nonempty_iff_charged antitone).mpr (le history holds)
  · intro derive
    exact ⟨fun history holds => (Derivation.nonempty_iff_charged antitone).mp (derive history holds)⟩

end Adequacy

/-- A stop reads as the stop postcondition. -/
theorem halt_spec (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    (antitone : escape.Antitone) {A : Type} (reason : PIR.Stop) (post : A → List E → Prop)
    (epost : EStack⟨PIR.Stop → List E → Prop⟩) :
    (letI := chargedMonad absorb escape antitone
     Triple (PIR.Process.halt reason : PIR.Process I A) (epost.1 reason) post epost) := by
  let := chargedMonad absorb escape antitone
  exact ⟨fun _ h => h⟩

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

@[reducible] noncomputable def costMonad (absorb : Interface I E P Raw) (charge : List E → E → ENNReal) :
    WPMonad (PIR.Process I) (List E → ENNReal → Prop) EStack⟨PIR.Stop → List E → ENNReal → Prop⟩ where
  toWP _ := { wpTrans := fun x => ⟨costWP absorb charge x⟩,
              wp_trans_monotone := fun x post post' epost epost' hE hP =>
                PIR.Process.foldReplies_mono (costNode_mono absorb charge)
                  (fun value history cost inside => hP value history cost inside)
                  (fun reason history cost inside => hE.1 reason history cost inside) x }
  pure_le_wp_pure _ _ _ := fun _ _ h => h
  bind_le_wp_bind x f post epost := by
    intro history cost h
    change costWP absorb charge (x.bind f) post epost history cost
    unfold costWP; rw [PIR.Process.foldReplies_bind]; exact h

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

section ChargedSpecs
variable (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
  (antitone : escape.Antitone)
abbrev ChargedTriple {A : Type} (process : PIR.Process I A) (pre : List E → Prop)
    (post : A → List E → Prop) (epost : EStack⟨PIR.Stop → List E → Prop⟩) : Prop :=
  letI := chargedMonad absorb escape antitone
  Triple process pre post epost

/-- Recover the existing proof object from a checked triple. This does not run
proof search or choose a knowledge extractor. -/
noncomputable def ofTriple {A : Type} {pre : List E → Prop} {Post : List E → A → Prop}
    {process : PIR.Process I A}
    (proof : ChargedTriple absorb escape antitone process pre (fun value history => Post history value) estack⟨fun _ _ => True⟩)
    (history : List E) (holds : pre history) : Derivation absorb escape Post history process :=
  Classical.choice ((triple_iff_derivation absorb escape antitone pre Post process).mp proof history holds)

/-- Reuse a component's checked contract as a WP specification. The returned
value and the reached history remain available to the continuation. -/
theorem derivation_spec {A : Type} (process : PIR.Process I A)
    (pre : List E → Prop) (Post : List E → A → Prop)
    (derive : ∀ history, pre history → Derivation absorb escape Post history process) :
    ChargedTriple absorb escape antitone process pre (fun value history => Post history value) estack⟨fun _ _ => True⟩ :=
  (triple_iff_derivation absorb escape antitone pre Post process).mpr
    fun history holds => ⟨derive history holds⟩

/-- A received value is arbitrary subject only to the actual recovery equation. -/
theorem receive_spec (operation : I.Op) (event : P → E)
    (recover : E → Option (I.Reply operation))
    (absorbed : absorb operation = .receive event recover)
    (post : I.Reply operation → List E → Prop) (epost : EStack⟨PIR.Stop → List E → Prop⟩) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => Lean.Order.iInf fun message => Lean.Order.iInf fun value =>
        Lean.Order.himp ⌜recover (event message) = some value⌝ (post value (history ++ [event message]))) post epost := by
  let := chargedMonad absorb escape antitone
  constructor
  intro history holds
  simp only [iInf_prop_eq_forall, himp_prop_eq_imp, ofProp_prop_eq] at holds
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  exact holds

/-- Sending changes the transcript even though it consumes no proof message. -/
theorem send_spec (operation : I.Op) (event : E) (value : I.Reply operation)
    (absorbed : absorb operation = .send event value)
    (post : I.Reply operation → List E → Prop) (epost : EStack⟨PIR.Stop → List E → Prop⟩) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => post value (history ++ [event])) post epost := by
  let := chargedMonad absorb escape antitone
  constructor
  intro history holds
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  exact holds

/-- The cut is a raw-answer event, fixed before this query. All successful
actual decodings outside the cut must satisfy the continuation. -/
theorem query_spec (operation : I.Op) (event : E)
    (decode : Raw event → Option (I.Reply operation))
    (absorbed : absorb operation = .query event decode) (bad : Raw event → Prop)
    (post : I.Reply operation → List E → Prop) (epost : EStack⟨PIR.Stop → List E → Prop⟩) :
    ChargedTriple absorb escape antitone (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history => Lean.Order.meet ⌜escape history event bad⌝ (Lean.Order.iInf fun raw => Lean.Order.iInf fun value =>
        Lean.Order.himp ⌜decode raw = some value⌝ (Lean.Order.himp ⌜¬ bad raw⌝ (post value (history ++ [event]))))) post epost := by
  let := chargedMonad absorb escape antitone
  constructor
  intro history holds
  simp only [meet_prop_eq_and, iInf_prop_eq_forall, himp_prop_eq_imp, ofProp_prop_eq] at holds
  change (absorb operation).ChargedNode escape _ history
  rw [absorbed]
  refine antitone history event _ bad ?_ holds.1
  rintro raw ⟨value, decoded, outside⟩
  exact Classical.byContradiction fun good => outside (holds.2 raw value decoded good)

/-- An invariant specification for bounded loops; the zero case is a separate
postcondition, so no body assumption can be used for an empty loop. -/
theorem repeat_spec {A : Type} (step : A → PIR.Process I A)
    (invariant : Nat → A → List E → Prop)
    (body : ∀ remaining value, ChargedTriple absorb escape antitone (step value) (invariant (remaining + 1) value)
      (invariant remaining) estack⟨fun _ _ => True⟩) (count : Nat) (value : A) :
    ChargedTriple absorb escape antitone (PIR.repeatN count step value) (invariant count value) (invariant 0)
      estack⟨fun _ _ => True⟩ := by
  let := chargedMonad absorb escape antitone
  constructor
  exact PIR.Process.le_foldReplies_repeatN (absorb.chargedNode_monotone antitone)
    step invariant (fun remaining value => (body remaining value).le_wp) count value

end ChargedSpecs

section CostSpecs
variable (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
abbrev CostTriple {A : Type} (process : PIR.Process I A) (pre : List E → ENNReal → Prop)
    (post : A → List E → ENNReal → Prop) (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) : Prop :=
  letI := costMonad absorb charge
  Triple process pre post epost

theorem halt_cost {A : Type} (reason : PIR.Stop) (post : A → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) :
    CostTriple absorb charge (PIR.Process.halt reason : PIR.Process I A) (epost.1 reason) post epost := by
  let := costMonad absorb charge
  exact ⟨fun _ _ holds => holds⟩

theorem receive_cost (operation : I.Op) (event : P → E)
    (recover : E → Option (I.Reply operation)) (absorbed : absorb operation = .receive event recover)
    (post : I.Reply operation → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => Lean.Order.iInf fun message => Lean.Order.iInf fun value =>
        Lean.Order.himp ⌜recover (event message) = some value⌝ (post value (history ++ [event message]) cost))
      post epost := by
  let := costMonad absorb charge
  constructor
  intro history cost holds
  simp only [iInf_prop_eq_forall, himp_prop_eq_imp, ofProp_prop_eq] at holds
  change costNode absorb charge operation _ history cost
  rw [costNode, absorbed]
  exact holds

theorem send_cost (operation : I.Op) (event : E) (value : I.Reply operation)
    (absorbed : absorb operation = .send event value)
    (post : I.Reply operation → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => post value (history ++ [event]) cost) post epost := by
  let := costMonad absorb charge
  constructor
  intro history cost holds
  change costNode absorb charge operation _ history cost
  rw [costNode, absorbed]
  exact holds

/-- Pay at the reached history, without subtracting infinities or assuming a
finite price. The continuation budget is explicit, and covers every reply. -/
theorem query_cost (operation : I.Op) (event : E)
    (decode : Raw event → Option (I.Reply operation)) (absorbed : absorb operation = .query event decode)
    (remaining : ENNReal) (post : I.Reply operation → List E → ENNReal → Prop)
    (epost : EStack⟨PIR.Stop → List E → ENNReal → Prop⟩) :
    CostTriple absorb charge (.call operation .done : PIR.Process I (I.Reply operation))
      (fun history cost => Lean.Order.meet ⌜charge history event + remaining ≤ cost⌝
        (Lean.Order.iInf fun value => post value (history ++ [event]) remaining)) post epost := by
  let := costMonad absorb charge
  constructor
  intro history cost holds
  simp only [meet_prop_eq_and, iInf_prop_eq_forall, ofProp_prop_eq] at holds
  change costNode absorb charge operation _ history cost
  rw [costNode, absorbed]
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
    (post : A → List E → ENNReal → Prop) :
    CostTriple absorb charge process
      (fun _ cost => Lean.Order.meet ⌜bound + remaining ≤ cost⌝ (Lean.Order.iInf fun value =>
        Lean.Order.iInf fun reached => Lean.Order.iInf fun available =>
          Lean.Order.himp ⌜remaining ≤ available⌝ (post value reached available)))
      post estack⟨fun _ _ _ => True⟩ := by
  let := costMonad absorb charge
  constructor
  intro history cost holds
  simp only [meet_prop_eq_and, iInf_prop_eq_forall, himp_prop_eq_imp, ofProp_prop_eq] at holds
  exact PIR.Process.foldReplies_mono (costNode_mono absorb charge)
    (fun value reached available enough => holds.2 value reached available enough)
    (fun _ _ _ inside => inside) process history cost
    (reserve absorb charge remaining process history bound cost (bounded history) holds.1)

/-- A resource invariant for a bounded loop. A body specification is used only
at a positive remaining count; the terminal invariant supplies the zero case. -/
theorem repeat_cost_spec {A : Type} (step : A → PIR.Process I A)
    (invariant : Nat → A → List E → ENNReal → Prop)
    (body : ∀ remaining value, CostTriple absorb charge (step value)
      (invariant (remaining + 1) value) (invariant remaining) estack⟨fun _ _ _ => True⟩)
    (count : Nat) (value : A) :
    CostTriple absorb charge (PIR.repeatN count step value) (invariant count value)
      (invariant 0) estack⟨fun _ _ _ => True⟩ := by
  let := costMonad absorb charge
  constructor
  exact PIR.Process.le_foldReplies_repeatN (costNode_mono absorb charge)
    step invariant (fun remaining value => (body remaining value).le_wp) count value

/-- The cost triple's accepted boundary is precisely the existing pathwise bound. -/
theorem cost_of_triple {A : Type} {process : PIR.Process I A} {pre : List E → ENNReal → Prop}
    (proof : CostTriple absorb charge process pre (fun _ _ _ => True) estack⟨fun _ _ _ => True⟩)
    (history : List E) (cost : ENNReal) (holds : pre history cost) :
    Typed.ChargedCostBound absorb charge process history cost := by
  let := costMonad absorb charge
  exact (costWP_iff absorb charge process history cost).mp (proof.le_wp history cost holds)

end CostSpecs

end ZkcSecurity.Obligations.WeakestPrecondition
