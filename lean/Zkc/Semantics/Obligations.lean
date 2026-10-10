import Zkc.Semantics.Relation

/-! Finite, ordered derivations of reusable obligations.

The caller chooses `Claim`, including every relevant subject, context and value.
`check` compares exact claims against independently supplied source requirements;
deleting candidate rules cannot delete those requirements. It checks availability,
not truth, rule validity, terminal execution or correspondence with a native body.

For soundness, fix `holds` and each rule's `bad` event at the actual execution.
Supply sound terminal facts and a sound interpretation of every candidate rule.
Open residuals may be added to the seed list only under the same explicit semantic
assumptions. Logical facts are reusable; transcript and resource disciplines stay
with the existing execution/interaction interfaces. No probability bound is given.
-/

set_option autoImplicit false

namespace PIR.Obligations

variable {Claim : Type}

/-- One reduction instance: all prerequisites justify its conclusion. A rule
with no prerequisites still needs a semantic law; syntax does not establish it. -/
structure Rule (Claim : Type) where
  prerequisites : List Claim
  conclusion : Claim
  deriving DecidableEq, Repr

/-- A law for the chosen execution, supplied separately from structural checking.
`bad` must describe an explicitly admitted exceptional event of that execution. -/
def Rule.Sound (holds : Claim → Prop) (bad : Prop) (rule : Rule Claim) : Prop :=
  (∀ claim ∈ rule.prerequisites, holds claim) → holds rule.conclusion ∨ bad

/-- Each demand is checked independently; multiplicity does not consume facts. -/
def covers [DecidableEq Claim] (available requirements : List Claim) : Bool :=
  requirements.all (fun claim => decide (claim ∈ available))

@[simp] theorem covers_eq_true [DecidableEq Claim] {available requirements : List Claim} :
    covers available requirements = true ↔ ∀ claim ∈ requirements, claim ∈ available := by
  simp [covers]

/-- Check in the supplied order, retaining every earlier fact. An unavailable
prerequisite rejects the whole derivation, even if its conclusion is not required.
This is a certificate checker, not a search for a possible ordering. -/
def derive [DecidableEq Claim] (available : List Claim) :
    List (Rule Claim) → Option (List Claim)
  | [] => some available
  | rule :: rest =>
      if covers available rule.prerequisites then
        derive (rule.conclusion :: available) rest
      else none

/-- `requirements` comes from the source independently of the candidate `rules`.
`terminals` names supplied facts; checking does not itself justify their truth. -/
def check [DecidableEq Claim] (requirements terminals : List Claim)
    (rules : List (Rule Claim)) : Bool :=
  match derive terminals rules with
  | none => false
  | some available => covers available requirements

theorem check_eq_true [DecidableEq Claim] {requirements terminals : List Claim}
    {rules : List (Rule Claim)} :
    check requirements terminals rules = true ↔
      ∃ available, derive terminals rules = some available ∧
        ∀ claim ∈ requirements, claim ∈ available := by
  cases run : derive terminals rules <;> simp [check, run]

/-- Independently supplied ordered certificates compose using the actual facts
returned by the first. Failure in either segment remains failure. -/
theorem derive_append [DecidableEq Claim] (available : List Claim)
    (first second : List (Rule Claim)) :
    derive available (first ++ second) =
      (derive available first).bind (fun middle => derive middle second) := by
  induction first generalizing available with
  | nil => rfl
  | cons rule rest ih =>
      simp only [List.cons_append, derive]
      split <;> simp_all

/-- Instantiate every subject in a rule together. This is a map of actual
claims, not permission to identify unrelated keys, roles or invocation sites. -/
def Rule.map {Target : Type} (substitute : Claim → Target) (rule : Rule Claim) : Rule Target :=
  ⟨rule.prerequisites.map substitute, substitute rule.conclusion⟩

/-- Semantic instantiation uses the target predicate pulled back through the
actual substitution. Renaming alone cannot establish a property of the target. -/
theorem Rule.Sound.map {Target : Type} (substitute : Claim → Target)
    (holds : Target → Prop) (bad : Prop) {rule : Rule Claim}
    (law : rule.Sound (fun claim => holds (substitute claim)) bad) :
    (rule.map substitute).Sound holds bad := by
  intro premises
  apply law
  intro claim member
  exact premises (substitute claim) (List.mem_map.mpr ⟨claim, member, rfl⟩)

theorem covers_map {Target : Type} [DecidableEq Claim] [DecidableEq Target]
    (substitute : Claim → Target) {available required : List Claim}
    (accepted : covers available required = true) :
    covers (available.map substitute) (required.map substitute) = true := by
  rw [covers_eq_true] at accepted ⊢
  intro target member
  obtain ⟨claim, needed, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨claim, accepted claim needed, rfl⟩

/-- An accepted component derivation can be instantiated at an actual call.
The converse needs stronger hypotheses: a noninjective map can merge facts.
Semantic validity of instantiated laws is a separate premise of check_sound. -/
theorem derive_map {Target : Type} [DecidableEq Claim] [DecidableEq Target]
    (substitute : Claim → Target) {available result : List Claim}
    {rules : List (Rule Claim)} (accepted : derive available rules = some result) :
    derive (available.map substitute) (rules.map (Rule.map substitute)) =
      some (result.map substitute) := by
  induction rules generalizing available with
  | nil =>
      cases accepted
      rfl
  | cons rule rest ih =>
      simp only [derive] at accepted
      split at accepted
      next covered =>
        have mapped := covers_map substitute covered
        simpa only [List.map_cons, derive, Rule.map, mapped, if_true] using ih accepted
      next => contradiction

theorem check_map {Target : Type} [DecidableEq Claim] [DecidableEq Target]
    (substitute : Claim → Target) {required terminals : List Claim}
    {rules : List (Rule Claim)} (accepted : check required terminals rules = true) :
    check (required.map substitute) (terminals.map substitute)
      (rules.map (Rule.map substitute)) = true := by
  obtain ⟨available, derived, covered⟩ := check_eq_true.mp accepted
  apply check_eq_true.mpr
  refine ⟨available.map substitute, derive_map substitute derived, ?_⟩
  exact covers_eq_true.mp (covers_map substitute (covers_eq_true.mpr covered))

/-- Later derivations can reuse every fact established by an earlier segment. -/
theorem derive_preserves [DecidableEq Claim] {available result : List Claim}
    {rules : List (Rule Claim)} (accepted : derive available rules = some result) :
    ∀ claim ∈ available, claim ∈ result := by
  induction rules generalizing available with
  | nil =>
      cases accepted
      exact fun _ member => member
  | cons rule rest ih =>
      simp only [derive] at accepted
      split at accepted
      · intro claim member
        exact ih accepted claim (List.mem_cons_of_mem _ member)
      · contradiction

/-- Repeated or combined demands never replace another independently required
root. The same derivation can discharge both lists without consuming evidence. -/
theorem check_requirements_append [DecidableEq Claim]
    (first second terminals : List Claim) (rules : List (Rule Claim)) :
    check (first ++ second) terminals rules = true ↔
      check first terminals rules = true ∧ check second terminals rules = true := by
  cases run : derive terminals rules <;> simp [check, run, covers, List.all_append]

/-- A successful derivation preserves semantic truth when none of its admitted
bad events occurs. Every candidate rule needs its own interpretation premise. -/
theorem derive_sound [DecidableEq Claim] (holds : Claim → Prop)
    (bad : Rule Claim → Prop) {terminals available : List Claim}
    {rules : List (Rule Claim)}
    (terminalSound : ∀ claim ∈ terminals, holds claim)
    (ruleSound : ∀ rule ∈ rules, rule.Sound holds (bad rule))
    (noBad : ∀ rule ∈ rules, ¬ bad rule)
    (accepted : derive terminals rules = some available) :
    ∀ claim ∈ available, holds claim := by
  induction rules generalizing terminals with
  | nil =>
      cases accepted
      exact terminalSound
  | cons rule rest ih =>
      simp only [derive] at accepted
      split at accepted
      next ready =>
        have prerequisites := covers_eq_true.mp ready
        have conclusion : holds rule.conclusion :=
          (ruleSound rule (by simp) (fun claim member =>
            terminalSound claim (prerequisites claim member))).resolve_right
              (noBad rule (by simp))
        apply ih (terminals := rule.conclusion :: terminals) _ _ _ accepted
        · intro claim member
          rcases List.mem_cons.mp member with same | previous
          · exact same ▸ conclusion
          · exact terminalSound claim previous
        · intro next member
          exact ruleSound next (List.mem_cons_of_mem _ member)
        · intro next member
          exact noBad next (List.mem_cons_of_mem _ member)
      next => contradiction

theorem check_sound_of_not_bad [DecidableEq Claim] (holds : Claim → Prop)
    (bad : Rule Claim → Prop) {requirements terminals : List Claim}
    {rules : List (Rule Claim)}
    (terminalSound : ∀ claim ∈ terminals, holds claim)
    (ruleSound : ∀ rule ∈ rules, rule.Sound holds (bad rule))
    (noBad : ∀ rule ∈ rules, ¬ bad rule)
    (accepted : check requirements terminals rules = true) :
    ∀ claim ∈ requirements, holds claim := by
  obtain ⟨available, run, covered⟩ := check_eq_true.mp accepted
  intro claim member
  exact derive_sound holds bad terminalSound ruleSound noBad run claim (covered claim member)

/-- All independently required roots hold together, or a bad event of one of the
supplied rules occurs. This is a logical disjunction, not a security bound. -/
theorem check_sound [DecidableEq Claim] (holds : Claim → Prop)
    (bad : Rule Claim → Prop) {requirements terminals : List Claim}
    {rules : List (Rule Claim)}
    (terminalSound : ∀ claim ∈ terminals, holds claim)
    (ruleSound : ∀ rule ∈ rules, rule.Sound holds (bad rule))
    (accepted : check requirements terminals rules = true) :
    (∀ claim ∈ requirements, holds claim) ∨ ∃ rule ∈ rules, bad rule := by
  classical
  by_cases occurred : ∃ rule ∈ rules, bad rule
  · exact Or.inr occurred
  · exact Or.inl (check_sound_of_not_bad holds bad terminalSound ruleSound
      (fun rule member event => occurred ⟨rule, member, event⟩) accepted)

/-- The finite checker supplies the existing reduction interface. Truth of the
actual terminal seeds remains the contract's residual premise; clients can use
`ReductionContract.then` or `terminal_sound` without a second composition law. -/
theorem check_reduction [DecidableEq Claim] (holds : Claim → Prop)
    (bad : Rule Claim → Prop) {requirements terminals : List Claim}
    {rules : List (Rule Claim)}
    (ruleSound : ∀ rule ∈ rules, rule.Sound holds (bad rule))
    (accepted : check requirements terminals rules = true) :
    Relation.ReductionContract
      (fun required => ∀ claim ∈ required, holds claim)
      (fun facts => ∀ claim ∈ facts, holds claim)
      requirements terminals (∃ rule ∈ rules, bad rule) :=
  ⟨fun terminalSound => check_sound holds bad terminalSound ruleSound accepted⟩

end PIR.Obligations
