import Zkc.Semantics.Obligations

/-! Executable controls and semantic countermodels for finite obligations. -/

set_option autoImplicit false

namespace Tests.Obligations

open PIR.Obligations

inductive Kind where
  | terminal | left | right | root
  deriving DecidableEq, Repr

/-- Identical shapes do not identify distinct subjects or execution contexts. -/
structure Claim where
  kind : Kind
  subject : Nat
  context : Nat
  deriving DecidableEq, Repr

def seed : Claim := ⟨.terminal, 7, 11⟩
def otherSeed : Claim := ⟨.terminal, 8, 11⟩
def left : Claim := ⟨.left, 7, 11⟩
def right : Claim := ⟨.right, 7, 11⟩
def root : Claim := ⟨.root, 7, 11⟩

def leftRule : Rule Claim := ⟨[seed], left⟩
def rightRule : Rule Claim := ⟨[seed, otherSeed], right⟩
def rootRule : Rule Claim := ⟨[left, right], root⟩
def rules : List (Rule Claim) := [leftRule, rightRule, rootRule]

/-- The seed is reused across two branches; the root requires both branches. -/
theorem shared_premise : check [root] [seed, otherSeed] rules = true := by decide

theorem actual_available_facts :
    derive [seed, otherSeed] rules = some [root, right, left, seed, otherSeed] := by decide

/-- Instantiate the same component derivation at another actual call context. -/
theorem renamed_call :
    check ([root].map (fun c => { c with context := 42 }))
      ([seed, otherSeed].map (fun c => { c with context := 42 }))
      (rules.map (Rule.map (fun c => { c with context := 42 }))) = true :=
  check_map (fun c => { c with context := 42 }) shared_premise

/-- Claim mapping is directional. Forgetting subjects can turn a refused
derivation into an accepted one, so it cannot justify source/subject erasure. -/
theorem lossy_map_not_reflection :
    check [seed] [otherSeed] [] = false ∧
    check ([seed].map Claim.kind) ([otherSeed].map Claim.kind) [] = true := by
  decide

theorem duplicate_demand : check [root, root] [seed, otherSeed] rules = true := by decide

theorem duplicate_prerequisite :
    check [left] [seed] [⟨[seed, seed], left⟩] = true := by decide

/-- Repeating the covered root cannot conceal the distinct missing subject. -/
theorem duplicate_does_not_hide_missing_demand :
    check [root, root, { root with subject := 9 }] [seed, otherSeed] rules = false := by
  decide

theorem whole_chain_omission : check [root] [seed, otherSeed] [] = false := by decide

theorem missing_terminal : check [root] [seed] rules = false := by decide

theorem missing_branch :
    check [root] [seed, otherSeed] [leftRule, rootRule] = false := by decide

theorem swapped_subject :
    check [root] [{ seed with subject := 9 }, otherSeed] rules = false := by decide

theorem swapped_context :
    check [root] [{ seed with context := 12 }, otherSeed] rules = false := by decide

/-- Even a coordinated replacement of a terminal and rule cannot replace the
independently retained original source requirement. -/
theorem coordinated_subject_replacement :
    check [left] [{ seed with subject := 9 }]
      [⟨[{ seed with subject := 9 }], { left with subject := 9 }⟩] = false := by decide

theorem coordinated_context_replacement :
    check [left] [{ seed with context := 12 }]
      [⟨[{ seed with context := 12 }], { left with context := 12 }⟩] = false := by decide

theorem unseeded_cycle :
    check [left, right] [] [⟨[right], left⟩, ⟨[left], right⟩] = false := by decide

theorem unseeded_self_cycle :
    check [left] [] [⟨[left], left⟩] = false := by decide

/-- A graph cycle is harmless when its ordered uses already have a seed. -/
theorem seeded_cycle :
    check [left, right] [right] [⟨[right], left⟩, ⟨[left], right⟩] = true := by decide

theorem forward_reference :
    check [root] [seed, otherSeed] [rootRule, leftRule, rightRule] = false := by decide

/-- An already covered root does not excuse a malformed extra rule. -/
theorem malformed_unused_rule : check [seed] [seed] [rootRule] = false := by decide

theorem empty_source : check ([] : List Claim) [] [] = true := by decide

theorem terminal_only : check [seed] [seed] [] = true := by decide

/-- A supplied open residual is usable structurally, but its truth is still a
premise of every semantic soundness theorem. -/
theorem explicit_residual : check [root] [left, right] [rootRule] = true := by decide

theorem unstated_residual : check [root] [left] [rootRule] = false := by decide

theorem segmented_derivation :
    derive [seed, otherSeed] ([leftRule, rightRule] ++ [rootRule]) =
      (derive [seed, otherSeed] [leftRule, rightRule]).bind
        (fun available => derive available [rootRule]) :=
  derive_append _ _ _

theorem prefix_fact_reused : left ∈ [root, right, left, seed, otherSeed] :=
  derive_preserves (show derive [right, left, seed, otherSeed] [rootRule] =
    some [root, right, left, seed, otherSeed] by decide) left (by decide)

theorem independently_combined_requirements :
    check ([left] ++ [root]) [seed, otherSeed] rules = true :=
  (check_requirements_append _ _ _ _).mpr ⟨by decide, shared_premise⟩

/-- Claim meaning can depend on arbitrary facts about the fixed actual execution.
These two propositions need not have decidable truth. -/
def holds (first second : Prop) : Nat → Prop
  | 0 => first
  | 1 => second
  | _ => first ∧ second

def conjunctionRule : Rule Nat := ⟨[0, 1], 2⟩

theorem conjunction_rule_sound (first second : Prop) :
    conjunctionRule.Sound (holds first second) False := by
  intro premises
  exact Or.inl ⟨premises 0 (by decide), premises 1 (by decide)⟩

/-- A concrete multi-premise instance uses both the semantic rule law and the
sound terminal seeds. Structural checking contributes the required-root link. -/
theorem interpreted_roots (first second : Prop) (hfirst : first) (hsecond : second) :
    ∀ claim ∈ [2, 0], holds first second claim := by
  apply check_sound_of_not_bad (holds first second) (fun _ => False)
    (terminals := [0, 1]) (rules := [conjunctionRule])
  · intro claim member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact hfirst
    · exact hsecond
  · intro rule member
    have same : rule = conjunctionRule := List.mem_singleton.mp member
    subst rule
    exact conjunction_rule_sound first second
  · exact fun _ _ event => event
  · decide

/-- The existing reduction contract can consume the checked finite derivation. -/
theorem conjunction_contract (first second : Prop) :
    PIR.Relation.ReductionContract
      (fun required => ∀ claim ∈ required, holds first second claim)
      (fun facts => ∀ claim ∈ facts, holds first second claim)
      [2] [0, 1] (∃ rule ∈ [conjunctionRule], (fun _ => False) rule) := by
  apply check_reduction (holds first second) (fun _ => False)
  · intro rule member
    have same : rule = conjunctionRule := List.mem_singleton.mp member
    subst rule
    exact conjunction_rule_sound first second
  · decide

def forgedRule : Rule Nat := ⟨[], 0⟩

/-- An empty-premise rule passes availability checking, but cannot manufacture
a false proposition: it fails the separately required rule interpretation. -/
theorem structural_acceptance_is_not_rule_validity :
    check [0] [] [forgedRule] = true ∧
      ¬ forgedRule.Sound (fun _ => False) False := by
  constructor
  · decide
  · intro sound
    exact (sound (by simp [forgedRule])).elim id id

/-- Likewise, the seed list alone is not evidence of a successful terminal. -/
theorem structural_acceptance_is_not_terminal_truth :
    check [0] [0] ([] : List (Rule Nat)) = true ∧
      ¬ (∀ claim ∈ ([0] : List Nat), (fun _ => False) claim) := by
  constructor
  · decide
  · intro sound
    exact sound 0 (by decide)

/-- Admitting an explicit bad event allows the disjunction, not the false root. -/
theorem admitted_bad_event :
    (∀ claim ∈ ([0] : List Nat), (fun _ => False) claim) ∨
      ∃ rule ∈ [forgedRule], (fun _ => True) rule := by
  apply check_sound (fun _ => False) (fun _ => True) (terminals := [])
  · simp
  · exact fun _ _ _ => Or.inr trivial
  · decide

theorem admitted_bad_event_does_not_establish_root :
    ¬ (∀ claim ∈ ([0] : List Nat), (fun _ => False) claim) := by
  intro sound
  exact sound 0 (by decide)

end Tests.Obligations
