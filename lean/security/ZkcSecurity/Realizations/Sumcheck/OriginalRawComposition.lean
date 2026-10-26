module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawSoundness

@[expose] public section

/-! Source-order conjunction of two raw calls. Each terminal runs before the
next call, and every stop suppresses its suffix. The second call starts with
the actual first call's reached construction state. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck TableComponent
open Std.WP ZkcSecurity.Obligations.WeakestPrecondition

variable {F G : Type} [Field F] [DecidableEq F]

def both {I : PIR.Signature} (left right : Values (Component (assignment F G)) [.boolean]) :
    PIR.Process I (Values (Component (assignment F G)) [.boolean]) :=
  .done (.cons ((left.get .here).bind fun a => (right.get .here).map fun b => a && b) .nil)

noncomputable def sourceTwoRoots (maximum : Nat)
    (leftContext rightContext : Realizations.Sumcheck.Original.Context)
    (left right : List F) (leftClaim rightClaim : F) (count : Nat) :=
  (sourceRoot (G := G) maximum leftContext left leftClaim count).bind fun first =>
  (sourceRoot (G := G) maximum rightContext right rightClaim count).bind fun second =>
    both first second

noncomputable def twoRoots (maximum : Nat)
    (leftSchedule rightSchedule : Nominal.Schedule "bls12-381.fr")
    (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) :=
  (root maximum leftSchedule left leftClaim count construction).bind fun first =>
  (root maximum rightSchedule right rightClaim count first.2).bind fun second =>
    (both first.1 second.1).bind fun result => .done (result, second.2)

omit [Field F] [DecidableEq F] in
theorem both_bridge (routing : Zkc.Construction.Original.Routing)
    (left right : Values (Component (assignment F G)) [.boolean])
    (construction : ConstructionState (F := F) (G := G)) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr")
      (fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history (Zkc.Construction.Original.fold routing (both left right) construction)
      ((both left right).bind fun result => .done (result, construction)) := by
  unfold both
  exact .done _ _ ⟨rfl, rfl⟩

theorem twoRoots_bridge (routing : Zkc.Construction.Original.Routing)
    (leftContext rightContext : Realizations.Sumcheck.Original.Context)
    (leftSchedule rightSchedule : Nominal.Schedule "bls12-381.fr") (maximum : Nat)
    (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G))
    (leftRoutes : OriginalSecurity.Routes routing leftContext leftSchedule construction.frames)
    (rightRoutes : OriginalSecurity.Routes routing rightContext rightSchedule construction.frames) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr")
      (fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing
        (sourceTwoRoots maximum leftContext rightContext left right leftClaim rightClaim count) construction)
      (twoRoots maximum leftSchedule rightSchedule left right leftClaim rightClaim count construction) := by
  rw [sourceTwoRoots, Zkc.Construction.Original.fold_bind]
  apply (root_bridge routing leftContext leftSchedule maximum left leftClaim count construction leftRoutes).bind
  intro reached first firstPreserved
  change DomainReduction.Bridge _ _ reached
    (Zkc.Construction.Original.fold routing
      ((sourceRoot maximum rightContext right rightClaim count).bind fun second => both first.1 second) first.2) _
  rw [Zkc.Construction.Original.fold_bind]
  have nextRoutes : OriginalSecurity.Routes routing rightContext rightSchedule first.2.frames :=
    firstPreserved.2 ▸ rightRoutes
  have tail := (root_bridge routing rightContext rightSchedule maximum right rightClaim count first.2 nextRoutes).bind
    (fun second => Zkc.Construction.Original.fold routing (both first.1 second.1) second.2)
    (fun second => (both first.1 second.1).bind fun result => .done (result, second.2))
    (PostNext := fun reached (result : Result (F := F) (G := G)) =>
      result.2.history = reached ∧ result.2.frames = construction.frames) (by
      intro reached second secondPreserved
      have last := both_bridge routing first.1 second.1 second.2
      rw [secondPreserved.1] at last
      exact last.weaken fun reached result holds =>
        ⟨holds.1, holds.2.trans (secondPreserved.2.trans firstPreserved.2)⟩)
  rw [firstPreserved.1] at tail
  exact tail

variable {charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal}
variable [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)]

def both_rejected (left right : Result (F := F) (G := G))
    (history : Domain.History (uniformCarriers F G))
    (wrong : acceptance left ≠ some true ∨ acceptance right ≠ some true) :
    Derivation (Nominal.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      ((both left.1 right.1).bind fun result => .done (result, right.2)) := by
  have leftEq : left.1.get .here = acceptance left := by
    unfold acceptance OriginalSecurity.acceptance
    cases left.1 with | cons value rest => cases rest; rfl
  have rightEq : right.1.get .here = acceptance right := by
    unfold acceptance OriginalSecurity.acceptance
    cases right.1 with | cons value rest => cases rest; rfl
  apply Derivation.done
  change ((left.1.get .here).bind fun a => (right.1.get .here).map fun b => a && b) ≠ some true
  rw [leftEq, rightEq]
  cases leftValue : acceptance left with
  | none => simp
  | some a =>
    cases rightValue : acceptance right with
    | none => simp
    | some b => cases a <;> cases b <;> simp_all

def Correct (raw : List F) (claim : F) (count : Nat) : Prop :=
  raw.length < indexLimit ∧ raw.length = 2 ^ count ∧ claim = raw.sum

noncomputable def twoRoots_rejected
    (sampling : (Nominal.queriesWithFrame (G := G) "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).ConditionalBound
      (Nominal.layoutWithFrame "bls12-381.fr"
        (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).representation 1 1 charge)
    (maximum : Nat) (leftSchedule rightSchedule : Nominal.Schedule "bls12-381.fr")
    (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G))
    (wrong : ¬ (Correct left leftClaim count ∧ Correct right rightClaim count)) :
    Derivation (Nominal.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      (twoRoots maximum leftSchedule rightSchedule left right leftClaim rightClaim count construction) := by
  unfold twoRoots
  by_cases firstCorrect : Correct left leftClaim count
  · have secondWrong : right.length < indexLimit → right.length = 2 ^ count → rightClaim ≠ right.sum := by
      intro bounded shape equal
      exact wrong ⟨firstCorrect, bounded, shape, equal⟩
    apply (unrestricted (root maximum leftSchedule left leftClaim count construction) history).bind
    intro reached first _
    apply (root_rejected sampling maximum rightSchedule right rightClaim count first.2 reached secondWrong).bind
    intro reached second rejected
    exact both_rejected first second reached (Or.inr rejected)
  · have firstWrong : left.length < indexLimit → left.length = 2 ^ count → leftClaim ≠ left.sum := by
      intro bounded shape equal
      exact firstCorrect ⟨bounded, shape, equal⟩
    apply (root_rejected sampling maximum leftSchedule left leftClaim count construction history firstWrong).bind
    intro reached first rejected
    apply (unrestricted (root maximum rightSchedule right rightClaim count first.2) reached).bind
    intro reached second _
    exact both_rejected first second reached (Or.inl rejected)

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
set_option experimental.vcgen true in
theorem twoRoots_cost (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (maximum : Nat) (leftSchedule rightSchedule : Nominal.Schedule "bls12-381.fr")
    (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) "bls12-381.fr") charge
      (twoRoots maximum leftSchedule rightSchedule left right leftClaim rightClaim count construction)
      history ((maximum + maximum) • price) := by
  let absorb := Nominal.interface (F := F) (G := G) "bls12-381.fr"
  let := costMonad absorb charge
  apply cost_of_triple absorb charge
    (pre := fun _ credit => (maximum + maximum) • price ≤ credit) ?_ history _ le_rfl
  have first := bound_spec absorb charge
    (root maximum leftSchedule left leftClaim count construction) (maximum • price) (maximum • price)
    (root_cost price priced maximum leftSchedule left leftClaim count construction)
  have second (state : ConstructionState (F := F) (G := G)) := bound_spec absorb charge
    (root maximum rightSchedule right rightClaim count state) (maximum • price) 0
    (root_cost price priced maximum rightSchedule right rightClaim count state)
  unfold twoRoots
  vcgen [first, second, both]
  all_goals simp_all only [add_nsmul, add_zero]

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
