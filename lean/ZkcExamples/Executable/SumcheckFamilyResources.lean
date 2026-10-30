module

public import ZkcExamples.Executable.SumcheckFamilySource
public meta import ZkcTools.ConstructionBindings.ArtifactBindingTactic

@[expose] public section

/-! Resource certificates generated from the same local occurrence and helper
laws as the mathematical proof. Arbitrary proof heads, false claims, stopped
queries, and every typed challenge reply retain their stopping behavior. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckFamily.Source
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform
open Zkc.Construction.ArtifactBinding
open SumcheckShape

def roundPrefix (shape : Shape) : List Code := (roundCode shape.names).take 27
def roundSuffix (shape : Shape) : List Code := (roundCode shape.names).drop 28

theorem round_split (shape : Shape) : roundCode shape.names = roundPrefix shape ++
    [.helper ⟨.call shape.names.appendHelper, [9,24], [.data (.vector shape.names.scalar)], []⟩] ++
      roundSuffix shape := rfl

theorem roundPrefix_static (shape : Shape) : Code.static (roundPrefix shape) = some 28 := rfl
theorem roundSuffix_static (shape : Shape) : Code.static (roundSuffix shape) = some 7 := rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Only local helper prices are admitted. The round certificate and total
budget are generated below, rather than supplied by a realization. -/
structure Prices (shape : Shape) (price : String → List (Value F G) → Nat) (appendBound : Nat) : Prop where
  pending : ∀ (claim : F), price shape.names.pendingHelper [.data (.field shape.names.scalar claim)] ≤ 2
  openClaim : ∀ (point : List F) (claim : F),
    price shape.names.openClaimHelper [.vector shape.names.scalar point, .data (.field shape.names.scalar claim)] ≤ 1
  atPrefix : ∀ (point : List F) (claim : F),
    price shape.names.atPrefixHelper [.vector shape.names.scalar point, .data (.field shape.names.scalar claim)] ≤ 1
  append : ∀ (point : List F) (answer : F),
    price shape.names.appendHelper [.vector shape.names.scalar point, .data (.field shape.names.scalar answer)] ≤ appendBound
  check : ∀ (values point : List F) (claim : F), point.length < 64 → values.length = 2 ^ point.length →
    price shape.names.checkHelper [.vector shape.names.scalar values, .vector shape.names.scalar point,
      .data (.field shape.names.scalar claim)] = 62 + 20 * point.length

/-- The fixed nonhelper round charge is 36. The only variable local price is
point extension; all result declarations and continuation branches are checked. -/
theorem round_fits (shape : Shape) (occurrences : Occurrences shape) (helpers : Helpers (F := F) (G := G) shape)
    (price : String → List (Value F G) → Nat) (appendBound : Nat) (prices : Prices shape price appendBound)
    (a b c d e f g h : Domain.Value (Structured.uniformCarriers F G))
    (index : Nat) (point : List F) (scalar : F) (history : Domain.History (Structured.uniformCarriers F G))
    (proof : Proof F G) (used budget : Nat) (within : used + (36 + appendBound) ≤ budget) :
    DomainVM.FitsK shape.program shape.context price budget (roundCode shape.names)
      ([a,b,c,d,e,f,g,h] ++ .data (.index index) :: ProgramShape.carried shape point scalar history) proof used
      (fun final unread charged => charged ≤ used + (36 + appendBound) ∧ ∀ values,
        Domain.read final yielded = some values →
          Domain.sortsMatch (carriedSorts shape.names) values = true →
            ProgramShape.Invariant shape (point.length + 1) values unread) := by
  rw [round_split, DomainVM.FitsK.append]
  apply DomainVM.FitsK.of_static shape.program shape.context price budget (roundPrefix shape) (roundPrefix_static shape)
    _ _ used _ (by omega)
  have lowResolved := occurrences.first index
  have highResolved := occurrences.second index
  have drawResolved := occurrences.draw index
  have deliveryResolved := occurrences.delivery index
  have firstRequest : (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index]).request = none := occurrences.firstRequest
  have secondRequest : (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index]).request = none := occurrences.secondRequest
  have deliveryRequest : (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index]).request = none := occurrences.deliveryRequest
  apply DomainVM.Continues.of_yields_all_proofs
  normalize_artifact_operations [Domain.Calculations.fieldAdd (F := F) (G := G),
      Domain.Calculations.fieldEqual (F := F) (G := G), lowResolved, highResolved, drawResolved, deliveryResolved,
      firstRequest, secondRequest, deliveryRequest, occurrences.firstSchema, occurrences.secondSchema, shape.suite]
    unfolding [roundPrefix, List.take, Code.instructions, roundCode, roundBody, ProgramShape.carried,
      Domain.evaluate, Domain.step, PIR.Yields, Structured.Ty.isHandle, Bool.not_false, Bool.not_true, drawOrigin]
  intros ignored low ignored1 ignored2 ignored3 ignored4 ignored5 ignored6 ignored7 ignored8 ignored9 high
    ignored10 ignored11 ignored12 ignored13 ignored14 ignored15 ignored16 ignored17 ignored18 ignored19 ignored20 ignored21 ignored22
  by_cases valid : scalar = low + high
  all_goals simp only [valid, decide_true, decide_false]
  all_goals normalize_artifact_operations [lowResolved, highResolved, drawResolved, deliveryResolved,
      firstRequest, secondRequest, deliveryRequest, shape.suite]
    unfolding [Domain.evaluate, Domain.step, PIR.Yields, Structured.Ty.isHandle, Bool.not_false, Bool.not_true, drawOrigin]
  intro ignored24 ignored25 ignored26 ignored27 ignored28 ignored29 answer
  change F at answer
  intros
  have priceBound := prices.append point answer
  simp only [DomainVM.FitsStep]
  normalize_artifact_operations [] unfolding [DomainVM.arguments, Uniform.DomainAdapter.readbackData,
    Uniform.DomainAdapter.readbackPayload]
  simp only [Eq.mp]
  refine ⟨by omega, _, rfl, ?_, ?_⟩
  · omega
  · apply DomainVM.Continues.of_yields_all_proofs
    normalize_artifact_operations [helpers.append] unfolding [Domain.step, PIR.Yields]
    intros
    simp only [DomainVM.FitsK]
    apply DomainVM.FitsK.of_static shape.program shape.context price budget (roundSuffix shape) (roundSuffix_static shape)
    · omega
    · apply DomainVM.Continues.of_yields_all_proofs
      normalize_artifact_operations [Domain.Calculations.fieldConstant (F := F) (G := G),
        Domain.Calculations.fieldSubtract (F := F) (G := G),
        Domain.Calculations.fieldMultiply (F := F) (G := G),
        Domain.Calculations.fieldAdd (F := F) (G := G)] unfolding [roundSuffix, List.drop, Code.instructions, roundCode, roundBody,
        Domain.evaluate, Domain.step, PIR.Yields]
      intros
      refine ⟨by omega, ?_⟩
      intro values readEq sorted
      simp only [Option.some.injEq] at readEq
      subst values
      exact ⟨point ++ [answer], _, _, rfl, by simp⟩

/-- Generate the established budget interface from bounded local laws. -/
theorem budgetContract (shape : Shape) (occurrences : Occurrences shape) (helpers : Helpers (F := F) (G := G) shape)
    (price : String → List (Value F G) → Nat) (appendBound : Nat) (prices : Prices shape price appendBound) :
    ProgramShape.Contract shape price (36 + appendBound) where
  pending := helpers.pending
  openClaim := helpers.openClaim
  atPrefix := helpers.atPrefix
  pendingCost := prices.pending
  openClaimCost := prices.openClaim
  atPrefixCost := prices.atPrefix
  checkCost := prices.check
  round := fun values publicClaim rounds initial =>
    round_fits shape occurrences helpers price appendBound prices
      (.data (.vector shape.names.scalar values)) (.data (.field shape.names.scalar publicClaim))
      (.data (.index rounds)) (.transcript shape.names.suite initial)
      (.data (.vector shape.names.scalar [])) (.data (.field shape.names.scalar publicClaim))
      (.data (.vector shape.names.scalar [])) (.data (.field shape.names.scalar publicClaim))

end ZkcExamples.Executable.SumcheckFamily.Source
