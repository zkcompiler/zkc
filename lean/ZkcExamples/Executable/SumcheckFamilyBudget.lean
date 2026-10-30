module

public import Zkc.Construction.OriginProjection
public import Zkc.Executable.HelperCosts
public import Zkc.Executable.DomainFitsRules
public import Zkc.Executable.DomainSuccess
public import ZkcExamples.Executable.SumcheckShape
public meta import Mathlib.Tactic.Ring
public meta import ZkcTools.ConstructionBindings.ArtifactBindingTactic

@[expose] public section

/-! Resource contracts for arbitrary programs of the Sumcheck shape. The
family has no dependency on an installed Entry or its helper implementation. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckFamily
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open SumcheckShape
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! A parameterized replacement for the retired Artifact interface. The local
round certificate is about actual Code/Domain continuations; it is independent
of oracle answers, honesty and whole-program execution equations. -/
namespace ProgramShape

structure Description where
  program : Structured.Program
  context : Context
  names : Names
  maximum : Nat
  small : maximum < 64
  suite : context.suite = names.suite

def inputs (shape : Description) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  [.data (.vector shape.names.scalar values), .data (.field shape.names.scalar claim),
    .data (.index rounds), .transcript shape.names.suite history]

def carried (shape : Description) (point : List F) (claim : F)
    (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim),
    .transcript shape.names.suite history]

def Invariant (shape : Description) (count : Nat) (env : DomainVM.Environment F G) (_ : Proof F G) : Prop :=
  ∃ point claim history, env = carried shape point claim history ∧ point.length = count

/-- Obligations at the actual program/helper boundary, replacing the former
Artifact's independent interpreter contracts. No whole-run equality is a field. -/
structure Contract (shape : Description) (cost : String → List (Value F G) → Nat) (roundCost : Nat) : Prop where
  pending : ∀ (claim : F), Domain.callHelper (Structured.ringModel F G) shape.program shape.names.pendingHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)] [.data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar []), .data (.field shape.names.scalar claim)]
  openClaim : ∀ (point : List F) (claim : F), Domain.callHelper (Structured.ringModel F G) shape.program shape.names.openClaimHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)]
    [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)]
  atPrefix : ∀ (point : List F) (claim : F), Domain.callHelper (Structured.ringModel F G) shape.program shape.names.atPrefixHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)]
    [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)]
  pendingCost : ∀ (claim : F), cost shape.names.pendingHelper [.data (.field shape.names.scalar claim)] ≤ 2
  openClaimCost : ∀ (point : List F) (claim : F),
    cost shape.names.openClaimHelper [.vector shape.names.scalar point, .data (.field shape.names.scalar claim)] ≤ 1
  atPrefixCost : ∀ (point : List F) (claim : F),
    cost shape.names.atPrefixHelper [.vector shape.names.scalar point, .data (.field shape.names.scalar claim)] ≤ 1
  checkCost : ∀ (values point : List F) (claim : F), point.length < 64 → values.length = 2 ^ point.length →
    cost shape.names.checkHelper [.vector shape.names.scalar values, .vector shape.names.scalar point,
      .data (.field shape.names.scalar claim)] = 62 + 20 * point.length
  round : ∀ (values : List F) (publicClaim : F) (rounds : Nat)
    (initial : Domain.History (Structured.uniformCarriers F G)) (index : Nat) (point : List F) (claim : F)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G) (used budget : Nat),
    used + roundCost ≤ budget →
    DomainVM.FitsK shape.program shape.context cost budget (roundCode shape.names)
      (inputs shape values publicClaim rounds initial ++
        [.data (.vector shape.names.scalar []), .data (.field shape.names.scalar publicClaim),
          .data (.vector shape.names.scalar []), .data (.field shape.names.scalar publicClaim)] ++
          .data (.index index) :: carried shape point claim history) proof used
      (fun final unread charged => charged ≤ used + roundCost ∧ ∀ values,
        Domain.read final yielded = some values → Domain.sortsMatch (carriedSorts shape.names) values = true →
          Invariant shape (point.length + 1) values unread)

def reading (shape : Description) : Lowered :=
  ⟨code shape.names shape.maximum, [13,10], []⟩

/-- Arbitrary programs, contexts, nominal names, helper implementations and
static maxima satisfying the local actual-program contract share this bound.
The receive plan is irrelevant to typed Code sufficiency. -/
theorem sufficient (shape : Description) (price : String → List (Value F G) → Nat)
    (roundCost : Nat) (contract : Contract shape price roundCost) (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : 72 + (roundCost + 21) * rounds ≤ budget) :
    DomainVM.Sufficient shape.program shape.context price budget (reading shape)
      (inputs shape values claim rounds history) proof := by
  have costIdentity : (roundCost + 21) * rounds = rounds * (roundCost + 1) + 20 * rounds := by ring
  rw [costIdentity] at fits
  have pendingPrice := contract.pendingCost claim
  have openPrice := contract.openClaimCost [] claim
  unfold DomainVM.Sufficient reading code pendingCall openClaimCall
  apply DomainVM.FitsK.helper _ _ _ _ shape.names.pendingHelper [1]
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)] _ _ proof 0 _
    [.data (.field shape.names.scalar claim)] [.data (.field shape.names.scalar claim)] rfl rfl
  · omega
  · normalize_artifact_operations [contract.pending] unfolding [inputs, carried, Domain.step, DomainVM.Continues]
    apply DomainVM.FitsK.helper _ _ _ _ shape.names.openClaimHelper [4,5]
      [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)] _ _ proof _ _
      [.data (.vector shape.names.scalar []), .data (.field shape.names.scalar claim)]
      [.vector shape.names.scalar [], .data (.field shape.names.scalar claim)] rfl rfl
    · omega
    · normalize_artifact_operations [contract.openClaim] unfolding [inputs, carried, Domain.step, DomainVM.Continues]
      apply DomainVM.FitsK.loop_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        (Invariant shape) roundCost ⟨[], claim, history, rfl, rfl⟩
      · intro index carried unread charged valid within
        obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
        apply DomainVM.FitsK.mono _ _ _ _ _ _ _ _ _ _ ?_
          (contract.round values claim rounds history index point scalar suffix unread charged budget (by omega))
        intro final unread charged found
        refine ⟨found.1, ?_⟩
        intro result readEq sorted
        simpa only [length] using found.2 result readEq sorted
      · intro admitted
        omega
      · intro admitted carried unread charged valid smaller sorted
        obtain ⟨point, scalar, suffix, rfl, length⟩ := valid
        have pointSmall : point.length < 64 := by have := shape.small; omega
        have checkPrice := contract.checkCost values point scalar pointSmall (by rw [length]; exact shaped)
        have prefixPrice := contract.atPrefixCost point scalar
        apply DomainVM.FitsK.helper _ _ _ _ shape.names.atPrefixHelper [8,9]
          [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)] _ _ unread charged _
          [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar scalar)]
          [.vector shape.names.scalar point, .data (.field shape.names.scalar scalar)] rfl rfl
        · omega
        · normalize_artifact_operations [contract.atPrefix] unfolding [inputs, carried, Domain.step, DomainVM.Continues]
          apply DomainVM.FitsK.helper _ _ _ _ shape.names.checkHelper [0,11,12] [.data .boolean] [] _ unread _ _
            [.data (.vector shape.names.scalar values), .data (.vector shape.names.scalar point),
              .data (.field shape.names.scalar scalar)]
            [.vector shape.names.scalar values, .vector shape.names.scalar point,
              .data (.field shape.names.scalar scalar)] rfl rfl
          · rw [checkPrice, length]; omega
          · apply DomainVM.Continues.of_forall
            intro final unread
            simp only [DomainVM.FitsK]
            rw [checkPrice, length]; omega

/-- Honest completeness interface for an arbitrary actual program of the
shape. Mathematical success is an independent canonical Process obligation;
resource bounds alone cannot establish this hypothesis. -/
theorem honest_success (shape : Description) (price : String → List (Value F G) → Nat)
    (roundCost : Nat) (contract : Contract shape price roundCost) (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : 72 + (roundCost + 21) * rounds ≤ budget)
    (initial : History F G) (oracle : History F G → F)
    (holds : DomainVM.Environment F G → Proof F G → Prop)
    (passes : DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation shape.program shape.context (Code.instructions (reading shape).code)
        (reading shape).returned (inputs shape values claim rounds history)) proof holds) :
    ∃ returned unread, holds returned unread ∧
      DomainVM.metered (m := Id) shape.program shape.context Origin.withoutCoordinates initial oracle
        price budget (reading shape) (inputs shape values claim rounds history) proof = (.returned returned, unread) :=
  DomainVM.metered_success shape.program shape.context Origin.withoutCoordinates initial oracle price budget
    (reading shape) (inputs shape values claim rounds history) proof holds
    (sufficient shape price roundCost contract budget values claim rounds history proof shaped fits) passes

end ProgramShape

end ZkcExamples.Executable.SumcheckFamily
