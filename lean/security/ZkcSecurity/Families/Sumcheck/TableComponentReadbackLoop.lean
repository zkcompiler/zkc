module

public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackRound
public import ZkcSecurity.Families.Sumcheck.TableComponentPrefix
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! The actual two loop bodies share one dimension-indexed table invariant.
The original table, challenge prefix, complete history, and both carried values
remain explicit. Zero and arbitrary partial index lists use the same induction. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.FiatShamir
open Zkc.Polynomial.Multilinear

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure Sites (plan : Plan) (context : Context) (index : Nat) where
  low : Origin
  high : Origin
  query : Origin
  delivery : Origin
  lowFound : Domain.templateOrigin context plan.lowTemplate [index] = some low
  highFound : Domain.templateOrigin context plan.highTemplate [index] = some high
  queryFound : Domain.queryOrigin context context.suite plan.field plan.queryTemplate [index] = some query
  deliveryFound : Domain.templateOrigin context plan.deliveryTemplate [index] = some delivery
  lowMessage : low.request = none
  highMessage : high.request = none
  deliveryMessage : delivery.request = none
  request : query.request = some (.draw plan.field)

abbrev LoopState (F G : Type) [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] :=
  PrefixState F (Domain.History (ringModel F G).toCarriers)

def producerCarried (field suite : String) {n : Nat} (state : LoopState F G n) :
    Domain.Environment (ringModel F G).toCarriers :=
  [.data (.vector field state.entries), .data (.index n), .data (.index 1),
    .data (.vector field state.point),
    .transcript suite state.frame]

def validatorCarried (field suite : String) {n : Nat} (state : LoopState F G n) :
    Domain.Environment (ringModel F G).toCarriers :=
  [.data (.vector field state.point), .data (.field field state.scalar),
    .transcript suite state.frame]

def loopInvariant (field suite : String) (original : List F) (count : Nat) (indices : List Nat)
    (left right : Domain.Environment (ringModel F G).toCarriers) : Prop :=
  ∃ state : LoopState F G indices.length,
    state.original = original ∧ indices.length ≤ count ∧
      state.scalar = state.entries.sum ∧ left = producerCarried field suite state ∧ right = validatorCarried field suite state

set_option linter.unusedSimpArgs false in
theorem loop_readback (plan : Plan) (program : Structured.Program)
    (helpers : HelperLaws (F := F) (G := G) program plan)
    (context : Context) (sites : ∀ index, Sites plan context index)
    (leftCaptured rightCaptured : Domain.Environment (ringModel F G).toCarriers)
    (original : List F) (count : Nat) (countSmall : count < 64)
    (shape : original.length = 2 ^ count) (bounded : original.length < indexLimit)
    (indices : List Nat) (left right : Domain.Environment (ringModel F G).toCarriers)
    (holds : loopInvariant plan.field context.suite original count indices left right) :
    Readback (loopInvariant plan.field context.suite original count [])
      (Domain.iterate
        (producerBlock plan program context leftCaptured.length)
        leftCaptured [leftCaptured.length + 21, leftCaptured.length + 22, leftCaptured.length + 23,
          leftCaptured.length + 24, leftCaptured.length + 20]
        [.data (.vector plan.field), .data .index, .data .index,
          .data (.vector plan.field), .transcript context.suite] indices left)
      (Domain.iterate
        (CompiledRound.block plan.toPlan program context plan.field rightCaptured.length)
        rightCaptured [rightCaptured.length + 21, rightCaptured.length + 26, rightCaptured.length + 20]
        [.data (.vector plan.field), .data (.field plan.field),
          .transcript context.suite] indices right) := by
  apply Readback.iterate _ _ _ _ _ _ _ _ (loopInvariant plan.field context.suite original count) _ indices left right holds
  intro index rest left right invariant
  obtain ⟨state, sameOriginal, remainingBound, honest, rfl, rfl⟩ := invariant
  have dimensionSmall : (index :: rest).length < 64 := lt_of_le_of_lt remainingBound countSmall
  have entriesBound : state.entries.length < indexLimit := by
    rw [state.entries_shape]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) remainingBound) (shape ▸ bounded)
  have positive : 0 < (index :: rest).length := by simp
  have splitShape : state.entries.length % 2 = 0 := by
    rw [state.entries_shape, List.length_cons, Nat.pow_succ]
    omega
  let site := sites index
  have round := readback plan program helpers context index site.low site.high site.query site.delivery
    site.lowFound site.highFound site.queryFound site.deliveryFound site.lowMessage site.highMessage
    site.deliveryMessage site.request leftCaptured rightCaptured state.entries state.point
    (index :: rest).length state.entries_shape entriesBound dimensionSmall positive state.frame
  rw [← honest] at round
  apply round.mono
  intro leftFinal rightFinal returned
  obtain ⟨challenge, leftRead, rightRead⟩ := returned
  let endpoints : F × F := ((state.entries.take (state.entries.length / 2)).sum,
    (state.entries.drop (state.entries.length / 2)).sum)
  let next : LoopState F G rest.length :=
    { state.advance endpoints challenge with
      frame := TableComponent.Execution.finalHistory plan.field site.low site.high site.query site.delivery
        state.frame endpoints.1 endpoints.2 challenge }
  have nextEntries : next.entries = restrictValues state.entries challenge := state.advance_entries endpoints challenge
  have nextHonest : next.scalar = next.entries.sum := by
    rw [nextEntries, Zkc.Protocols.Sumcheck.Multilinear.restrictValues_sum _ _ splitShape]
    rfl
  refine ⟨producerCarried plan.field context.suite next, validatorCarried plan.field context.suite next, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [producerCarried]
    rw [nextEntries]
    exact leftRead
  · exact rightRead
  · simp [Domain.sortsMatch, producerCarried, Domain.Value.sort, Domain.Payload.ty]
  · simp [Domain.sortsMatch, validatorCarried, Domain.Value.sort, Domain.Payload.ty]
  · exact ⟨next, sameOriginal, by simpa using Nat.le_trans (Nat.le_succ rest.length) remainingBound,
      nextHonest, rfl, rfl⟩

/-- Start the installed loop from the source table and its honest sum. This
shared introduction retains the exact whole carried ABI, including empty
prefix and arbitrary initial history, also when the round count is zero. -/
theorem initial_loop_readback (plan : Plan) (program : Structured.Program)
    (helpers : HelperLaws (F := F) (G := G) program plan)
    (context : Context) (sites : ∀ index, Sites plan context index)
    (leftCaptured rightCaptured : Domain.Environment (ringModel F G).toCarriers)
    (original : List F) (count : Nat) (countSmall : count < 64)
    (shape : original.length = 2 ^ count) (bounded : original.length < indexLimit)
    (history : Domain.History (ringModel F G).toCarriers) :
    Readback (loopInvariant plan.field context.suite original count [])
      (Domain.iterate (producerBlock plan program context leftCaptured.length)
        leftCaptured [leftCaptured.length + 21, leftCaptured.length + 22, leftCaptured.length + 23,
          leftCaptured.length + 24, leftCaptured.length + 20]
        [.data (.vector plan.field), .data .index, .data .index,
          .data (.vector plan.field), .transcript context.suite] (List.range count)
        [.data (.vector plan.field original), .data (.index count), .data (.index 1),
          .data (.vector plan.field []), .transcript context.suite history])
      (Domain.iterate (CompiledRound.block plan.toPlan program context plan.field rightCaptured.length)
        rightCaptured [rightCaptured.length + 21, rightCaptured.length + 26, rightCaptured.length + 20]
        [.data (.vector plan.field), .data (.field plan.field), .transcript context.suite]
        (List.range count) [.data (.vector plan.field []), .data (.field plan.field original.sum),
          .transcript context.suite history]) := by
  let initial : LoopState F G (List.range count).length :=
    PrefixState.initial original (List.range count).length original.sum history (by simpa using shape)
  have run := loop_readback plan program helpers context sites leftCaptured rightCaptured
    original count countSmall shape bounded (List.range count)
    (producerCarried plan.field context.suite initial) (validatorCarried plan.field context.suite initial)
    (by refine ⟨initial, rfl, ?_, rfl, rfl, rfl⟩; simp only [List.length_range, Nat.le_refl])
  simpa only [producerCarried, validatorCarried, initial, PrefixState.initial,
    PrefixState.entries, restrictPrefixValues_nil, List.length_range] using run

end ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
