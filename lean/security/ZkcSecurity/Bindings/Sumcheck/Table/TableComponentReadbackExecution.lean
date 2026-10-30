module

public import ZkcSecurity.Bindings.Transcript.HonestReadbackLoops
public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentReadbackLoop

@[expose] public section

/-! Adapt a checked pair of source loop bodies to the honest component law.
The full producer and validator returns, including their shared history, reach
both continuations. The rule does not identify or erase an arbitrary frame. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.FiatShamir

variable {F G A B : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem sourceLoopBind (plan : Plan) (field : String) (fieldEq : plan.field = field)
    (program : Structured.Program)
    (helpers : HelperLaws (F := F) (G := G) program plan)
    (context : Context) (sites : ∀ index, Sites plan context index)
    (leftBody rightBody : Domain.View.Block (ringModel F G).toCarriers)
    (leftOffset rightOffset : Nat)
    (leftEq : leftBody = producerBlock plan program context leftOffset)
    (rightEq : rightBody = CompiledRound.block plan.toPlan program context field rightOffset)
    (leftCaptured rightCaptured : Domain.Environment (ringModel F G).toCarriers)
    (leftSize : leftCaptured.length = leftOffset) (rightSize : rightCaptured.length = rightOffset)
    (raw : List F) (count : Nat) (small : count < 64)
    (shape : raw.length = 2 ^ count) (bounded : raw.length < indexLimit)
    (history : Domain.History (ringModel F G).toCarriers)
    (Post : A → B → Prop)
    (nextLeft : Domain.Environment (ringModel F G).toCarriers → PIR.Process (Domain.effects (ringModel F G).toCarriers) A)
    (nextRight : Domain.Environment (ringModel F G).toCarriers → PIR.Process (Domain.effects (ringModel F G).toCarriers) B)
    (next : ∀ state : LoopState F G 0, state.original = raw → state.scalar = state.entries.sum →
      Readback Post (nextLeft (producerCarried field context.suite state))
        (nextRight (validatorCarried field context.suite state))) :
    Readback Post
      ((Domain.iterate leftBody leftCaptured
        [leftOffset + 21, leftOffset + 22, leftOffset + 23, leftOffset + 24, leftOffset + 20]
        [.data (.vector field), .data .index, .data .index,
          .data (.vector field), .transcript context.suite] (List.range count)
        [.data (.vector field raw), .data (.index count), .data (.index 1),
          .data (.vector field []), .transcript context.suite history]).bind nextLeft)
      ((Domain.iterate rightBody rightCaptured [rightOffset + 21, rightOffset + 26, rightOffset + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        (List.range count) [.data (.vector field []), .data (.field field raw.sum),
          .transcript context.suite history]).bind nextRight) := by
  subst field
  rw [leftEq, rightEq, ← leftSize, ← rightSize]
  apply (initial_loop_readback plan program helpers context sites leftCaptured rightCaptured
    raw count small shape bounded history).bind
  intro left right post
  obtain ⟨state, original, _, honest, rfl, rfl⟩ := post
  exact next state original honest

end ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
