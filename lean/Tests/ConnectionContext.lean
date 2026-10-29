import Zkc.Construction.ConnectionContext
import Zkc.Construction.ConnectionMasking
import ZkcTools.ConstructionBindings.Readback

set_option autoImplicit false
namespace Tests.ConnectionContext
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionFrame

def stack : ScopedFrames [.value .index, .value .index] :=
  [⟨"outer", .var (.there .here)⟩, ⟨"inner", .var .here⟩]

example (model : DomainModel) (outer inner : Nat) :
    stack.eval model (.cons inner (.cons outer .nil)) =
      [⟨"outer", outer⟩, ⟨"inner", inner⟩] := rfl

-- Equal numerical indices do not alter the symbolic identity or order.
example (model : DomainModel) :
    stack.eval model (.cons 7 (.cons 3 .nil)) ≠
      [⟨"outer", 7⟩, ⟨"inner", 3⟩] := by
  change ([⟨"outer", 3⟩, ⟨"inner", 7⟩] : Original.Frames) ≠ _
  decide

example (model : DomainModel) (outer inner : Nat) :
    (stack.rename (target := .value .boolean :: [.value .index, .value .index]) .there).eval
      model (.cons true (.cons inner (.cons outer .nil))) =
        stack.eval model (.cons inner (.cons outer .nil)) :=
  stack.eval_rename .there _ _ (fun _ => rfl)

def returns : Values (Comp [] [.value .index, .value .boolean]) [.boolean, .index] :=
  .cons (.present (.var (.there .here))) (.cons (.present (.var .here)) .nil)
def row : Layout [.value .index, .value .boolean] := [.data (.present (.var (.there .here)))]

-- The private residual is hidden by the source scope; acceptance is retained.
example : Readback row (mask 1 [[1], [0]] returns) [.data 0, .absent] := by
  derive_source_readback

-- The same physical row cannot drop a public residual.
example : ¬ Original.outputReferences 1 [[1], [0, 1]] [.data 0, .absent] = some [0] := by decide
example : inputScopes 1 [[1], [0], [0, 1]] [.capability 73, .absent, .data 0] = true := rfl
example : inputScopes 1 [[1], [0], [0, 1]] [.capability 73, .data 1, .data 0] = false := rfl
example : inputScopes 1 [[1]] [.capability 73, .absent] = false := rfl

end Tests.ConnectionContext
