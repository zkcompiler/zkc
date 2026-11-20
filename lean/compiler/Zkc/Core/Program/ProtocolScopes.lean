module

public import Zkc.Core.Program.ProtocolRules

@[expose] public section

/-! Deciding the role scopes of typed protocol regions. -/

namespace Zkc.Core

section
variable {V : Vocabulary} {hs : Headers V}

def ProtocolOp.decideWithin {ins outs : List (LTy V)} (roles : List Role)
    (op : ProtocolOp V hs ins outs) : Decidable (op.Within roles) := by
  cases op <;> unfold ProtocolOp.Within <;> infer_instance

mutual
  def decideWithin (roles : List Role) : {Γ : Ctx (LTy V)} → {outs : List (LTy V)} →
      (body : Term (protocolDialect V hs) Γ outs) → Decidable (Within roles body)
    | _, _, .ret _ => isTrue trivial
    | _, _, .op _ op _ _ rest => by
      unfold Within
      letI := op.decideWithin roles
      letI := decideWithin roles rest
      infer_instance
    | _, _, .guard _ ps _ _ _ rest => by
      unfold Within
      letI := decideWithin roles rest
      infer_instance
    | _, _, .choose _ ps _ _ _ yes no _ rest => by
      unfold Within
      letI := decideWithin roles yes
      letI := decideWithin roles no
      letI := decideWithin roles rest
      infer_instance
    | _, _, .cases _ ps _ _ _ arms _ rest => by
      unfold Within
      letI := decideWithinArms roles arms
      letI := decideWithin roles rest
      infer_instance
    | _, _, .loop _ ps _ _ _ _ body _ rest => by
      unfold Within
      letI := decideWithin roles body
      letI := decideWithin roles rest
      infer_instance
    | _, _, .block _ _ body _ rest => by
      unfold Within
      letI := decideWithin roles body
      letI := decideWithin roles rest
      infer_instance
    | _, _, .attempt _ ps _ _ body _ rest => by
      unfold Within
      letI := decideWithin roles body
      letI := decideWithin roles rest
      infer_instance
  def decideWithinArms (roles : List Role) : {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
      (arms : Arms (protocolDialect V hs) Γ mid payloads) → Decidable (WithinArms roles arms)
    | _, _, _, .nil => isTrue trivial
    | _, _, _, .cons _ arm rest => by
      unfold WithinArms
      letI := decideWithin roles arm
      letI := decideWithinArms roles rest
      infer_instance
end

mutual
  /-- At an operation and at a guard the proposition is by definition that of the rest, and the
  decision of the rest is returned as it is. Reaching it through `unfold` leaves a cast there,
  and the kernel's check of that cast grows with the rest of the run, so that evaluating the
  decision of a run of operations and guards is quadratic in its length. -/
  def decideEnclosed : {Γ : Ctx (LTy V)} → {outs : List (LTy V)} →
      (body : Term (protocolDialect V hs) Γ outs) → Decidable (Enclosed body)
    | _, _, .ret _ => isTrue trivial
    | _, _, .op _ _ _ _ rest => decideEnclosed rest
    | _, _, .guard _ _ _ _ _ rest => decideEnclosed rest
    | _, _, .choose _ ps _ _ _ yes no _ rest => by
      unfold Enclosed
      letI := decideWithin ps yes
      letI := decideWithin ps no
      letI := decideEnclosed yes
      letI := decideEnclosed no
      letI := decideEnclosed rest
      infer_instance
    | _, _, .cases _ ps _ _ _ arms _ rest => by
      unfold Enclosed
      letI := decideWithinArms ps arms
      letI := decideEnclosedArms arms
      letI := decideEnclosed rest
      infer_instance
    | _, _, .loop _ ps _ _ _ _ body _ rest => by
      unfold Enclosed
      letI := decideWithin ps body
      letI := decideEnclosed body
      letI := decideEnclosed rest
      infer_instance
    | _, _, .block _ _ body _ rest => by
      unfold Enclosed
      letI := decideEnclosed body
      letI := decideEnclosed rest
      infer_instance
    | _, _, .attempt _ _ _ _ body _ rest => by
      unfold Enclosed
      letI := decideEnclosed body
      letI := decideEnclosed rest
      infer_instance
  def decideEnclosedArms : {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
      (arms : Arms (protocolDialect V hs) Γ mid payloads) → Decidable (EnclosedArms arms)
    | _, _, _, .nil => isTrue trivial
    | _, _, _, .cons _ arm rest => by
      unfold EnclosedArms
      letI := decideEnclosed arm
      letI := decideEnclosedArms rest
      infer_instance
end

end

end Zkc.Core
