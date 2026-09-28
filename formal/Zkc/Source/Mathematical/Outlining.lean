import Zkc.Semantics.Interpretation

/-! A semantic boundary for identified pure calls. The actual carrier checker
must establish which calls it introduced and supply the registered evaluations.
Original effects inhabit a separate constructor and are always forwarded. -/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Outlining

inductive Action (original pureCalls : PIR.Signature) where
  | original (op : original.Op)
  | introduced (op : pureCalls.Op)

abbrev signature (original pureCalls : PIR.Signature) : PIR.Signature where
  Op := Action original pureCalls
  Reply
    | .original op => original.Reply op
    | .introduced op => pureCalls.Reply op

variable {I P : PIR.Signature} {A : Type}

def operations (evaluate : (op : P.Op) → P.Reply op) :
    PIR.OperationInterpretation (signature I P) I
  | .original op => .call op .done
  | .introduced op => .done (evaluate op)

def fold (evaluate : (op : P.Op) → P.Reply op)
    (source : PIR.Proc (signature I P) A) : PIR.Proc I A :=
  source.interpret (operations evaluate)

theorem fold_original (evaluate : (op : P.Op) → P.Reply op) (op : I.Op)
    (next : I.Reply op → PIR.Proc (signature I P) A) :
    fold evaluate (.call (.original op) next) = .call op (fun reply => fold evaluate (next reply)) := rfl

theorem fold_introduced (evaluate : (op : P.Op) → P.Reply op) (op : P.Op)
    (next : P.Reply op → PIR.Proc (signature I P) A) :
    fold evaluate (.call (.introduced op) next) = fold evaluate (next (evaluate op)) := rfl

theorem fold_halt (evaluate : (op : P.Op) → P.Reply op) (reason : PIR.Stop) :
    fold (I := I) (A := A) evaluate (.halt reason) = .halt reason := rfl

theorem fold_bind {B : Type} (evaluate : (op : P.Op) → P.Reply op)
    (source : PIR.Proc (signature I P) A) (next : A → PIR.Proc (signature I P) B) :
    fold evaluate (source.bind next) = (fold evaluate source).bind (fun value => fold evaluate (next value)) :=
  PIR.Proc.interpret_bind _ _ _

/-- Tag every original action without adding a pure call. -/
def embed (source : PIR.Proc I A) : PIR.Proc (signature I P) A :=
  source.interpret (fun op => .call (.original op) .done)

/-- Whole-program forwarding, including arbitrary continuations and halts. -/
theorem fold_embed (evaluate : (op : P.Op) → P.Reply op) (source : PIR.Proc I A) :
    fold evaluate (embed source) = source := by
  induction source with
  | done value => rfl
  | halt reason => rfl
  | call op next ih =>
      change PIR.Proc.call op (fun reply => fold evaluate (embed (next reply))) = .call op next
      congr 1
      funext reply
      exact ih reply

end Zkc.Source.Mathematical.Outlining
