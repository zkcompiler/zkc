import Zkc.Source.Closures
import Zkc.Semantics.Boundary

set_option autoImplicit false

namespace PIR.Source
open Zkc.Source.Expressions Zkc.Source.Availability

variable {F : Type} [Ring F] [DecidableEq F]
variable {I : Signature} {A S T E G O : Type}

/-- The current pure closure fragment elaborates to a value return. Effectful
    source syntax needs its own interpretation; k below is a fixed supplied
    continuation, not a serialized source closure. -/
def elaborate {n : Nat} (b : Bound n F) : Proc I F := .done b.value

theorem elaboration_exact (scope : List Nat) (s : Env F) (c : Closure Nat)
    (b : Bound c.size F) (accepted : issue scope s c = some b)
    (k : F → Proc I A) (h : Handler I S E) (state : S) :
    ((elaborate b).bind k).run h state =
      (k (c.expand.eval (total s))).run h state := by
  change (k b.value).run h state = _
  rw [issued_value scope s c b accepted]

theorem elaboration_boundary {n : Nat} (b : Bound n F) (P : Interaction I)
    (phase : P.Phase) :
    Conforms P (elaborate b) phase ∧ Within 0 (elaborate (I := I) b) ∧
    Boundary.Returns P (fun value after => value = b.value ∧ after = phase)
      (elaborate b) phase := ⟨trivial, trivial, rfl, rfl⟩

/-- Source admission supplies equality of the actual captured computation;
    the existing handler relation then supplies complete execution refinement.
    Both the source and continuation are fixed across the comparison. -/
theorem admitted_context_related {Role H : Type} [DecidableEq Role]
    (actor : Role) (bindings : List (SourceView.Slot Role))
    (w v : SourceView.World Role F H) (c : Closure Nat)
    (x y : Bound c.size F)
    (hx : admit actor bindings w c = some x) (hy : admit actor bindings v c = some y)
    (agree : SourceView.SameView actor w v)
    (R : S → T → Prop) (left : E → List O) (right : G → List O)
    (h : Handler I S E) (g : Handler I T G)
    (law : HandlerRelated R left right h g) (k : F → Proc I A)
    (s : S) (t : T) (initial : R s t) :
    Related R left right (((elaborate x).bind k).run h s)
      (((elaborate y).bind k).run g t) := by
  have same : x = y := Option.some.inj
    (hx.symm.trans ((admission_same_view actor bindings w v c agree).trans hy))
  subst y
  exact run_related R left right h g law _ s t initial

end PIR.Source
