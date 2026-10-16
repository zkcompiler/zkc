module

public import Zkc.Source.Constructed

@[expose] public section

/-! Scalar constructed-subject normalization support. The transparent typed
program is tied to the actual exported syntax by a checked erasure equation. -/
set_option autoImplicit false
namespace Zkc.Source.Constructed

/-- Expose the typed body without recomputing admission in every denotation
comparison. The executable checker still admits exactly this complete body. -/
theorem Snapshot.check_program (snapshot : Snapshot)
    (program : Program language (snapshot.inputs.map scalar) snapshot.outputs)
    (shape : snapshot.shapeValid = true)
    (body : snapshot.raw = .ok program.erase) :
    snapshot.check = .ok ⟨program⟩ := by
  simp only [Snapshot.check, shape, ite_true, body, Program.elaborate_erase]

@[simp] theorem environment_push_here {V : Ty → Type} {Γ : List Ty} {ty : Ty}
    (env : Environment V Γ) (value : V ty) : env.push value .here = value := rfl

@[simp] theorem environment_push_there {V : Ty → Type} {Γ : List Ty} {ty head : Ty}
    (env : Environment V Γ) (value : V head) (reference : Var Γ ty) :
    env.push value (.there reference) = env reference := rfl

@[simp] theorem values_get_here {V : Ty → Type} {Γ : List Ty} {ty : Ty}
    (value : V ty) (values : Values V Γ) : (Values.cons value values).get .here = value := rfl

@[simp] theorem values_get_there {V : Ty → Type} {Γ : List Ty} {ty head : Ty}
    (value : V head) (values : Values V Γ) (reference : Var Γ ty) :
    (Values.cons value values).get (.there reference) = values.get reference := rfl

@[simp] theorem tupleAt_pair_first {V : String → Type} {first second : String}
    (a : V first) (b : V second) :
    tupleAt (.cons a (.cons b .nil)) 0 = a := rfl

@[simp] theorem tupleAt_pair_second {V : String → Type} {first second : String}
    (a : V first) (b : V second) :
    tupleAt (.cons a (.cons b .nil)) 1 = b := rfl

/-- Exact native occurrence metadata is part of the selected ideal experiment's
public domain separation. Encoding it to bytes is a separate obligation. -/
structure OccurrenceContext (Context : Type) where
  application : Context
  policy : String
  occurrences : List Primitive
  deriving DecidableEq

end Zkc.Source.Constructed
