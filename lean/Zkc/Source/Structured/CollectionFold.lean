module

public import Zkc.Source.Structured.DeterministicFold

@[expose] public section

/-! List accumulation through arbitrary state encoders. These laws own the
existing checked-fold proofs; clients choose chunks, encodings and actual callback
equations. Admission and body association remain separate checked obligations.
No algebraic structure on the list elements is required. -/
set_option autoImplicit false
namespace Zkc.Source.Finite

/-- A checked chunk is consulted only on a reached iteration. In particular,
zero repetitions do not introduce an admission check absent from the source. -/
def repeatAppend {B : Type} (chunk : PIR.Outcome (List B)) (count : Nat)
    (initial : List B) : PIR.Outcome (List B) :=
  match count with
  | 0 => .returned initial
  | _ + 1 => continueWith chunk fun values =>
      .returned (initial ++ (List.replicate count values).flatten)

@[simp] theorem repeatAppend_returned {B : Type} (chunk : List B) (count : Nat)
    (initial : List B) :
    repeatAppend (.returned chunk) count initial =
      .returned (initial ++ (List.replicate count chunk).flatten) := by
  cases count <;> simp only [repeatAppend, continueWith, List.replicate_zero,
    List.flatten_nil, List.append_nil]

theorem fold_append_encode {I : PIR.Signature} {A B S : Type}
    (step : S → A → PIR.Process I S) (encode : List B → S) (chunk : A → List B)
    (law : ∀ xs item, step (encode xs) item = .done (encode (xs ++ chunk item)))
    (items : List A) (initial : List B) :
    fold step items (encode initial) = .done (encode (initial ++ items.flatMap chunk)) := by
  let reference := fun (xs : List B) (item : A) => PIR.Outcome.returned (xs ++ chunk item)
  have checked : toProcess (I := I) (foldChecked reference items initial) =
      .done (initial ++ items.flatMap chunk) := by
    rw [← fold_checked, fold_total _ (fun xs item => xs ++ chunk item) (by intros; rfl)]
    rw [List.foldl_append_eq_append]
    rfl
  rw [fold_checked_encode step reference encode
    (by simpa only [reference, toProcess, PIR.Process.bind] using law), checked]
  rfl

theorem fold_repeat_encode {I : PIR.Signature} {B S : Type}
    (step : S → Nat → PIR.Process I S) (encode : List B → S) (chunk : List B)
    (law : ∀ xs index, step (encode xs) index = .done (encode (xs ++ chunk)))
    (start count : Nat) (initial : List B) :
    fold step (List.range' start count) (encode initial) =
      .done (encode (initial ++ (List.replicate count chunk).flatten)) := by
  rw [fold_append_encode step encode (fun _ => chunk) law]
  simp only [List.flatMap, List.map_const', List.length_range']

end Zkc.Source.Finite

namespace Zkc.Source.Structured.Evaluation

/-- An admitted collection fold accumulates checked chunks through any complete
state encoder. Domain admission and the actual callback law remain explicit. -/
theorem denoteFoldOn_append_encode {model : DomainModel} {A B : Type}
    (table : MeaningsOn model.toCarriers closedInterface) (spec : FoldSpec)
    (arguments : Values model.Value spec.domain.inputs)
    (captures : Values model.Value spec.captures)
    (items : List A) (pack : A → Values model.Value spec.domain.items)
    (encode : List B → Values model.Value spec.state) (initial : List B)
    (admitted : spec.domain.admit arguments = .returned (items.map pack))
    (chunk : A → List B)
    (law : ∀ state item, foldTransitionOn table spec arguments captures (encode state) (pack item) =
      .done (encode (state ++ chunk item))) :
    denoteFoldOn table spec (arguments.append ((encode initial).append captures)) =
      .done (encode (initial ++ items.flatMap chunk)) := by
  simp only [denoteFoldOn, Values.split_append, admitted, Finite.admitThen, Finite.fold_map]
  exact Finite.fold_append_encode _ encode chunk law items initial


theorem denoteLoopOn_append_encode {carriers : Carriers} {I : PIR.Signature} {B : Type}
    (state captures : List Ty)
    (body : RegionFunction carriers.Value I (.index :: (state ++ captures), state ++ captures))
    (encode : List B → Values carriers.Value state) (captured : Values carriers.Value captures)
    (chunk : List B) (count : Nat) (initial : List B)
    (law : ∀ xs index, body (.cons index ((encode xs).append captured)) =
      .done ((encode (xs ++ chunk)).append captured)) :
    denoteLoopOn state captures body 0 count (encode initial) captured =
      .done (encode (initial ++ (List.replicate count chunk).flatten)) := by
  simp only [denoteLoopOn, Finite.execute, Finite.Domain.admit, Finite.admitThen,
    Nat.sub_zero]
  apply Finite.fold_repeat_encode _ encode chunk _ 0 count initial
  intro xs index
  simp only [invokeCallbackOn, law, PIR.Process.bind, Values.split_append]

/-- Checked repetition retains the first stopping callback, and does not call
it on an empty range. The callback still returns the complete captured row. -/
theorem denoteLoopOn_repeatAppend {carriers : Carriers} {I : PIR.Signature} {B : Type}
    (state captures : List Ty)
    (body : RegionFunction carriers.Value I (.index :: (state ++ captures), state ++ captures))
    (encode : List B → Values carriers.Value state) (captured : Values carriers.Value captures)
    (chunk : PIR.Outcome (List B)) (count : Nat) (initial : List B)
    (law : ∀ xs index, body (.cons index ((encode xs).append captured)) =
      (Finite.toProcess chunk).bind fun values =>
        .done ((encode (xs ++ values)).append captured)) :
    denoteLoopOn state captures body 0 count (encode initial) captured =
      (Finite.toProcess (Finite.repeatAppend chunk count initial)).bind
        (fun result => .done (encode result)) := by
  cases chunk with
  | returned values =>
    have total := denoteLoopOn_append_encode state captures body encode captured values count initial
      (by simpa only [Finite.toProcess, PIR.Process.bind] using law)
    cases count <;> simpa only [Finite.repeatAppend, Finite.continueWith,
      Finite.toProcess, PIR.Process.bind, List.replicate_zero, List.flatten_nil,
      List.append_nil] using total
  | stopped reason =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [denoteLoopOn, Finite.execute, Finite.Domain.admit, Finite.admitThen,
        Nat.sub_zero, List.range'_succ, Finite.fold, invokeCallbackOn, law,
        Finite.toProcess, PIR.Process.bind, Finite.repeatAppend, Finite.continueWith]

end Zkc.Source.Structured.Evaluation
