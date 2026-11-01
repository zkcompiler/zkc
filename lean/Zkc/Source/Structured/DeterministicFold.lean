module

public import Zkc.Source.Structured.CollectionReference

@[expose] public section

/-! Encode an ordinary deterministic checked fold into an existing source fold.
Admission and every callback outcome remain explicit premises. The encoder is
arbitrary: this library knows no client state layout or mathematical reference. -/
set_option autoImplicit false
namespace Zkc.Source.Finite

theorem fold_checked_encode {I : PIR.Signature} {A S T : Type}
    (step : T → A → PIR.Process I T) (reference : S → A → PIR.Outcome S)
    (encode : S → T)
    (law : ∀ state item, step (encode state) item =
      (toProcess (I := I) (reference state item)).bind (fun result => .done (encode result)))
    (items : List A) (initial : S) :
    fold step items (encode initial) =
      (toProcess (I := I) (foldChecked reference items initial)).bind
        (fun result => .done (encode result)) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [fold, law]
    cases outcome : reference initial item <;>
      simp only [foldChecked, outcome, toProcess, continueWith, PIR.Process.bind, ih]

end Zkc.Source.Finite

namespace Zkc.Source.Structured.Evaluation

theorem denoteFoldOn_checked {model : DomainModel} {A S : Type}
    (table : MeaningsOn model.toCarriers closedInterface) (spec : FoldSpec)
    (arguments : Values model.Value spec.domain.inputs)
    (captures : Values model.Value spec.captures)
    (items : List A) (pack : A → Values model.Value spec.domain.items)
    (encode : S → Values model.Value spec.state) (initial : S)
    (admitted : spec.domain.admit arguments = .returned (items.map pack))
    (reference : S → A → PIR.Outcome S)
    (law : ∀ state item, foldTransitionOn table spec arguments captures (encode state) (pack item) =
      (Finite.toProcess (reference state item)).bind (fun result => .done (encode result))) :
    denoteFoldOn table spec (arguments.append ((encode initial).append captures)) =
      (Finite.toProcess (Finite.foldChecked reference items initial)).bind
        (fun result => .done (encode result)) := by
  simp only [denoteFoldOn, Values.split_append, admitted, Finite.admitThen, Finite.fold_map]
  exact Finite.fold_checked_encode _ reference encode law items initial

end Zkc.Source.Structured.Evaluation
