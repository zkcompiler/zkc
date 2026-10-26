module

public import Zkc.Source.Structured.CollectEvaluation

@[expose] public section

/-! Collection laws retain ordered admission and callback stops. These are
logical process equations, independent of native execution and capacity policy. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation
variable {carriers : Carriers} {interface : PIR.Signature}

/-- The domain and captures are packed once in the occurrence's declared order. -/
theorem denoteCollect_pack (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures) :
    denoteCollect table spec (arguments.append captures) =
      Finite.admitThen (spec.domain.admit arguments) fun items =>
        (Finite.fold (collectTransition table spec arguments captures) items []).bind fun collected =>
          .done (.cons (spec.collection.pack collected.reverse) .nil) := by
  simp only [denoteCollect, Values.split_append]

theorem denoteCollect_empty (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (empty : spec.domain.admit arguments = .returned []) :
    denoteCollect table spec (arguments.append captures) =
      .done (.cons (spec.collection.pack []) .nil) := by
  rw [denoteCollect_pack, empty]
  rfl

theorem denoteCollect_admission_stop (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures) (reason : PIR.Stop)
    (stopped : spec.domain.admit arguments = .stopped reason) :
    denoteCollect table spec (arguments.append captures) = .halt reason := by
  rw [denoteCollect_pack, stopped]
  rfl

/-- An unfiltered collection invokes the exact body with its complete tuple. -/
theorem collectTransition_unfiltered (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (absent : spec.predicate.isEmpty = true)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (collected : List (carriers.Value spec.collection.element))
    (item : Values carriers.Value spec.domain.items) :
    collectTransition table spec arguments captures collected item =
      (invoke table spec.bodyHelper (item.append (arguments.append captures))).bind fun value =>
        .done (value.get .here :: collected) := by
  simp only [collectTransition, absent, ↓reduceIte, PIR.Process.bind, Values.get]

/-- A scalar formula is justified through the actual callback on each admitted
item. The packing map retains every tuple component, domain argument and capture;
this rule supplies no formula classification from native or generated names. -/
theorem denoteCollect_reference {A : Type}
    (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (items : List A) (pack : A → Values carriers.Value spec.domain.items)
    (admitted : spec.domain.admit arguments = .returned (items.map pack))
    (absent : spec.predicate.isEmpty = true)
    (formula : A → carriers.Value spec.collection.element)
    (law : ∀ item ∈ items,
      invoke table spec.bodyHelper ((pack item).append (arguments.append captures)) =
        .done (.cons (formula item) .nil)) :
    denoteCollect table spec (arguments.append captures) =
      .done (.cons (spec.collection.pack (items.map formula)) .nil) := by
  rw [denoteCollect_pack]
  simp only [admitted, Finite.admitThen, Finite.fold_map]
  have folded := Finite.fold_total_on
    (fun collected item => collectTransition table spec arguments captures collected (pack item))
    (fun collected item => formula item :: collected) (fun _ => True) items [] trivial (by
      intro collected item member _
      constructor
      · rw [collectTransition_unfiltered _ _ absent, law item member]
        rfl
      · trivial)
  rw [folded]
  have ordered (xs : List A) (acc : List (carriers.Value spec.collection.element)) :
      (xs.foldl (fun collected item => formula item :: collected) acc).reverse =
        acc.reverse ++ xs.map formula := by
    induction xs generalizing acc with
    | nil => simp only [List.foldl_nil, List.map_nil, List.append_nil]
    | cons item rest ih =>
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_cons,
        List.append_assoc, List.singleton_append]
  simp only [PIR.Process.bind, ordered, List.reverse_nil, List.nil_append]

theorem collectTransition_false (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (collected : List (carriers.Value spec.collection.element))
    (item : Values carriers.Value spec.domain.items)
    (predicate : invoke table spec.predicateHelper (item.append (arguments.append captures)) =
      .done (.cons false .nil)) :
    collectTransition table spec arguments captures collected item = .done collected := by
  simp only [collectTransition, present, Bool.false_eq_true, ↓reduceIte, predicate,
    PIR.Process.bind, Values.get]

theorem collectTransition_predicate_stop (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (collected : List (carriers.Value spec.collection.element))
    (item : Values carriers.Value spec.domain.items) (reason : PIR.Stop)
    (predicate : invoke table spec.predicateHelper (item.append (arguments.append captures)) = .halt reason) :
    collectTransition table spec arguments captures collected item = .halt reason := by
  simp only [collectTransition, present, Bool.false_eq_true, ↓reduceIte, predicate, PIR.Process.bind]

theorem collectTransition_body_stop (table : HelperTable carriers.Value interface) (spec : CollectSpec)
    (absent : spec.predicate.isEmpty = true)
    (arguments : Values carriers.Value spec.domain.inputs)
    (captures : Values carriers.Value spec.captures)
    (collected : List (carriers.Value spec.collection.element))
    (item : Values carriers.Value spec.domain.items) (reason : PIR.Stop)
    (body : invoke table spec.bodyHelper (item.append (arguments.append captures)) = .halt reason) :
    collectTransition table spec arguments captures collected item = .halt reason := by
  simp only [collectTransition, absent, ↓reduceIte, PIR.Process.bind, Values.get, body]

end Zkc.Source.Structured.Evaluation
