module

public import Zkc.Source.Structured.Meaning

@[expose] public section

/-! Reusable contracts for actual imported computations. These equations are
about logical invocation and ordered values, with no native capacity claim. -/

namespace Zkc.Source.Structured

namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable (observations : SiteObservations interface)

theorem invoke_found (table : HelperTable (assignment F G) interface) (helper : Helper) (body : HelperFunction (assignment F G) interface helper)
    (found : table.find? (fun entry => entry.helper.name == helper.name) = some ⟨helper, body⟩)
    (arguments : Values (assignment F G) helper.inputs) :
    invoke table helper arguments = body arguments := by
  simp [invoke, found]

theorem invoke_extended [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] (table : HelperTable (assignment F G) interface)
    (definition : CheckedDefinition)
    (arguments : Values (assignment F G) definition.inputs) :
    invoke (extendMeanings observations table definition) definition.helper arguments =
      definition.body.denote (meaning observations table) arguments.get := by
  simp [extendMeanings, invoke]
  rfl

theorem invokeCallback_congr {inputs outputs : List Ty}
    (left right : RegionFunction (assignment F G) interface (inputs, outputs))
    (same : ∀ arguments, left arguments = right arguments)
    (arguments : Values (assignment F G) inputs) :
    invokeCallback left arguments = invokeCallback right arguments := same arguments

/-- ABI packing lemma used before simplifying a concrete imported fold. -/
theorem denoteFold_pack (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (initial : Values (assignment F G) spec.state)
    (captures : Values (assignment F G) spec.captures) :
    denoteFold table spec (arguments.append (initial.append captures)) =
      Finite.execute (spec.domain.denote arguments)
        (foldTransition table spec arguments captures) initial := by
  simp [denoteFold, Values.split_append]

theorem foldTransition_unfiltered (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (absent : spec.predicate.isEmpty = true)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state)
    (item : assignment F G spec.domain.item) :
    foldTransition table spec arguments captures state item =
      invoke table spec.stepHelper (state.append (.cons item (arguments.append captures))) := by
  simp [foldTransition, absent, PIR.Proc.bind, Values.get]
  rfl

theorem foldTransition_false (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state)
    (item : assignment F G spec.domain.item)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) =
      .done (.cons false .nil)) :
    foldTransition table spec arguments captures state item = .done state := by
  simp [foldTransition, present, predicate, PIR.Proc.bind, Values.get]

theorem foldTransition_true (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state)
    (item : assignment F G spec.domain.item)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) =
      .done (.cons true .nil)) :
    foldTransition table spec arguments captures state item =
      invoke table spec.stepHelper (state.append (.cons item (arguments.append captures))) := by
  simp [foldTransition, present, predicate, PIR.Proc.bind, Values.get]
  rfl

theorem foldTransition_predicate_stops (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures)
    (state : Values (assignment F G) spec.state)
    (item : assignment F G spec.domain.item) (reason : PIR.Stop)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) = .halt reason) :
    foldTransition table spec arguments captures state item = .halt reason := by
  simp [foldTransition, present, predicate, PIR.Proc.bind]

theorem denoteFold_empty (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (initial : Values (assignment F G) spec.state)
    (captures : Values (assignment F G) spec.captures)
    (empty : (spec.domain.denote arguments).admit = .returned []) :
    denoteFold table spec (arguments.append (initial.append captures)) = .done initial := by
  rw [denoteFold_pack]
  simp [Finite.execute, empty, Finite.admitThen, Finite.fold]

/-- Callback laws on reachable domain items suffice; no arbitrary semantic fuel
or proof about out-of-premise helper inputs is needed. -/
theorem denoteFold_reference (table : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (initial : Values (assignment F G) spec.state)
    (captures : Values (assignment F G) spec.captures)
    (items : List (assignment F G spec.domain.item))
    (admitted : (spec.domain.denote arguments).admit = .returned items)
    (reference : Values (assignment F G) spec.state → assignment F G spec.domain.item →
      Values (assignment F G) spec.state)
    (valid : Values (assignment F G) spec.state → Prop) (start : valid initial)
    (law : ∀ state item, item ∈ items → valid state →
      foldTransition table spec arguments captures state item = .done (reference state item) ∧
        valid (reference state item)) :
    denoteFold table spec (arguments.append (initial.append captures)) =
      .done (items.foldl reference initial) := by
  rw [denoteFold_pack]
  simp only [Finite.execute, admitted, Finite.admitThen]
  exact Finite.fold_total_on _ reference valid items initial start law

theorem denoteLoop_congr (state captures : List Ty)
    (left right : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), state ++ captures))
    (same : ∀ arguments, left arguments = right arguments)
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    denoteLoop state captures left lower upper initial captured =
      denoteLoop state captures right lower upper initial captured := by
  simp only [denoteLoop, invokeCallback, same]

theorem denoteLoop_zero (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (empty : upper ≤ lower)
    (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    denoteLoop state captures body lower upper initial captured = .done initial := by
  simp [denoteLoop, Nat.sub_eq_zero_of_le empty, Finite.execute, Finite.Domain.admit,
    Finite.admitThen, Finite.fold]

/-- A counted callback may be proved under a reachable-state invariant. Its
ordered state and unchanged captures are separate parts of the interface. -/
theorem denoteLoop_reference (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures)
    (reference : Values (assignment F G) state → Nat → Values (assignment F G) state)
    (valid : Values (assignment F G) state → Prop) (start : valid initial)
    (law : ∀ current index, index ∈ List.range' lower (upper - lower) → valid current →
      invokeCallback body (.cons index (current.append captured)) =
        .done ((reference current index).append captured) ∧ valid (reference current index)) :
    denoteLoop state captures body lower upper initial captured =
      .done ((List.range' lower (upper - lower)).foldl reference initial) := by
  simp only [denoteLoop, Finite.execute, Finite.Domain.admit, Finite.admitThen]
  apply Finite.fold_total_on _ reference valid _ initial start
  intro current index member invariant
  obtain ⟨equation, preserved⟩ := law current index member invariant
  exact ⟨by simp [equation, PIR.Proc.bind, Values.split_append], preserved⟩

theorem denoteConditionalLoop_zero (state captures : List Ty)
    (body : RegionFunction (assignment F G) interface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (empty : upper ≤ lower)
    (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) :
    denoteConditionalLoop state captures body lower upper initial captured = .done initial := by
  simp [denoteConditionalLoop, Nat.sub_eq_zero_of_le empty, Finite.execute,
    Finite.Domain.admit, Finite.admitThen, Finite.fold, PIR.Proc.bind]

theorem boundedAt_exact [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] (table : HelperTable (assignment F G) interface)
    (domain : String) (container : List F) (index : Nat) (value : F)
    (read : container[index]? = some value) :
    operation observations table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      .done (.cons value .nil) := by
  change (match container[index]? with
    | some result => (PIR.Proc.done (Values.cons result Values.nil) : PIR.Proc interface (Values (assignment F G) [.field domain]))
    | none => PIR.Proc.halt .refused) = _
  rw [read]
  rfl

theorem boundedAt_refuses [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] (table : HelperTable (assignment F G) interface)
    (domain : String) (container : List F) (index : Nat)
    (read : container[index]? = none) :
    operation observations table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      .halt .refused := by
  change (match container[index]? with
    | some result => (PIR.Proc.done (Values.cons result Values.nil) : PIR.Proc interface (Values (assignment F G) [.field domain]))
    | none => PIR.Proc.halt .refused) = _
  rw [read]
  rfl

theorem enumerated_index_bound (container : List F) (index : Nat)
    (member : index ∈ List.range container.length) : index < container.length :=
  List.mem_range.mp member

/-- The domain input assignment is explicit, including the exact selected vector.
Other arguments are retained for I/A/C packing but do not select the items. -/
theorem indices_admit (name : String) (types : List Ty) (field : String)
    (container : Var types (.vector field)) (arguments : Values (assignment F G) types)
    (representable : (arguments.get container).length < indexLimit) :
    ((⟨name, types, field, container, true⟩ : DomainSpec).denote arguments).admit =
      .returned (List.range (arguments.get container).length) := by
  change (Finite.Domain.check ((arguments.get container).length < indexLimit) .exhausted
    (Finite.Domain.elements _)).admit = _
  simp [Finite.Domain.admit, representable]

theorem elements_admit (name : String) (types : List Ty) (field : String)
    (container : Var types (.vector field)) (arguments : Values (assignment F G) types)
    (representable : (arguments.get container).length < indexLimit) :
    ((⟨name, types, field, container, false⟩ : DomainSpec).denote arguments).admit =
      .returned (arguments.get container) := by
  change (Finite.Domain.check ((arguments.get container).length < indexLimit) .exhausted
    (Finite.Domain.elements _)).admit = _
  simp [Finite.Domain.admit, representable]

theorem stopped_bypasses_suffix {A B : Type} (reason : PIR.Stop) (next : A → PIR.Proc interface B) :
    (PIR.Proc.halt reason : PIR.Proc interface A).bind next = .halt reason := rfl

section Group

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
variable (table : HelperTable (assignment F G) interface)

/-- The group identity is the additive identity of the explicitly chosen group. -/
theorem groupIdentity_exact (domain : String) :
    operation observations table (.groupIdentity domain) .nil .nil =
      .done (.cons (0 : G) .nil) := rfl

theorem groupAdd_exact (domain : String) (left right : G) :
    operation observations table (.groupAdd domain)
      (.cons left (.cons right .nil)) .nil = .done (.cons (left + right) .nil) := rfl

/-- The source operands are group, scalar; the module action is scalar on group. -/
theorem groupScale_exact (group field : String) (point : G) (scalar : F) :
    operation observations table (.groupScale group field)
      (.cons point (.cons scalar .nil)) .nil = .done (.cons (scalar • point) .nil) := rfl

theorem groupEqual_exact (domain : String) (left right : G) :
    operation observations table (.groupEqual domain)
      (.cons left (.cons right .nil)) .nil = .done (.cons (decide (left = right)) .nil) := rfl

theorem groupAdd_comm (domain : String) (left right : G) :
    operation observations table (.groupAdd domain)
      (.cons left (.cons right .nil)) .nil =
    operation observations table (.groupAdd domain)
      (.cons right (.cons left .nil)) .nil := by
  simp only [groupAdd_exact, add_comm]

theorem groupScale_add (group field : String) (left right : G) (scalar : F) :
    operation observations table (.groupScale group field)
      (.cons (left + right) (.cons scalar .nil)) .nil =
      .done (.cons (scalar • left + scalar • right) .nil) := by
  simp only [groupScale_exact, smul_add]

end Group

/-- A mark retains its effect even though the operation has no operands/results. -/
theorem operation_mark [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (table : HelperTable (assignment F G) interface) (site : String) :
    operation observations table (.mark site) .nil .nil =
      (observations.mark site).bind (fun _ => .done .nil) := rfl

end Evaluation

end Zkc.Source.Structured
