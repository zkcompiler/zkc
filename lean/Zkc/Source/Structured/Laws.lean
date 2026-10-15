module

public import Zkc.Source.Structured.Meaning

@[expose] public section

/-! Reusable contracts for actual imported computations. These equations are
about logical invocation and ordered values, with no native capacity claim. -/

namespace Zkc.Source.Structured

variable {F : Type}

theorem invoke_found (table : Meanings F) (helper : Helper) (body : FunctionMeaning F helper)
    (found : table.find? (fun entry => entry.helper.name == helper.name) = some ⟨helper, body⟩)
    (arguments : Values (scalarAssignment F) helper.inputs) :
    invoke table helper arguments = body arguments := by
  simp [invoke, found]

theorem invoke_extended [CommRing F] [DecidableEq F] (table : Meanings F)
    (definition : CheckedDefinition)
    (arguments : Values (scalarAssignment F) definition.inputs) :
    invoke (extendMeanings table definition) definition.helper arguments =
      definition.body.denote (meaning F table) arguments.get := by
  simp [extendMeanings, invoke]
  rfl

theorem invokeCallback_congr {inputs outputs : List Ty}
    (left right : RegionFunction (scalarAssignment F) closedInterface (inputs, outputs))
    (same : ∀ arguments, left arguments = right arguments)
    (arguments : Values (scalarAssignment F) inputs) :
    invokeCallback left arguments = invokeCallback right arguments := same arguments

/-- ABI packing lemma used before simplifying a concrete imported fold. -/
theorem denoteFold_pack (table : Meanings F) (spec : FoldSpec)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (initial : Values (scalarAssignment F) spec.state)
    (captures : Values (scalarAssignment F) spec.captures) :
    denoteFold table spec (arguments.append (initial.append captures)) =
      Finite.execute (spec.domain.denote arguments)
        (foldTransition table spec arguments captures) initial := by
  simp [denoteFold, Values.split_append]

theorem foldTransition_unfiltered (table : Meanings F) (spec : FoldSpec)
    (absent : spec.predicate.isEmpty = true)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures)
    (state : Values (scalarAssignment F) spec.state)
    (item : scalarAssignment F spec.domain.item) :
    foldTransition table spec arguments captures state item =
      invoke table spec.stepHelper (state.append (.cons item (arguments.append captures))) := by
  simp [foldTransition, absent, PIR.Proc.bind, Values.get]
  rfl

theorem foldTransition_false (table : Meanings F) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures)
    (state : Values (scalarAssignment F) spec.state)
    (item : scalarAssignment F spec.domain.item)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) =
      .done (.cons false .nil)) :
    foldTransition table spec arguments captures state item = .done state := by
  simp [foldTransition, present, predicate, PIR.Proc.bind, Values.get]

theorem foldTransition_true (table : Meanings F) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures)
    (state : Values (scalarAssignment F) spec.state)
    (item : scalarAssignment F spec.domain.item)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) =
      .done (.cons true .nil)) :
    foldTransition table spec arguments captures state item =
      invoke table spec.stepHelper (state.append (.cons item (arguments.append captures))) := by
  simp [foldTransition, present, predicate, PIR.Proc.bind, Values.get]
  rfl

theorem foldTransition_predicate_stops (table : Meanings F) (spec : FoldSpec)
    (present : spec.predicate.isEmpty = false)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures)
    (state : Values (scalarAssignment F) spec.state)
    (item : scalarAssignment F spec.domain.item) (reason : PIR.Stop)
    (predicate : invoke table spec.predicateHelper (.cons item (arguments.append captures)) = .halt reason) :
    foldTransition table spec arguments captures state item = .halt reason := by
  simp [foldTransition, present, predicate, PIR.Proc.bind]

theorem denoteFold_empty (table : Meanings F) (spec : FoldSpec)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (initial : Values (scalarAssignment F) spec.state)
    (captures : Values (scalarAssignment F) spec.captures)
    (empty : (spec.domain.denote arguments).admit = .returned []) :
    denoteFold table spec (arguments.append (initial.append captures)) = .done initial := by
  rw [denoteFold_pack]
  simp [Finite.execute, empty, Finite.admitThen, Finite.fold]

/-- Callback laws on reachable domain items suffice; no arbitrary semantic fuel
or proof about out-of-premise helper inputs is needed. -/
theorem denoteFold_reference (table : Meanings F) (spec : FoldSpec)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (initial : Values (scalarAssignment F) spec.state)
    (captures : Values (scalarAssignment F) spec.captures)
    (items : List (scalarAssignment F spec.domain.item))
    (admitted : (spec.domain.denote arguments).admit = .returned items)
    (reference : Values (scalarAssignment F) spec.state → scalarAssignment F spec.domain.item →
      Values (scalarAssignment F) spec.state)
    (valid : Values (scalarAssignment F) spec.state → Prop) (start : valid initial)
    (law : ∀ state item, item ∈ items → valid state →
      foldTransition table spec arguments captures state item = .done (reference state item) ∧
        valid (reference state item)) :
    denoteFold table spec (arguments.append (initial.append captures)) =
      .done (items.foldl reference initial) := by
  rw [denoteFold_pack]
  simp only [Finite.execute, admitted, Finite.admitThen]
  exact Finite.fold_total_on _ reference valid items initial start law

theorem denoteLoop_congr (state captures : List Ty)
    (left right : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), state ++ captures))
    (same : ∀ arguments, left arguments = right arguments)
    (lower upper : Nat) (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures) :
    denoteLoop state captures left lower upper initial captured =
      denoteLoop state captures right lower upper initial captured := by
  simp only [denoteLoop, invokeCallback, same]

theorem denoteLoop_zero (state captures : List Ty)
    (body : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (empty : upper ≤ lower)
    (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures) :
    denoteLoop state captures body lower upper initial captured = .done initial := by
  simp [denoteLoop, Nat.sub_eq_zero_of_le empty, Finite.execute, Finite.Domain.admit,
    Finite.admitThen, Finite.fold]

/-- A counted callback may be proved under a reachable-state invariant. Its
ordered state and unchanged captures are separate parts of the interface. -/
theorem denoteLoop_reference (state captures : List Ty)
    (body : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), state ++ captures))
    (lower upper : Nat) (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures)
    (reference : Values (scalarAssignment F) state → Nat → Values (scalarAssignment F) state)
    (valid : Values (scalarAssignment F) state → Prop) (start : valid initial)
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
    (body : RegionFunction (scalarAssignment F) closedInterface
      (.index :: (state ++ captures), .boolean :: (state ++ captures)))
    (lower upper : Nat) (empty : upper ≤ lower)
    (initial : Values (scalarAssignment F) state)
    (captured : Values (scalarAssignment F) captures) :
    denoteConditionalLoop state captures body lower upper initial captured = .done initial := by
  simp [denoteConditionalLoop, Nat.sub_eq_zero_of_le empty, Finite.execute,
    Finite.Domain.admit, Finite.admitThen, Finite.fold, PIR.Proc.bind]

theorem boundedAt_exact [CommRing F] [DecidableEq F] (table : Meanings F)
    (domain : String) (container : List F) (index : Nat) (value : F)
    (read : container[index]? = some value) :
    operation table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      .done (.cons value .nil) := by
  change (match container[index]? with
    | some result => (PIR.Proc.done (Values.cons result Values.nil) : Closed (Values (scalarAssignment F) [.field domain]))
    | none => PIR.Proc.halt .refused) = _
  rw [read]
  rfl

theorem boundedAt_refuses [CommRing F] [DecidableEq F] (table : Meanings F)
    (domain : String) (container : List F) (index : Nat)
    (read : container[index]? = none) :
    operation table (.boundedAt domain) (.cons container (.cons index .nil)) .nil =
      .halt .refused := by
  change (match container[index]? with
    | some result => (PIR.Proc.done (Values.cons result Values.nil) : Closed (Values (scalarAssignment F) [.field domain]))
    | none => PIR.Proc.halt .refused) = _
  rw [read]
  rfl

theorem enumerated_index_bound (container : List F) (index : Nat)
    (member : index ∈ List.range container.length) : index < container.length :=
  List.mem_range.mp member

/-- The domain input assignment is explicit, including the exact selected vector.
Other arguments are retained for I/A/C packing but do not select the items. -/
theorem indices_admit (name : String) (types : List Ty) (field : String)
    (container : Var types (.vector field)) (arguments : Values (scalarAssignment F) types)
    (representable : (arguments.get container).length < indexLimit) :
    ((⟨name, types, field, container, true⟩ : DomainSpec).denote arguments).admit =
      .returned (List.range (arguments.get container).length) := by
  change (Finite.Domain.check ((arguments.get container).length < indexLimit) .refused
    (Finite.Domain.elements _)).admit = _
  simp [Finite.Domain.admit, representable]

theorem elements_admit (name : String) (types : List Ty) (field : String)
    (container : Var types (.vector field)) (arguments : Values (scalarAssignment F) types)
    (representable : (arguments.get container).length < indexLimit) :
    ((⟨name, types, field, container, false⟩ : DomainSpec).denote arguments).admit =
      .returned (arguments.get container) := by
  change (Finite.Domain.check ((arguments.get container).length < indexLimit) .refused
    (Finite.Domain.elements _)).admit = _
  simp [Finite.Domain.admit, representable]

theorem stopped_bypasses_suffix {A B : Type} (reason : PIR.Stop) (next : A → Closed B) :
    (PIR.Proc.halt reason : Closed A).bind next = .halt reason := rfl

end Zkc.Source.Structured
