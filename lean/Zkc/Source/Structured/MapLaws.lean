module

public import Zkc.Source.Structured.Evaluation

@[expose] public section

/-! Map equations retain ordered shape checks, complete scalar tuples and the
actual helper invocation. They impose no equations based on helper names. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation

variable {F G : Type} {I J : PIR.Signature}

theorem mapShape_first_exhausted (length : Nat) (rest : List Nat)
    (large : ¬ length < indexLimit) :
    mapShape (length :: rest) = .stopped .exhausted := by
  simp only [mapShape, large, ↓reduceIte]

theorem mapShapeRemaining_exhausted (expected length : Nat) (rest : List Nat)
    (large : ¬ length < indexLimit) :
    mapShapeRemaining expected (length :: rest) = .stopped .exhausted := by
  simp only [mapShapeRemaining, large, ↓reduceIte]

theorem mapShapeRemaining_mismatch (expected length : Nat) (rest : List Nat)
    (small : length < indexLimit) (different : length ≠ expected) :
    mapShapeRemaining expected (length :: rest) = .stopped .refused := by
  simp only [mapShapeRemaining, small, different, ↓reduceIte]

theorem mapShapeRemaining_equal (length : Nat) (rest : List Nat)
    (small : length < indexLimit) :
    mapShapeRemaining length (length :: rest) = mapShapeRemaining length rest := by
  simp only [mapShapeRemaining, small, ↓reduceIte]

theorem mapShapeRemaining_of_equal (length : Nat) (rest : List Nat)
    (small : length < indexLimit) (equal : ∀ value ∈ rest, value = length) :
    mapShapeRemaining length rest = .returned length := by
  induction rest with
  | nil => rfl
  | cons value rest ih =>
    rw [equal value List.mem_cons_self, mapShapeRemaining_equal length rest small]
    exact ih (fun value member => equal value (List.mem_cons_of_mem _ member))

theorem mapShape_of_equal (length : Nat) (rest : List Nat)
    (small : length < indexLimit) (equal : ∀ value ∈ rest, value = length) :
    mapShape (length :: rest) = .returned length := by
  simp only [mapShape, small, ↓reduceIte]
  exact mapShapeRemaining_of_equal length rest small equal

theorem mapRows_congr (left right : Nat → PIR.Proc I F)
    (same : ∀ index, left index = right index) (indices : List Nat) :
    mapRows left indices = mapRows right indices := by
  have equal : left = right := funext same
  rw [equal]

theorem mapRow_table_congr (left right : HelperTable (assignment F G) I) (spec : MapSpec)
    (same : invoke left spec.helper = invoke right spec.helper)
    (args : Values (assignment F G) spec.arguments) (index : Nat) :
    mapRow left spec args index = mapRow right spec args index := by
  simp only [mapRow, same]

theorem denoteMap_table_congr (left right : HelperTable (assignment F G) I) (spec : MapSpec)
    (same : invoke left spec.helper = invoke right spec.helper)
    (args : Values (assignment F G) spec.arguments) :
    denoteMap left spec args = denoteMap right spec args := by
  have rows := funext (mapRow_table_congr left right spec same args)
  simp only [denoteMap, rows]

theorem mapRows_interpret (operations : PIR.OperationInterpretation I J)
    (row : Nat → PIR.Proc I F) (indices : List Nat) :
    (mapRows row indices).interpret operations =
      mapRows (fun index => (row index).interpret operations) indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [mapRows, PIR.Proc.interpret_bind, ih, PIR.Proc.interpret]

/-- Arbitrary complete helper processes can be substituted pointwise. -/
theorem mapRow_equation (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (index : Nat)
    (values : Values (assignment F G) spec.scalarInputs)
    (selected : mapRowArguments spec.field spec.rowwise args index = some values) :
    mapRow table spec args index =
      (invoke table spec.helper values).bind (fun result => .done (result.get .here)) := by
  simp only [mapRow, selected]

theorem mapRows_total_on (row : Nat → PIR.Proc I F) (formula : Nat → F)
    (indices : List Nat) (law : ∀ index ∈ indices, row index = .done (formula index)) :
    mapRows row indices = .done (indices.map formula) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [mapRows, law index List.mem_cons_self]
    simp only [PIR.Proc.bind]
    rw [ih (fun value member => law value (List.mem_cons_of_mem _ member))]
    rfl

/-- Shape failure precedes every helper invocation. -/
theorem denoteMap_shape_stops (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (reason : PIR.Stop)
    (shape : mapShape (mapLengths spec.field spec.rowwise args) = .stopped reason) :
    denoteMap table spec args = .halt reason := by
  simp only [denoteMap, shape, Finite.admitThen]

/-- The logical exhausted branch is stated for actual argument lengths, without
constructing an infeasibly large executable fixture. -/
theorem denoteMap_first_exhausted (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (length : Nat) (rest : List Nat)
    (lengths : mapLengths spec.field spec.rowwise args = length :: rest)
    (large : ¬ length < indexLimit) :
    denoteMap table spec args = .halt .exhausted := by
  apply denoteMap_shape_stops
  rw [lengths, mapShape_first_exhausted length rest large]

/-- Equal empty rows succeed without any helper equation or invocation. -/
theorem denoteMap_empty (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments)
    (shape : mapShape (mapLengths spec.field spec.rowwise args) = .returned 0) :
    denoteMap table spec args = .done (.cons [] .nil) := by
  simp only [denoteMap, shape, Finite.admitThen, List.range_zero, mapRows, PIR.Proc.bind]

/-- The scalar formula must be established for the actual table invocation on
all complete reached tuples. Shape admission includes unused rows. -/
theorem denoteMap_reference (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (length : Nat)
    (shape : mapShape (mapLengths spec.field spec.rowwise args) = .returned length)
    (scalarArgs : Nat → Values (assignment F G) spec.scalarInputs) (formula : Nat → F)
    (selected : ∀ index < length,
      mapRowArguments spec.field spec.rowwise args index = some (scalarArgs index))
    (helper : ∀ index < length, invoke table spec.helper (scalarArgs index) =
      .done (.cons (formula index) .nil)) :
    denoteMap table spec args = .done (.cons ((List.range length).map formula) .nil) := by
  have rows : mapRows (mapRow table spec args) (List.range length) =
      .done ((List.range length).map formula) := by
    apply mapRows_total_on
    intro index member
    have bound := List.mem_range.mp member
    rw [mapRow_equation table spec args index (scalarArgs index) (selected index bound), helper index bound]
    rfl
  simp only [denoteMap, shape, Finite.admitThen, rows, PIR.Proc.bind]

/-- Splitting traversal retains the exact effectful prefix before the suffix. -/
theorem mapRows_append (row : Nat → PIR.Proc I F) (beforeIndices suffix : List Nat) :
    mapRows row (beforeIndices ++ suffix) =
      (mapRows row beforeIndices).bind (fun before =>
        (mapRows row suffix).bind (fun after => .done (before ++ after))) := by
  induction beforeIndices with
  | nil => simp only [List.nil_append, mapRows, PIR.Proc.bind, PIR.Proc.bind_done]
  | cons index rest ih =>
    simp only [List.cons_append, mapRows, ih, PIR.Proc.bind_assoc, PIR.Proc.bind]

/-- A stopped row preserves earlier effects and suppresses every later call. -/
theorem mapRows_stopped_prefix (row : Nat → PIR.Proc I F)
    (beforeIndices suffix : List Nat) (index : Nat) (reason : PIR.Stop)
    (stopped : row index = .halt reason) :
    mapRows row (beforeIndices ++ index :: suffix) =
      (mapRows row beforeIndices).bind (fun _ => .halt reason) := by
  rw [mapRows_append]
  simp only [mapRows, stopped, PIR.Proc.bind]

/-- The stopping premise concerns the actual helper at the selected full tuple. -/
theorem mapRow_helper_stops (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (index : Nat)
    (values : Values (assignment F G) spec.scalarInputs)
    (selected : mapRowArguments spec.field spec.rowwise args index = some values)
    (reason : PIR.Stop) (stopped : invoke table spec.helper values = .halt reason) :
    mapRow table spec args index = .halt reason := by
  rw [mapRow_equation table spec args index values selected, stopped]
  rfl

theorem denoteMap_stopped_prefix (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (length index : Nat)
    (shape : mapShape (mapLengths spec.field spec.rowwise args) = .returned length)
    (beforeIndices suffix : List Nat) (order : List.range length = beforeIndices ++ index :: suffix)
    (values : Values (assignment F G) spec.scalarInputs)
    (selected : mapRowArguments spec.field spec.rowwise args index = some values)
    (reason : PIR.Stop) (stopped : invoke table spec.helper values = .halt reason) :
    denoteMap table spec args =
      (mapRows (mapRow table spec args) beforeIndices).bind (fun _ => .halt reason) := by
  simp only [denoteMap, shape, Finite.admitThen, order]
  rw [mapRows_stopped_prefix _ beforeIndices suffix index reason
    (mapRow_helper_stops table spec args index values selected reason stopped)]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind]

/-- A helper may emit an arbitrary process prefix before stopping. Neither that
prefix nor effects of earlier rows are erased, and later rows are unreachable. -/
theorem denoteMap_helper_effect_prefix {A : Type}
    (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (length index : Nat)
    (shape : mapShape (mapLengths spec.field spec.rowwise args) = .returned length)
    (beforeIndices afterIndices : List Nat)
    (order : List.range length = beforeIndices ++ index :: afterIndices)
    (values : Values (assignment F G) spec.scalarInputs)
    (selected : mapRowArguments spec.field spec.rowwise args index = some values)
    (effects : PIR.Proc I A) (reason : PIR.Stop)
    (stopped : invoke table spec.helper values = effects.bind (fun _ => .halt reason)) :
    denoteMap table spec args = (mapRows (mapRow table spec args) beforeIndices).bind
      (fun _ => effects.bind (fun _ => .halt reason)) := by
  simp only [denoteMap, shape, Finite.admitThen, order]
  rw [mapRows_append]
  simp only [mapRows, mapRow_equation table spec args index values selected,
    stopped, PIR.Proc.bind_assoc, PIR.Proc.bind]

/-- The common restriction ABI checks both complete rows, then broadcasts its
third operand to the actual scalar helper. The output order is zipWith order. -/
theorem denoteMap_twoRows_broadcast (table : HelperTable (assignment F G) I)
    (helperName field : String) (left right : List F) (broadcast : F)
    (small : left.length < indexLimit) (sameLength : right.length = left.length)
    (formula : F → F → F)
    (helper : ∀ a b, invoke table (MapSpec.helper ⟨helperName, field, [true, true, false]⟩)
      (.cons a (.cons b (.cons broadcast .nil))) = .done (.cons (formula a b) .nil)) :
    denoteMap table ⟨helperName, field, [true, true, false]⟩
      (.cons left (.cons right (.cons broadcast .nil))) =
        .done (.cons (List.zipWith formula left right) .nil) := by
  let scalarArgs : Nat → Values (assignment F G) [.field field, .field field, .field field] :=
    fun index => .cons (left[index]?.getD broadcast)
      (.cons (right[index]?.getD broadcast) (.cons broadcast .nil))
  let rowFormula : Nat → F := fun index =>
    formula (left[index]?.getD broadcast) (right[index]?.getD broadcast)
  have equation := denoteMap_reference table ⟨helperName, field, [true, true, false]⟩
    (.cons left (.cons right (.cons broadcast .nil))) left.length
    (by change mapShape [left.length, right.length] = .returned left.length
        rw [sameLength]
        exact mapShape_of_equal _ _ small (by simp)) scalarArgs rowFormula
    (by intro index bound
        have rightBound : index < right.length := by rw [sameLength]; exact bound
        simp only [mapRowArguments, List.getElem?_eq_getElem bound,
          List.getElem?_eq_getElem rightBound, scalarArgs, Option.getD_some]
        rfl)
    (by intro index _; exact helper _ _)
  have ordered : (List.range left.length).map rowFormula = List.zipWith formula left right := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_zipWith, sameLength, Nat.min_self]
    · intro index leftBound rightBound
      have bound : index < left.length := by simpa only [List.length_map, List.length_range] using leftBound
      have boundRight : index < right.length := by rw [sameLength]; exact bound
      simp only [List.getElem_map, List.getElem_range, rowFormula,
        List.getElem?_eq_getElem bound, List.getElem?_eq_getElem boundRight,
        Option.getD_some, List.getElem_zipWith]
  exact equation.trans (congrArg (fun values => PIR.Proc.done (Values.cons values Values.nil)) ordered)

end Zkc.Source.Structured.Evaluation
