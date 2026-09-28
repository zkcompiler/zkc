import Zkc.Source.Mathematical.GraphPrefix
import Zkc.Source.Mathematical.Static
import Zkc.Source.Mathematical.TypeCapacity

/-! Executable elaboration of resolved pure graphs into intrinsic syntax.

Operation resolution and type-template substitution precede this boundary.
No source type annotation can authorize a forward reference, an implicit
capture, a differently typed operand or a changed fold invariant. Success
retains an exact erasure equation to the supplied finite graph.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Graph

inductive Raw (Op : Type) (Count : Type := Nat) where
  | outputs (refs : List Nat)
  | operation (op : Op) (args : List Nat) (next : Raw Op Count)
  | tuple (args : List Nat) (next : Raw Op Count)
  | project (value component : Nat) (next : Raw Op Count)
  | map (count : Count) (captures : List Nat) (body next : Raw Op Count)
  | fold (count : Count) (initial captures : List Nat) (body next : Raw Op Count)
  deriving DecidableEq, Repr

inductive Error where
  | resource
  | depth
  | scope
  | arity
  | type
  | product
  | invariant
  | count
  deriving DecidableEq, Repr

variable {Ty : Type}

structure Selected (Γ : List Ty) (index : Nat) where
  ty : Ty
  value : Var Γ ty
  erasure : value.index = index

instance {Γ : List Ty} {index : Nat} : Subsingleton (Selected Γ index) where
  allEq left right := by
    have sameIndex := left.erasure.trans right.erasure.symm
    have sameType := left.value.type_eq_of_index right.value sameIndex
    cases left with
    | mk leftTy left leftEq =>
      cases right with
      | mk rightTy right rightEq =>
        dsimp only at sameType sameIndex
        cases sameType
        cases left.eq_of_index right sameIndex
        rfl

def select : (Γ : List Ty) → (index : Nat) → Except Error (Selected Γ index)
  | [], _ => .error .scope
  | ty :: _, 0 => .ok ⟨ty, .here, rfl⟩
  | _ :: Γ, index + 1 => do
      let selected ← select Γ index
      return ⟨selected.ty, .there selected.value, by simp [Var.index, selected.erasure]⟩

@[inline] def Selected.castResult {Γ Δ : List Ty} {index other : Nat}
    (context : Γ = Δ) (position : index = other)
    (result : Except Error (Selected Γ index)) : Except Error (Selected Δ other) :=
  context ▸ position ▸ result

@[simp] theorem Selected.castResult_isOk {Γ Δ : List Ty} {index other : Nat}
    (context : Γ = Δ) (position : index = other)
    (result : Except Error (Selected Γ index)) :
    (castResult context position result).isOk = result.isOk := by
  cases context
  cases position
  rfl

@[simp] theorem Selected.castResult_error {Γ Δ : List Ty} {index other : Nat}
    (context : Γ = Δ) (position : index = other) (error : Error) :
    castResult context position (.error error) = .error error := by
  cases context
  cases position
  rfl

/-- Scan to the requested binding, then rebuild its typed variable from the
reversed prefix. Neither phase retains a stack frame per preceding binding. -/
def selectFrom : (Γ : List Ty) → (index : Nat) → (skipped : List Ty) →
    Except Error (Selected (skipped.reverse ++ Γ) (index + skipped.length))
  | [], _, _ => .error .scope
  | ty :: _, 0, skipped =>
      .ok ⟨ty, Var.here.weakenReversed skipped, by simp [Var.index]⟩
  | head :: Γ, index + 1, skipped =>
      Selected.castResult
        (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
        (by simp only [List.length_cons]; omega)
        (selectFrom Γ index (head :: skipped))

def selectIterative (Γ : List Ty) (index : Nat) : Except Error (Selected Γ index) :=
  selectFrom Γ index []

theorem selectFrom_isOk_iff (Γ : List Ty) (index : Nat) (skipped : List Ty) :
    (selectFrom Γ index skipped).isOk = true ↔ index < Γ.length := by
  induction Γ generalizing index skipped with
  | nil => simp [selectFrom, Except.isOk, Except.toBool]
  | cons head rest ih =>
    cases index with
    | zero => simp [selectFrom, Except.isOk, Except.toBool]
    | succ index => simpa [selectFrom] using ih index (head :: skipped)

theorem selectFrom_failure (Γ : List Ty) (index : Nat) (skipped : List Ty)
    (outside : Γ.length ≤ index) : selectFrom Γ index skipped = .error .scope := by
  induction Γ generalizing index skipped with
  | nil => rfl
  | cons head rest ih =>
    cases index with
    | zero => simp at outside
    | succ index =>
      rw [selectFrom, ih index (head :: skipped) (by simpa using outside)]
      exact Selected.castResult_error _ _ _

theorem select_isOk_iff (Γ : List Ty) (index : Nat) :
    (select Γ index).isOk = true ↔ index < Γ.length := by
  induction Γ generalizing index with
  | nil => simp [select, Except.isOk, Except.toBool]
  | cons head rest ih =>
    cases index with
    | zero => simp [select, Except.isOk, Except.toBool]
    | succ index =>
      have earlier := ih index
      cases found : select rest index with
      | error error =>
        rw [select, found]
        change false = true ↔ index + 1 < rest.length + 1
        simpa [found, Except.isOk, Except.toBool] using earlier
      | ok value =>
        rw [select, found]
        change true = true ↔ index + 1 < rest.length + 1
        simpa [found, Except.isOk, Except.toBool] using earlier

theorem select_failure (Γ : List Ty) (index : Nat) (outside : Γ.length ≤ index) :
    select Γ index = .error .scope := by
  induction Γ generalizing index with
  | nil => rfl
  | cons head rest ih =>
    cases index with
    | zero => simp at outside
    | succ index =>
      rw [select, ih index (by simpa using outside)]
      rfl

@[csimp] theorem select_eq_selectIterative : @select = @selectIterative := by
  funext Ty Γ index
  by_cases within : index < Γ.length
  · have plain := (select_isOk_iff Γ index).mpr within
    have iterative := (selectFrom_isOk_iff Γ index []).mpr within
    cases first : select Γ index with
    | error error => simp [first, Except.isOk, Except.toBool] at plain
    | ok value =>
      cases second : selectIterative Γ index with
      | error error => simp [selectIterative] at second; simp [second, Except.isOk, Except.toBool] at iterative
      | ok other => exact congrArg Except.ok (Subsingleton.elim value other)
  · rw [select_failure Γ index (by omega)]
    exact (selectFrom_failure Γ index [] (by omega)).symm

def operandIndices {Γ ports : List Ty} : Operands Γ ports → List Nat
  | .nil => []
  | .cons value rest => value.index :: operandIndices rest

def operandIndexList {Γ ports : List Ty} (values : Operands Γ ports) : List Nat :=
  values.toList Var.index

@[csimp] theorem operandIndices_eq_operandIndexList : @operandIndices = @operandIndexList := by
  funext Ty Γ ports values
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simpa only [operandIndices, operandIndexList, Values.toList] using
      congrArg (List.cons first.index) ih

theorem operandIndices_reverse {Γ ports : List Ty} (values : Operands Γ ports) :
    operandIndices values.reverse = (operandIndices values).reverse := by
  rw [operandIndices_eq_operandIndexList]
  exact Values.toList_reverse Var.index values

structure SelectedOperands (Γ : List Ty) (indices : List Nat) where
  ports : List Ty
  values : Operands Γ ports
  erasure : operandIndices values = indices

theorem operands_eq_of_indices {Γ firstTypes otherTypes : List Ty}
    (first : Operands Γ firstTypes) (other : Operands Γ otherTypes)
    (same : operandIndices first = operandIndices other) :
    firstTypes = otherTypes ∧ HEq first other := by
  induction first generalizing otherTypes with
  | nil =>
    cases other with
    | nil => exact ⟨rfl, HEq.rfl⟩
    | cons head tail => simp [operandIndices] at same
  | cons head tail ih =>
    cases other with
    | nil => simp [operandIndices] at same
    | cons otherHead otherTail =>
      have positions := List.cons.inj same
      have typeEq := head.type_eq_of_index otherHead positions.1
      cases typeEq
      obtain ⟨typesEq, valuesEq⟩ := ih otherTail positions.2
      cases typesEq
      cases eq_of_heq valuesEq
      cases head.eq_of_index otherHead positions.1
      exact ⟨rfl, HEq.rfl⟩

instance {Γ : List Ty} {indices : List Nat} : Subsingleton (SelectedOperands Γ indices) where
  allEq first other := by
    have same := first.erasure.trans other.erasure.symm
    obtain ⟨typesEq, valuesEq⟩ := operands_eq_of_indices first.values other.values same
    cases first with
    | mk firstTypes first firstEq =>
      cases other with
      | mk otherTypes other otherEq =>
        dsimp only at typesEq valuesEq
        cases typesEq
        cases eq_of_heq valuesEq
        rfl

def selectOperands (Γ : List Ty) : (indices : List Nat) →
    Except Error (SelectedOperands Γ indices)
  | [] => return ⟨[], .nil, rfl⟩
  | index :: indices => do
      let first ← select Γ index
      let rest ← selectOperands Γ indices
      return ⟨first.ty :: rest.ports, .cons first.value rest.values,
        by simp [operandIndices, first.erasure, rest.erasure]⟩

@[inline] def SelectedOperands.castResult {Γ : List Ty} {indices other : List Nat}
    (same : indices = other) (result : Except Error (SelectedOperands Γ indices)) :
    Except Error (SelectedOperands Γ other) := same ▸ result

/-- Select in authored order, storing a reversed list until the final reversal. -/
def selectOperandsFrom (Γ : List Ty) : (indices : List Nat) → {seen : List Nat} →
    SelectedOperands Γ seen → Except Error (SelectedOperands Γ (seen.reverse ++ indices))
  | [], _, seen =>
      SelectedOperands.castResult (List.append_nil _).symm
        (.ok ⟨seen.ports.reverse, seen.values.reverse,
          by rw [operandIndices_reverse, seen.erasure]⟩)
  | index :: indices, seenIndices, seen => do
      let first ← select Γ index
      SelectedOperands.castResult
        (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
        (selectOperandsFrom Γ indices (seen := index :: seenIndices)
          ⟨first.ty :: seen.ports, .cons first.value seen.values,
          by simp only [operandIndices, first.erasure, seen.erasure]⟩)

def selectOperandsIterative (Γ : List Ty) (indices : List Nat) : Except Error (SelectedOperands Γ indices) :=
  selectOperandsFrom Γ indices ⟨[], .nil, rfl⟩

private def selectionOutcome {A : Type} : Except Error A → Except Error Unit
  | .error error => .error error
  | .ok _ => .ok ()

private theorem castOperands_outcome {Γ : List Ty} {indices other : List Nat}
    (same : indices = other) (result : Except Error (SelectedOperands Γ indices)) :
    selectionOutcome (SelectedOperands.castResult same result) = selectionOutcome result := by
  cases same
  rfl

private theorem selectOperandsFrom_outcome (Γ : List Ty) (indices : List Nat)
    {seen : List Nat} (selected : SelectedOperands Γ seen) :
    selectionOutcome (selectOperandsFrom Γ indices selected) =
      selectionOutcome (selectOperands Γ indices) := by
  induction indices generalizing seen with
  | nil => rw [selectOperandsFrom, castOperands_outcome]; rfl
  | cons index indices ih =>
    cases found : select Γ index with
    | error error => simp only [selectOperandsFrom, selectOperands, found]; rfl
    | ok first =>
      simp only [selectOperandsFrom, selectOperands, found]
      change selectionOutcome (SelectedOperands.castResult _ _) = _
      rw [castOperands_outcome, ih]
      cases selectOperands Γ indices <;> rfl

@[csimp] theorem selectOperands_eq_selectOperandsIterative :
    @selectOperands = @selectOperandsIterative := by
  funext Ty Γ indices
  have same := selectOperandsFrom_outcome Γ indices ⟨[], .nil, rfl⟩
  change selectionOutcome (selectOperandsIterative Γ indices) =
    selectionOutcome (selectOperands Γ indices) at same
  cases first : selectOperands Γ indices with
  | error error =>
    rw [first] at same
    cases second : selectOperandsIterative Γ indices with
    | error other =>
      rw [second] at same
      have errorEq : other = error := Except.error.inj same
      cases errorEq
      rfl
    | ok other => rw [second] at same; cases same
  | ok value =>
    rw [first] at same
    cases second : selectOperandsIterative Γ indices with
    | error error => rw [second] at same; cases same
    | ok other => exact congrArg Except.ok (Subsingleton.elim value other)

variable {Role : Type} [DecidableEq Role] {parties : List Role} {algebra : Algebra}

def inputIndices {Γ : List (Port Role algebra.Ty)} {types : List algebra.Ty} :
    Inputs Γ types → List Nat
  | .nil => []
  | .cons value rest => value.2.index :: inputIndices rest

def inputIndexList {Γ : List (Port Role algebra.Ty)} {types : List algebra.Ty}
    (inputs : Inputs Γ types) : List Nat := inputs.toList (fun value => value.2.index)

omit [DecidableEq Role] in
@[csimp] theorem inputIndices_eq_inputIndexList : @inputIndices = @inputIndexList := by
  funext Role algebra Γ types inputs
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
    simpa only [inputIndices, inputIndexList, Values.toList] using
      congrArg (List.cons first.2.index) ih

omit [DecidableEq Role] in
theorem inputIndices_reverse {Γ : List (Port Role algebra.Ty)} {types : List algebra.Ty}
    (inputs : Inputs Γ types) : inputIndices inputs.reverse = (inputIndices inputs).reverse := by
  rw [inputIndices_eq_inputIndexList]
  exact Values.toList_reverse (fun value => value.2.index) inputs

omit [DecidableEq Role] in
theorem input_eq_of_index {Γ : List (Port Role algebra.Ty)} {type : algebra.Ty}
    (first other : Input Γ type) (same : first.2.index = other.2.index) : first = other := by
  cases first with
  | mk firstRoles first =>
    cases other with
    | mk otherRoles other =>
      have typesEq := first.type_eq_of_index other same
      have rolesEq := congrArg Port.roles typesEq
      cases rolesEq
      cases first.eq_of_index other same
      rfl

omit [DecidableEq Role] in
theorem inputs_eq_of_indices {Γ : List (Port Role algebra.Ty)} {types : List algebra.Ty}
    (first other : Inputs Γ types) (same : inputIndices first = inputIndices other) : first = other := by
  induction first with
  | nil => cases other; rfl
  | cons head rest ih =>
    cases other with
    | cons otherHead otherRest =>
      have indicesEq := List.cons.inj same
      cases input_eq_of_index head otherHead indicesEq.1
      cases ih otherRest indicesEq.2
      rfl

def toInputs {Γ ports : List (Port Role algebra.Ty)} :
    Operands Γ ports → Inputs Γ (ports.map Port.ty)
  | .nil => .nil
  | .cons value rest => .cons ⟨_, value⟩ (toInputs rest)

def toInputsMapped {Γ ports : List (Port Role algebra.Ty)} (values : Operands Γ ports) :
    Inputs Γ (ports.map Port.ty) :=
  values.mapTypes Port.ty (fun {port} value => ⟨port.roles, value⟩)

omit [DecidableEq Role] in
@[csimp] theorem toInputs_eq_toInputsMapped : @toInputs = @toInputsMapped := by
  funext Role algebra Γ ports values
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simpa only [toInputs, toInputsMapped, Values.mapTypes] using
      congrArg (Values.cons ⟨_, first⟩) ih

omit [DecidableEq Role] in
@[simp] theorem toInputs_indices {Γ ports : List (Port Role algebra.Ty)}
    (values : Operands Γ ports) : inputIndices (toInputs values) = operandIndices values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [toInputs, inputIndices, operandIndices, ih]

@[inline] def castVariable {Γ : List (Port Role algebra.Ty)} {roles : List Role} {a b : algebra.Ty}
    (same : a = b) (value : Var Γ ⟨roles, a⟩) : Var Γ ⟨roles, b⟩ := same ▸ value

omit [DecidableEq Role] in
@[simp] theorem castVariable_index {Γ : List (Port Role algebra.Ty)}
    {roles : List Role} {a b : algebra.Ty} (same : a = b) (value : Var Γ ⟨roles, a⟩) :
    (castVariable same value).index = value.index := by cases same; rfl

def selectInputs [DecidableEq algebra.Ty] (Γ : List (Port Role algebra.Ty)) :
    (types : List algebra.Ty) → (indices : List Nat) →
      Except Error { inputs : Inputs Γ types // inputIndices inputs = indices }
  | [], [] => return ⟨.nil, rfl⟩
  | ty :: types, index :: indices => do
      let selected ← select Γ index
      if same : selected.ty.ty = ty then
        let value : Input Γ ty := ⟨selected.ty.roles, castVariable same selected.value⟩
        have indexEq : value.2.index = index := by
          simpa [value] using selected.erasure
        let rest ← selectInputs Γ types indices
        return ⟨.cons value rest.val, by simp [inputIndices, indexEq, rest.property]⟩
      else throw .type
  | _, _ => throw .arity

@[inline] def castInputResult {Γ : List (Port Role algebra.Ty)}
    {types otherTypes : List algebra.Ty} {indices otherIndices : List Nat}
    (typesEq : types = otherTypes) (indicesEq : indices = otherIndices)
    (result : Except Error { inputs : Inputs Γ types // inputIndices inputs = indices }) :
    Except Error { inputs : Inputs Γ otherTypes // inputIndices inputs = otherIndices } :=
  typesEq ▸ indicesEq ▸ result

def selectInputsFrom [DecidableEq algebra.Ty] (Γ : List (Port Role algebra.Ty)) :
    (types : List algebra.Ty) → (indices : List Nat) →
    {seenTypes : List algebra.Ty} → {seenIndices : List Nat} →
    { inputs : Inputs Γ seenTypes // inputIndices inputs = seenIndices } →
      Except Error { inputs : Inputs Γ (seenTypes.reverse ++ types) //
        inputIndices inputs = seenIndices.reverse ++ indices }
  | [], [], _, _, seen =>
      castInputResult (List.append_nil _).symm (List.append_nil _).symm
        (.ok ⟨seen.val.reverse, by rw [inputIndices_reverse, seen.property]⟩)
  | ty :: types, index :: indices, seenTypes, seenIndices, seen => do
      let selected ← select Γ index
      if same : selected.ty.ty = ty then
        let value : Input Γ ty := ⟨selected.ty.roles, castVariable same selected.value⟩
        have indexEq : value.2.index = index := by simpa [value] using selected.erasure
        castInputResult
          (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
          (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
          (selectInputsFrom Γ types indices (seenTypes := ty :: seenTypes)
            (seenIndices := index :: seenIndices)
            ⟨.cons value seen.val, by simp only [inputIndices, indexEq, seen.property]⟩)
      else throw .type
  | _, _, _, _, _ => throw .arity

def selectInputsIterative [DecidableEq algebra.Ty] (Γ : List (Port Role algebra.Ty))
    (types : List algebra.Ty) (indices : List Nat) :
    Except Error { inputs : Inputs Γ types // inputIndices inputs = indices } :=
  selectInputsFrom Γ types indices ⟨.nil, rfl⟩

omit [DecidableEq Role] in
private theorem castInputs_outcome {Γ : List (Port Role algebra.Ty)}
    {types otherTypes : List algebra.Ty} {indices otherIndices : List Nat}
    (typesEq : types = otherTypes) (indicesEq : indices = otherIndices)
    (result : Except Error { inputs : Inputs Γ types // inputIndices inputs = indices }) :
    selectionOutcome (castInputResult typesEq indicesEq result) = selectionOutcome result := by
  cases typesEq
  cases indicesEq
  rfl

omit [DecidableEq Role] in
private theorem selectInputsFrom_outcome [DecidableEq algebra.Ty]
    (Γ : List (Port Role algebra.Ty)) (types : List algebra.Ty) (indices : List Nat)
    {seenTypes : List algebra.Ty} {seenIndices : List Nat}
    (seen : { inputs : Inputs Γ seenTypes // inputIndices inputs = seenIndices }) :
    selectionOutcome (selectInputsFrom Γ types indices seen) =
      selectionOutcome (selectInputs Γ types indices) := by
  induction types generalizing indices seenTypes seenIndices with
  | nil =>
    cases indices with
    | nil => rw [selectInputsFrom, castInputs_outcome]; rfl
    | cons _ _ => rfl
  | cons ty types ih =>
    cases indices with
    | nil => rfl
    | cons index indices =>
      cases found : select Γ index with
      | error error => simp only [selectInputsFrom, selectInputs, found]; rfl
      | ok selected =>
        simp only [selectInputsFrom, selectInputs, found]
        dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure]
        by_cases same : selected.ty.ty = ty
        · simp only [same, dite_true]
          change selectionOutcome (castInputResult _ _ _) = _
          rw [castInputs_outcome, ih]
          cases selectInputs Γ types indices <;> rfl
        · simp only [same, dite_false]
          rfl

@[csimp] theorem selectInputs_eq_selectInputsIterative : @selectInputs = @selectInputsIterative := by
  funext Role algebra inst Γ types indices
  have same := selectInputsFrom_outcome Γ types indices ⟨.nil, rfl⟩
  change selectionOutcome (selectInputsIterative Γ types indices) =
    selectionOutcome (selectInputs Γ types indices) at same
  cases first : selectInputs Γ types indices with
  | error error =>
    rw [first] at same
    cases second : selectInputsIterative Γ types indices with
    | error other =>
      rw [second] at same
      have errorEq : other = error := Except.error.inj same
      cases errorEq
      rfl
    | ok other => rw [second] at same; cases same
  | ok value =>
    cases second : selectInputsIterative Γ types indices with
    | error error => rw [first, second] at same; cases same
    | ok other =>
      congr 1
      apply Subtype.ext
      exact inputs_eq_of_indices value.val other.val (value.property.trans other.property.symm)

def Region.erase {Γ ports} : Region parties algebra Γ ports → Raw algebra.Op algebra.Count
  | .outputs values => .outputs (operandIndices values)
  | .operation op args _ next => .operation op (inputIndices args) next.erase
  | .tuple args _ next => .tuple (inputIndices args) next.erase
  | .project value component next => .project value.2.index component.index next.erase
  | .map count captures body next =>
      .map count (operandIndices captures) body.erase next.erase
  | .fold count initial captures body next =>
      .fold count (operandIndices initial) (operandIndices captures) body.erase next.erase

def Prefix.erase {Γ Δ} (frames : Prefix parties algebra Γ Δ)
    (tail : Raw algebra.Op algebra.Count) : Raw algebra.Op algebra.Count :=
  match frames with
  | .nil => tail
  | .operation previous op args _ => previous.erase (.operation op (inputIndices args) tail)
  | .tuple previous args _ => previous.erase (.tuple (inputIndices args) tail)
  | .project previous value component => previous.erase (.project value.2.index component.index tail)
  | .map previous count capture body => previous.erase (.map count (operandIndices capture) body.erase tail)
  | .fold previous count initial capture body =>
      previous.erase (.fold count (operandIndices initial) (operandIndices capture) body.erase tail)

theorem Prefix.erase_nil {Γ} (raw : Raw algebra.Op algebra.Count) :
    (Prefix.nil : Prefix parties algebra Γ Γ).erase raw = raw := rfl

theorem Prefix.close_erase {Γ Δ ports} (frames : Prefix parties algebra Γ Δ)
    (tail : Region parties algebra Δ ports) : (frames.close tail).erase = frames.erase tail.erase := by
  induction frames generalizing ports with
  | nil => rfl
  | operation previous op args available ih => exact ih (.operation op args available tail)
  | tuple previous args available ih => exact ih (.tuple args available tail)
  | project previous value component ih => exact ih (.project value component tail)
  | map previous count capture body ih => exact ih (.map count capture body tail)
  | fold previous count initial capture body ih => exact ih (.fold count initial capture body tail)

structure Decoded (parties : List Role) (algebra : Algebra)
    (Γ : List (Port Role algebra.Ty)) (raw : Raw algebra.Op algebra.Count) where
  ports : List (Port Role algebra.Ty)
  region : Region parties algebra Γ ports
  erasure : region.erase = raw

def Decoded.requirePorts [DecidableEq algebra.Ty] {Γ raw}
    (decoded : Decoded parties algebra Γ raw) (ports : List (Port Role algebra.Ty)) :
    Except Error { region : Region parties algebra Γ ports // region.erase = raw } :=
  if same : decoded.ports = ports then
    .ok ⟨same ▸ decoded.region, by cases same; exact decoded.erasure⟩
  else .error .invariant

abbrev Capacity (algebra : Algebra) :=
  TypeCapacity algebra.Ty algebra.Count algebra.product algebra.vector

/-- Installed resolvers can retain exact signature counters. A missing entry
uses ordinary bounded measurement. The callback's cost belongs to its owner. -/
abbrev SignatureMeasurements (capacity : Capacity algebra) :=
  (operation : algebra.Op) → Option
    (capacity.SignatureMeasurement (algebra.arguments operation) (algebra.result operation))

abbrev MeasuredPorts (capacity : Capacity algebra) (ports : List (Port Role algebra.Ty)) :=
  Values (fun port => capacity.Measured port.ty) ports

def measurePorts (capacity : Capacity algebra) (ports : List (Port Role algebra.Ty)) :
    Option (MeasuredPorts capacity ports) :=
  Values.ofList? (fun port => capacity.measure port.ty) ports

def appendMeasured {capacity : Capacity algebra} {Γ Δ : List (Port Role algebra.Ty)}
    (first : MeasuredPorts capacity Γ) (rest : MeasuredPorts capacity Δ) :
    MeasuredPorts capacity (Γ ++ Δ) :=
  first.append rest

def measuredTypes {capacity : Capacity algebra} {ports : List (Port Role algebra.Ty)} :
    MeasuredPorts capacity ports → Values capacity.Measured (ports.map Port.ty) :=
  Values.mapTypes Port.ty (fun value => value)

def measureVectors (capacity : Capacity algebra) (count : algebra.Count)
    {ports : List (Port Role algebra.Ty)} (measured : MeasuredPorts capacity ports) :
    Option (MeasuredPorts capacity (vectorPorts count ports)) :=
  match measured with
  | .nil => some .nil
  | .cons first rest => do
      let first ← capacity.measureVector first count
      let rest ← measureVectors capacity count rest
      return .cons first rest

def measureVectorsMapped (capacity : Capacity algebra) (count : algebra.Count)
    {ports : List (Port Role algebra.Ty)} (measured : MeasuredPorts capacity ports) :
    Option (MeasuredPorts capacity (vectorPorts count ports)) :=
  Values.mapTypesOption
    (Value := fun port : Port Role algebra.Ty => capacity.Measured port.ty)
    (Other := fun port : Port Role algebra.Ty => capacity.Measured port.ty)
    (fun port : Port Role algebra.Ty => ⟨port.roles, algebra.vector port.ty count⟩)
    (fun value => capacity.measureVector value count) measured

omit [DecidableEq Role] in
@[csimp] theorem measureVectors_eq_measureVectorsMapped : @measureVectors = @measureVectorsMapped := by
  funext Role algebra capacity count ports measured
  induction measured with
  | nil => rfl
  | cons first rest ih =>
    simp only [measureVectors, measureVectorsMapped, Values.mapTypesOption]
    rw [ih]
    rfl

structure MeasuredDecoded (parties : List Role) (algebra : Algebra)
    (capacity : Capacity algebra) (Γ : List (Port Role algebra.Ty)) (raw : Raw algebra.Op algebra.Count)
    extends Decoded parties algebra Γ raw where
  measured : MeasuredPorts capacity ports

def Prefix.closeMeasured {capacity : Capacity algebra} {Γ Δ raw original}
    (frames : Prefix parties algebra Γ Δ) (decoded : MeasuredDecoded parties algebra capacity Δ raw)
    (same : frames.erase raw = original) : MeasuredDecoded parties algebra capacity Γ original :=
  ⟨⟨decoded.ports, frames.close decoded.region,
    by rw [frames.close_erase, decoded.erasure]; exact same⟩, decoded.measured⟩

theorem Prefix.closeMeasured_nil_map {capacity : Capacity algebra} {Γ raw}
    (result : Except Error (MeasuredDecoded parties algebra capacity Γ raw)) :
    result.map (fun decoded => Prefix.nil.closeMeasured decoded (original := raw) rfl) = result := by
  cases result <;> rfl

/-- The context carries cached structural measurements. Introduced types are
bounded before comparison or insertion. A lawful view authorizes projection
without comparing the operand to its reconstructed product. Signatures reuse
retained root measurements when supplied, with bounded walks as a fallback.
Constructed products retain child certificates, while a boundary
product measures only the selected child after its index is checked. Product/vector formation combines
cached sizes. The allowance is
nesting depth plus one; nested regions spend two levels and siblings retain it. -/
def decodeMeasured [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool)
    (fuel : Nat) (Γ : List (Port Role algebra.Ty)) (measured : MeasuredPorts capacity Γ)
    (raw : Raw algebra.Op algebra.Count) (signatures : SignatureMeasurements capacity := fun _ => none) :
    Except Error (MeasuredDecoded parties algebra capacity Γ raw) :=
  match fuel with
  | 0 => throw .depth
  | fuel + 1 => do
      match hraw : raw with
      | .outputs indices =>
          let selected ← selectOperands Γ indices
          return ⟨⟨selected.ports, .outputs selected.values,
            by simp [Region.erase, selected.erasure, hraw]⟩,
            Operands.eval (fun v => measured.get v) selected.values⟩
      | .operation op indices next =>
          let resultType := algebra.result op
          let some result := capacity.measureSignatureResult (algebra.arguments op) resultType (signatures op)
            | throw .resource
          let args ← selectInputs Γ (algebra.arguments op) indices
          let tail ← decodeMeasured parties capacity countValid (fuel + 1)
            (⟨Inputs.available parties args.val, resultType⟩ :: Γ) (.cons result measured) next signatures
          return ⟨⟨tail.ports, .operation op args.val rfl tail.region,
            by simp [Region.erase, args.property, tail.erasure, hraw]⟩, tail.measured⟩
      | .tuple indices next =>
          let args ← selectOperands Γ indices
          let inputs := toInputs args.values
          let sizes := Operands.eval (fun v => measured.get v) args.values
          let some result := capacity.measureProduct (measuredTypes sizes) | throw .resource
          let tail ← decodeMeasured parties capacity countValid (fuel + 1)
            (⟨Inputs.available parties inputs, algebra.product (args.ports.map Port.ty)⟩ :: Γ)
            (.cons result measured) next signatures
          return ⟨⟨tail.ports, .tuple inputs rfl tail.region,
            by simp [Region.erase, inputs, args.erasure, tail.erasure, hraw]⟩, tail.measured⟩
      | .project index component next =>
          let selected ← select Γ index
          match capacity.view (measured.get selected.value) with
          | none => throw .product
          | some product =>
            let value : Input Γ (algebra.product product.types) :=
              ⟨selected.ty.roles, castVariable product.sound selected.value⟩
            have indexEq : value.2.index = index := by
              simpa [value] using selected.erasure
            let part ← select product.types component
            let result := product.child part.value
            let tail ← decodeMeasured parties capacity countValid (fuel + 1)
              (⟨value.1, part.ty⟩ :: Γ) (.cons result measured) next signatures
            return ⟨⟨tail.ports, .project value part.value tail.region,
              by simp [Region.erase, indexEq, part.erasure, tail.erasure, hraw]⟩, tail.measured⟩
      | .map count indices body next =>
          if !countValid count then throw .count
          let some index := capacity.measure (algebra.index count) | throw .resource
          let capture ← selectOperands Γ indices
          let captured := Operands.eval (fun v => measured.get v) capture.values
          let nested ← decodeMeasured parties capacity countValid (fuel - 1)
            (⟨parties, algebra.index count⟩ :: capture.ports) (.cons index captured) body signatures
          let some vectors := measureVectors capacity count nested.measured | throw .resource
          let tail ← decodeMeasured parties capacity countValid (fuel + 1)
            (vectorPorts count nested.ports ++ Γ) (appendMeasured vectors measured) next signatures
          return ⟨⟨tail.ports, .map count capture.values nested.region tail.region,
            by simp [Region.erase, capture.erasure, nested.erasure, tail.erasure, hraw]⟩, tail.measured⟩
      | .fold count initial indices body next =>
          if !countValid count then throw .count
          let some index := capacity.measure (algebra.index count) | throw .resource
          let carried ← selectOperands Γ initial
          let carriedSizes := Operands.eval (fun v => measured.get v) carried.values
          let capture ← selectOperands Γ indices
          let captured := Operands.eval (fun v => measured.get v) capture.values
          let nested ← decodeMeasured parties capacity countValid (fuel - 1)
            (⟨parties, algebra.index count⟩ :: (carried.ports ++ capture.ports))
            (.cons index (appendMeasured carriedSizes captured)) body signatures
          let checked ← nested.toDecoded.requirePorts carried.ports
          let tail ← decodeMeasured parties capacity countValid (fuel + 1)
            (carried.ports ++ Γ) (appendMeasured carriedSizes measured) next signatures
          return ⟨⟨tail.ports, .fold count carried.values capture.values checked.val tail.region,
            by simp [Region.erase, carried.erasure, capture.erasure, checked.property,
              tail.erasure, hraw]⟩, tail.measured⟩
  termination_by structural raw

/-- Construct flat spines with explicit checked frames. Nested bodies start
with an empty prefix. Only genuine nesting retains a recursive call frame. -/
def decodePrefix [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool) (fuel : Nat)
    {originalContext : List (Port Role algebra.Ty)} {original : Raw algebra.Op algebra.Count}
    (Γ : List (Port Role algebra.Ty)) (measured : MeasuredPorts capacity Γ)
    (raw : Raw algebra.Op algebra.Count) (frames : Prefix parties algebra originalContext Γ)
    (same : frames.erase raw = original) (signatures : SignatureMeasurements capacity) :
    Except Error (MeasuredDecoded parties algebra capacity originalContext original) :=
  match fuel with
  | 0 => throw .depth
  | fuel + 1 => do
      match hraw : raw with
      | .outputs indices =>
          let selected ← selectOperands Γ indices
          let decoded : MeasuredDecoded parties algebra capacity Γ (.outputs indices) :=
            ⟨⟨selected.ports, .outputs selected.values,
              by simp only [Region.erase, selected.erasure]⟩,
              Operands.eval (fun v => measured.get v) selected.values⟩
          return frames.closeMeasured decoded (by simpa only [hraw] using same)
      | .operation op indices next =>
          let resultType := algebra.result op
          let some result := capacity.measureSignatureResult (algebra.arguments op) resultType (signatures op)
            | throw .resource
          let args ← selectInputs Γ (algebra.arguments op) indices
          decodePrefix parties capacity countValid (fuel + 1)
            (⟨Inputs.available parties args.val, resultType⟩ :: Γ) (.cons result measured) next
            (.operation frames op args.val rfl)
            (by simpa only [Prefix.erase, args.property, hraw] using same) signatures
      | .tuple indices next =>
          let args ← selectOperands Γ indices
          let inputs := toInputs args.values
          let sizes := Operands.eval (fun v => measured.get v) args.values
          let some result := capacity.measureProduct (measuredTypes sizes) | throw .resource
          decodePrefix parties capacity countValid (fuel + 1)
            (⟨Inputs.available parties inputs, algebra.product (args.ports.map Port.ty)⟩ :: Γ)
            (.cons result measured) next (.tuple frames inputs rfl)
            (by simpa only [Prefix.erase, inputs, toInputs_indices, args.erasure, hraw] using same) signatures
      | .project index component next =>
          let selected ← select Γ index
          match capacity.view (measured.get selected.value) with
          | none => throw .product
          | some product =>
            let value : Input Γ (algebra.product product.types) :=
              ⟨selected.ty.roles, castVariable product.sound selected.value⟩
            have indexEq : value.2.index = index := by simpa [value] using selected.erasure
            let part ← select product.types component
            let result := product.child part.value
            decodePrefix parties capacity countValid (fuel + 1)
              (⟨value.1, part.ty⟩ :: Γ) (.cons result measured) next (.project frames value part.value)
              (by simpa only [Prefix.erase, indexEq, part.erasure, hraw] using same) signatures
      | .map count indices body next =>
          if !countValid count then throw .count
          let some index := capacity.measure (algebra.index count) | throw .resource
          let capture ← selectOperands Γ indices
          let captured := Operands.eval (fun v => measured.get v) capture.values
          let nested ← decodePrefix parties capacity countValid (fuel - 1) (original := body)
            (⟨parties, algebra.index count⟩ :: capture.ports) (.cons index captured)
            body .nil (Prefix.erase_nil body) signatures
          let some vectors := measureVectors capacity count nested.measured | throw .resource
          decodePrefix parties capacity countValid (fuel + 1)
            (vectorPorts count nested.ports ++ Γ) (appendMeasured vectors measured) next
            (.map frames count capture.values nested.region)
            (by simpa only [Prefix.erase, capture.erasure, nested.erasure, hraw] using same) signatures
      | .fold count initial indices body next =>
          if !countValid count then throw .count
          let some index := capacity.measure (algebra.index count) | throw .resource
          let carried ← selectOperands Γ initial
          let carriedSizes := Operands.eval (fun v => measured.get v) carried.values
          let capture ← selectOperands Γ indices
          let captured := Operands.eval (fun v => measured.get v) capture.values
          let nested ← decodePrefix parties capacity countValid (fuel - 1) (original := body)
            (⟨parties, algebra.index count⟩ :: (carried.ports ++ capture.ports))
            (.cons index (appendMeasured carriedSizes captured)) body .nil (Prefix.erase_nil body) signatures
          let checked ← nested.toDecoded.requirePorts carried.ports
          decodePrefix parties capacity countValid (fuel + 1)
            (carried.ports ++ Γ) (appendMeasured carriedSizes measured) next
            (.fold frames count carried.values capture.values checked.val)
            (by simpa only [Prefix.erase, carried.erasure, capture.erasure, checked.property, hraw]
                using same) signatures
  termination_by structural raw

theorem decodePrefix_eq [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool) (fuel : Nat)
    {originalContext : List (Port Role algebra.Ty)} {original : Raw algebra.Op algebra.Count}
    (Γ : List (Port Role algebra.Ty)) (measured : MeasuredPorts capacity Γ)
    (raw : Raw algebra.Op algebra.Count) (frames : Prefix parties algebra originalContext Γ)
    (same : frames.erase raw = original) (signatures : SignatureMeasurements capacity) :
    decodePrefix parties capacity countValid fuel Γ measured raw frames same signatures =
      (decodeMeasured parties capacity countValid fuel Γ measured raw signatures).map
        (fun decoded => frames.closeMeasured decoded same) := by
  induction raw generalizing Γ fuel originalContext original with
  | outputs indices =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [decodePrefix, decodeMeasured]
          cases selectOperands Γ indices <;> rfl
  | operation op indices next ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [decodePrefix, decodeMeasured]
          simp only [ih, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          repeat' first | rfl | split
  | tuple indices next ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [decodePrefix, decodeMeasured]
          simp only [ih, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          repeat' first | rfl | split
  | project index component next ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [decodePrefix, decodeMeasured]
          simp only [ih, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          repeat' first | rfl | split
  | map count indices body next bodyIH ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [decodePrefix, decodeMeasured]
          simp only [bodyIH, ih, Prefix.closeMeasured_nil_map]
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          repeat' first | rfl | split
  | fold count initial indices body next bodyIH ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [decodePrefix, decodeMeasured]
          simp only [bodyIH, ih, Prefix.closeMeasured_nil_map]
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
          repeat' first | rfl | split

def decodeMeasuredIterative [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool)
    (fuel : Nat) (Γ : List (Port Role algebra.Ty)) (measured : MeasuredPorts capacity Γ)
    (raw : Raw algebra.Op algebra.Count) (signatures : SignatureMeasurements capacity) :
    Except Error (MeasuredDecoded parties algebra capacity Γ raw) :=
  decodePrefix parties capacity countValid fuel Γ measured raw .nil rfl signatures

@[csimp] theorem decodeMeasured_eq_decodeMeasuredIterative :
    @decodeMeasured = @decodeMeasuredIterative := by
  funext Role roleEq algebra typeEq parties capacity countValid fuel Γ measured raw signatures
  symm
  apply (decodePrefix_eq parties capacity countValid fuel Γ measured raw .nil rfl signatures).trans
  cases decodeMeasured parties capacity countValid fuel Γ measured raw signatures <;> rfl

/-- Measure external context types once; recursive formation propagates their
certificates and returns the same intrinsic graph and exact erasure evidence. -/
def decode [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool)
    (fuel : Nat) (Γ : List (Port Role algebra.Ty)) (raw : Raw algebra.Op algebra.Count)
    (signatures : SignatureMeasurements capacity := fun _ => none) :
    Except Error (Decoded parties algebra Γ raw) := do
  if fuel == 0 then throw .depth
  let some measured := measurePorts capacity Γ | throw .resource
  let decoded ← decodeMeasured parties capacity countValid fuel Γ measured raw signatures
  return decoded.toDecoded

theorem decode_erases [DecidableEq algebra.Ty] (parties : List Role)
    (capacity : Capacity algebra) (countValid : algebra.Count → Bool)
    {signatures : SignatureMeasurements capacity} {fuel Γ raw result}
    (_accepted : decode parties capacity countValid fuel Γ raw signatures = .ok result) : result.region.erase = raw :=
  result.erasure

end Zkc.Source.Mathematical.Graph
