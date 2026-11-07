module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! The checked field-vector read emitted by the clear oracle realization.
The row guard precedes collection access. Both use the existing operation
semantics, retaining finite-index ingress and refusal on malformed storage.
The theorem is independent of any protocol, field implementation or caller frame.
-/

set_option autoImplicit false
namespace Zkc.Realization.TableRead
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Placement where
  start : Nat
  data : Nat
  rows : Nat
  position : Nat
  site : String

def instructions (domain : String) (placement : Placement) : List Construction.Instruction :=
  [⟨.execute .indexLess, [placement.position, placement.rows], [.data .boolean], []⟩,
   ⟨.require placement.site, [placement.start], [], []⟩,
   ⟨.calculate (.boundedAt domain), [placement.data, placement.position], [.data (.field domain)], []⟩]

structure Recognized (body : List Construction.Instruction) where
  domain : String
  placement : Placement
  exactBody : body = instructions domain placement

/-- The guard and read must use the same position. Recognition includes all
result sorts, operand order and the actual comparison-result slot. -/
def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let [comparison, guard, read] := body | none
  let [position, rows] := comparison.operands | none
  let .require site := guard.operation | none
  let [start] := guard.operands | none
  let .calculate (.boundedAt domain) := read.operation | none
  let [data, _] := read.operands | none
  let placement : Placement := ⟨start, data, rows, position, site⟩
  if matched : body = instructions domain placement then some ⟨domain, placement, matched⟩ else none

/-- The surrounding instruction traversal supplies the real SSA offset.
Recognition alone describes a relative placement; it does not certify the caller frame. -/
def recognizeAt (start : Nat) (body : List Construction.Instruction) : Option (Recognized body) := do
  let checked ← recognize body
  if checked.placement.start = start then some checked else none

def spine (domain : String) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model .indexLess
    [placement.position, placement.rows] [.data .boolean])
  (.step (fun _ ↦ Domain.View.require placement.start [])
  (.step (fun model ↦ Domain.View.calculation model (.boundedAt domain)
    [placement.data, placement.position] [.data (.field domain)]) .empty))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (domain : String) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions domain placement) ((spine domain placement).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.require _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
        Domain.Correspondence.empty))

theorem Recognized.correspondence {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      body ((spine checked.domain checked.placement).block model) := by
  rcases checked with ⟨domain, placement, rfl⟩
  exact TableRead.correspondence model program context domain placement

/-- The closed read is the existing checked comparison and bounded collection
operation. No source-level success or preselected answer is assumed. -/
def read (model : DomainModel) (domain : String) (cells : List (model.Field domain))
    (rows position : Nat) : Closed (model.Field domain) :=
  (primitiveOutcome (Primitive.indexLess.evaluateOn model.toFieldModel
    (.cons position (.cons rows .nil)))).bind fun within ↦
    if within.get .here then
      (ConnectionCalculations.closedCalculation model (.boundedAt domain)
        (.cons cells (.cons position .nil))).bind (fun answer ↦ .done (answer.get .here))
    else .halt .refused

/-- The complete result, including every refusal, is determined by the actual
row bound and stored word. This also covers inconsistent physical lengths. -/
theorem read_eq (model : DomainModel) (domain : String) (cells : List (model.Field domain))
    (rows position : Nat) : read model domain cells rows position =
    if position < indexLimit ∧ rows < indexLimit ∧ position < rows then
      match cells[position]? with
      | some value => .done value
      | none => .halt .refused
    else .halt .refused := by
  by_cases bounds : position < indexLimit ∧ rows < indexLimit
  · by_cases inside : position < rows
    · simp only [read, Primitive.evaluateOn, checkedIndices, bounds, ↓reduceIte,
        primitiveOutcome, PIR.Process.bind, inside, decide_true, and_self]
      change ((match cells[position]? with
        | some value => PIR.Process.done (.cons value .nil : Values model.Value [.field domain])
        | none => PIR.Process.halt .refused).bind (fun answer ↦ .done (answer.get .here))) = _
      cases cells[position]? <;> rfl
    · simp only [read, Primitive.evaluateOn, checkedIndices, bounds, inside, ↓reduceIte,
        primitiveOutcome, decide_false, and_false]
      rfl
  · have invalid : ¬ (position < indexLimit ∧ rows < indexLimit ∧ position < rows) :=
      fun all ↦ bounds ⟨all.1, all.2.1⟩
    simp [read, Primitive.evaluateOn, checkedIndices, bounds, invalid, primitiveOutcome,
      PIR.Process.bind]

set_option backward.isDefEq.respectTransparency false in
/-- The actual three-instruction block simulates that closed read, retaining
all checkpoints and the caller's complete frame. There is no in-range premise. -/
noncomputable def simulation (model : DomainModel) (domain : String)
    (environment : Domain.Environment model.toCarriers) (data rowsSlot positionSlot : Nat)
    (site : String) (cells : List (model.Field domain)) (rows position : Nat)
    (readData : environment[data]? = some (.data ⟨.vector domain, rfl, cells⟩))
    (readRows : environment[rowsSlot]? = some (.data (.index rows)))
    (readPosition : environment[positionSlot]? = some (.data (.index position))) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((read model domain cells rows position).interpret
        (closedLift (I := Domain.effects model.toCarriers))).bind
          (fun value ↦ .done (environment ++ [.data (.boolean true),
            .data ⟨.field domain, rfl, value⟩])))
      ((spine domain ⟨environment.length, data, rowsSlot, positionSlot, site⟩).block model environment) := by
  have comparisonRead : Domain.read environment [positionSlot, rowsSlot] =
      Domain.encodeValues (tys := [.index, .index]) (.cons position (.cons rows .nil)) := by
    simp [Domain.read, readPosition, readRows, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle]
  have comparison : Domain.View.execute model .indexLess
      [positionSlot, rowsSlot] [.data .boolean] environment =
      if position < indexLimit ∧ rows < indexLimit then
        .done (environment ++ [.data (.boolean (decide (position < rows)))])
      else .halt .refused := by
    have law := ConnectionPrimitives.view_execute model .indexLess
      (.cons position (.cons rows .nil)) rfl rfl environment _ comparisonRead
    by_cases bounds : position < indexLimit ∧ rows < indexLimit <;>
      simpa [Primitive.results, Primitive.evaluateOn, checkedIndices, bounds,
        primitiveOutcome, PIR.Process.bind, Original.encodeHelperResult,
        Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
        Domain.Payload.ofValue, Ty.isHandle] using law
  let yes : Domain.Value model.toCarriers := .data (.boolean true)
  have collectionRead : Domain.read (environment ++ [yes]) [data, positionSlot] =
      Domain.encodeValues (tys := [.vector domain, .index]) (.cons cells (.cons position .nil)) := by
    simp [Domain.read, Original.read_append readData [yes], Original.read_append readPosition [yes],
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle]
  have collection : Domain.View.calculation model (.boundedAt domain)
      [data, positionSlot] [.data (.field domain)] (environment ++ [yes]) =
      match cells[position]? with
      | some value => .done (environment ++ [yes, .data ⟨.field domain, rfl, value⟩])
      | none => .halt .refused := by
    have law := ConnectionCalculations.view_calculation model (.boundedAt domain)
      (.cons cells (.cons position .nil)) rfl rfl (environment ++ [yes]) _ collectionRead
    change Domain.View.calculation _ _ _ _ _ =
      ((match cells[position]? with
        | some value => PIR.Process.done (.cons value .nil : Values model.Value [.field domain])
        | none => PIR.Process.halt .refused).interpret _).bind _ at law
    cases found : cells[position]? <;>
      simpa [found, Calculation.op, Op.results, PIR.Process.interpret, PIR.Process.bind, Original.encodeHelperResult,
        Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
        Domain.Payload.ofValue, Ty.isHandle, List.append_assoc] using law
  rw [read_eq]
  dsimp only [spine, ConnectionTargetPrefix.Prefix.block, ConnectionTargetPrefix.Prefix.plug]
  by_cases bounds : position < indexLimit ∧ rows < indexLimit
  · simp only [bounds] at comparison
    by_cases inside : position < rows
    · simp only [inside, decide_true] at comparison
      simp only [bounds.1, bounds.2, inside, and_self, ↓reduceIte]
      have guardStep : Domain.View.require environment.length [] (environment ++ [yes]) =
          .done (environment ++ [yes]) := by simp [Domain.View.require, yes]
      cases found : cells[position]? with
      | none =>
        simp only [found] at collection
        simp only [PIR.Process.interpret, PIR.Process.bind]
        rw [Domain.View.sequence_return _ _ _ _ comparison]
        refine .checkpoint _ (List.prefix_refl _) (.checkpoint _ (by simp) ?_)
        rw [Domain.View.sequence_return _ _ _ _ guardStep]
        refine .checkpoint _ (by simp) (.checkpoint _ (by simp) ?_)
        simp only [Domain.View.sequence, collection, PIR.Process.bind]
        exact .checkpoint _ (by simp) (.halt .refused)
      | some value =>
        simp only [found] at collection
        simp only [PIR.Process.interpret, PIR.Process.bind]
        apply RecordAllocator.silent_sequence comparison (List.prefix_refl _) (by simp)
        apply RecordAllocator.silent_sequence guardStep (by simp) (by simp)
        apply RecordAllocator.silent_sequence collection (by simp) (by simp)
        exact .done rfl
    · simp only [inside, decide_false] at comparison
      simp only [inside, and_false, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
      rw [Domain.View.sequence_return _ _ _ _ comparison]
      refine .checkpoint _ (List.prefix_refl _) (.checkpoint _ (by simp) ?_)
      have guardStep : Domain.View.require environment.length []
          (environment ++ [.data (.boolean false)]) = .halt .refused := by
        simp [Domain.View.require]
      simp only [Domain.View.sequence, guardStep, PIR.Process.bind]
      exact .checkpoint _ (by simp) (.halt .refused)
  · simp only [bounds, ↓reduceIte] at comparison
    have invalid : ¬ (position < indexLimit ∧ rows < indexLimit ∧ position < rows) :=
      fun all ↦ bounds ⟨all.1, all.2.1⟩
    simp only [invalid, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
    simp only [Domain.View.sequence, comparison, PIR.Process.bind]
    exact .checkpoint _ (List.prefix_refl _) (.halt .refused)

/-- Specialize the common read proof to a fragment recognized in the actual
participant. The caller supplies reached values, never an alternate reader. -/
noncomputable def Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context)
    (environment : Domain.Environment model.toCarriers)
    (cells : List (model.Field checked.domain)) (rows position : Nat)
    (start : checked.placement.start = environment.length)
    (readData : environment[checked.placement.data]? =
      some (.data ⟨.vector checked.domain, rfl, cells⟩))
    (readRows : environment[checked.placement.rows]? = some (.data (.index rows)))
    (readPosition : environment[checked.placement.position]? = some (.data (.index position))) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((read model checked.domain cells rows position).interpret
        (closedLift (I := Domain.effects model.toCarriers))).bind
          (fun value ↦ .done (environment ++ [.data (.boolean true),
            .data ⟨.field checked.domain, rfl, value⟩])))
      (Domain.evaluate model program context body environment) := by
  rw [checked.correspondence model program context]
  rcases checked with ⟨domain, ⟨offset, data, rowsSlot, positionSlot, site⟩, matched⟩
  dsimp only at start ⊢
  subst offset
  exact TableRead.simulation model domain environment data rowsSlot positionSlot site
    cells rows position readData readRows readPosition

end Zkc.Realization.TableRead
