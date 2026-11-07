module

public import Zkc.Realization.RecordAllocator
public import Zkc.Construction.ConnectionClosedSimulation
public import Zkc.Construction.ConnectionLocalRange

@[expose] public section

/-! The actual phase comparison and complete conditional yield at the end of
a generated controller iteration. The comparison uses checked indices. Its
Boolean and state projection are derived from the emitted operands together. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryPhaseYield
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def instructions (start phase threshold : Nat) : List Construction.Instruction :=
  [⟨.execute (.indexConstant threshold), [], [.data .index], []⟩,
   ⟨.execute .indexLess, [phase, start], [.data .boolean], []⟩]

def spine (start phase threshold : Nat) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.indexConstant threshold) [] [.data .index])
    (.step (fun model ↦ Domain.View.execute model .indexLess [phase, start] [.data .boolean]) .empty)

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (start phase threshold : Nat) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions start phase threshold) ((spine start phase threshold).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _) Domain.Correspondence.empty)

structure Recognized (body : List Construction.Instruction) (yielded : List Nat) where
  start : Nat
  phase : Nat
  threshold : Nat
  state : List Nat
  exactBody : body = instructions start phase threshold
  exactYield : yielded = (start + 1) :: state
  phaseField : state[6]? = some phase

/-- The yielded Boolean must be the actual comparison result, and its phase
operand must be the phase field of the same returned controller state. -/
def recognize (start : Nat) (body : List Construction.Instruction) (yielded : List Nat) :
    Option (Recognized body yielded) := do
  let [first, second] := body | none
  let .execute (.indexConstant threshold) := first.operation | none
  let [phase, _] := second.operands | none
  let _ :: state := yielded | none
  if exactBody : body = instructions start phase threshold then
    if exactYield : yielded = (start + 1) :: state then
      if phaseField : state[6]? = some phase then
        some ⟨start, phase, threshold, state, exactBody, exactYield, phaseField⟩
      else none
    else none
  else none

def results {carriers : Carriers} (phase threshold : Nat) : Domain.Environment carriers :=
  [.data (.index threshold), .data (.boolean (decide (phase < threshold)))]

theorem simulation (model : DomainModel) (program : Program) (context : Context)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) (reference phase threshold : Nat)
    (phaseBound : phase < indexLimit) (thresholdBound : threshold < indexLimit)
    (read : environment[reference]? = some (.data (.index phase))) :
    Nonempty (Original.Simulation Eq (fun _ live ↦ captured <+: live)
      (.done (environment ++ results phase threshold))
      (Domain.evaluate model program context
        (instructions environment.length reference threshold) environment)) := by
  have constant : Domain.View.execute model (.indexConstant threshold) [] [.data .index]
      environment = .done (environment ++ [.data (.index threshold)]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant threshold)
      .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, thresholdBound, primitiveOutcome,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle] using law
  have operands : Domain.read (environment ++ [.data (.index threshold)])
      [reference, environment.length] = Domain.encodeValues
        (tys := [.index, .index]) (.cons phase (.cons threshold .nil)) := by
    simp [Domain.read, Original.read_append read [.data (.index threshold)],
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle]
  have comparison : Domain.View.execute model .indexLess [reference, environment.length]
      [.data .boolean] (environment ++ [.data (.index threshold)]) =
        .done (environment ++ results phase threshold) := by
    have law := ConnectionPrimitives.view_execute model .indexLess
      (.cons phase (.cons threshold .nil)) rfl rfl _ _ operands
    simpa [Primitive.results, Primitive.evaluateOn, checkedIndices, phaseBound, thresholdBound,
      primitiveOutcome, PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle,
      results, List.append_assoc] using law
  rw [correspondence]
  refine ⟨?_⟩
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
  apply RecordAllocator.silent_sequence constant preserved (preserved.trans (List.prefix_append _ _))
  apply RecordAllocator.silent_sequence comparison (preserved.trans (List.prefix_append _ _))
    (preserved.trans (List.prefix_append _ _))
  exact .done rfl

/-- The complete range yield retains its existing state layout and relates the
flag to the phase that was actually read. This is a structural obligation of
the controller connection, independent of its mathematical virtual answer. -/
theorem yield_read {carriers : Carriers}
    (environment carried : Domain.Environment carriers) (references : List Nat)
    (declared : List ValueSort) (phase threshold : Nat)
    (read : Domain.read environment references = some carried)
    (sorts : Domain.sortsMatch declared carried = true) :
    (Domain.read (environment ++ results phase threshold)
      ((environment.length + 1) :: references)).bind (Domain.rangeResult true declared) =
        some (decide (phase < threshold), carried) := by
  have retained := RecordAllocator.read_extended environment (results phase threshold)
    references carried read
  have all := Domain.View.read_cons _ (environment.length + 1) references
    (.data (.boolean (decide (phase < threshold)))) carried
    (by simp [results]) retained
  rw [all]
  simp [Domain.rangeResult, sorts]

theorem Recognized.yieldSimulation {A : Type} {body : List Construction.Instruction}
    {yielded : List Nat} (checked : Recognized body yielded)
    (model : DomainModel) (program : Program) (context : Context)
    (environment captured carried : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) (start : checked.start = environment.length)
    (phase : Nat) (phaseBound : phase < indexLimit)
    (thresholdBound : checked.threshold < indexLimit)
    (statePhase : carried[6]? = some (.data (.index phase)))
    (readState : Domain.read environment checked.state = some carried)
    (declared : List ValueSort) (sorts : Domain.sortsMatch declared carried = true)
    (relation : A → Domain.Environment model.toCarriers → Prop)
    (value : A) (related : relation value carried) :
    Nonempty (Original.Simulation (ConnectionLocalRange.Yield relation true declared yielded)
      (fun _ live ↦ captured <+: live) (.done (decide (phase < checked.threshold), value))
      (Domain.evaluate model program context body environment)) := by
  have readPhase : environment[checked.phase]? = some (.data (.index phase)) := by
    have projected := Domain.View.read_getElem? readState 6
    rw [statePhase, checked.phaseField] at projected
    exact projected.symm
  rcases checked with ⟨offset, phaseReference, threshold, references, rfl, rfl, _⟩
  dsimp only at start thresholdBound readPhase readState ⊢
  subst offset
  obtain ⟨head⟩ := simulation model program context environment captured preserved
    phaseReference phase threshold phaseBound thresholdBound readPhase
  have tail : Original.Simulation
      (ConnectionLocalRange.Yield relation true declared ((environment.length + 1) :: references))
      (fun (_ : PIR.Process (Domain.effects model.toCarriers) (Bool × A)) live ↦ captured <+: live)
      (.done (decide (phase < threshold), value))
      (.done (environment ++ results phase threshold)) :=
    .done ⟨carried, yield_read environment carried references declared phase threshold readState sorts,
      related⟩
  refine ⟨?_⟩
  simpa only [PIR.Process.bind_done] using
    (head.continueDone (targetNext := PIR.Process.done) (fun _ held ↦ held) tail)

end Zkc.Realization.QueryPhaseYield
