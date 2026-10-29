module

public import Zkc.Executable.DomainNormalization
public import Zkc.Construction.ScalarAdapter

@[expose] public section

/-! Reached nominal schemas and total calculation laws. These are runtime
representation invariants, independent of protocol validity. An invalid sort
or declaration is refused by Domain rather than erased by the scalar ABI. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
variable {carriers : Structured.Carriers}

theorem decode_of_sort {value : Domain.Value carriers} {ty : Structured.Ty}
    (sorted : value.sort = .data ty) : ∃ decoded, value.decode ty = some decoded := by
  cases value with
  | data payload =>
      rcases payload with ⟨actual, supported, contents⟩
      simp only [Domain.Value.sort, ValueSort.data.injEq] at sorted
      subst actual
      exact ⟨contents, by simp [Domain.Value.decode, Domain.Payload.value]⟩
  | transcript | indices => cases sorted

theorem decodeValues_of_sorts :
    ∀ (tys : List Structured.Ty) (env : Domain.Environment carriers),
      env.map Domain.Value.sort = tys.map ValueSort.data →
        ∃ values, Domain.decodeValues tys env = some values
  | [], [], _ => ⟨.nil, rfl⟩
  | [], _ :: _, sorted => by simp at sorted
  | _ :: _, [], sorted => by simp at sorted
  | ty :: tys, value :: env, sorted => by
      simp only [List.map_cons, List.cons.injEq] at sorted
      obtain ⟨decoded, found⟩ := decode_of_sort sorted.1
      obtain ⟨rest, restFound⟩ := decodeValues_of_sorts tys env sorted.2
      exact ⟨.cons decoded rest, by simp [Domain.decodeValues, found, restFound]⟩

theorem encode_sort {ty : Structured.Ty} {value : carriers.Value ty}
    {encoded : Domain.Value carriers} (found : Domain.Value.encode ty value = some encoded) :
    encoded.sort = .data ty := by
  unfold Domain.Value.encode Domain.Payload.ofValue at found
  split at found
  · cases found
    rfl
  · cases found

theorem encodeValues_sorts {tys : List Structured.Ty} (values : Values carriers.Value tys)
    {encoded : Domain.Environment carriers} (found : Domain.encodeValues values = some encoded) :
    encoded.map Domain.Value.sort = tys.map ValueSort.data := by
  induction values generalizing encoded with
  | nil => simp only [Domain.encodeValues, Option.some.injEq] at found; subst encoded; rfl
  | cons head tail ih =>
      simp only [Domain.encodeValues] at found
      cases first : Domain.Value.encode _ head with
      | none => simp [first] at found
      | some encodedHead =>
          cases rest : Domain.encodeValues tail with
          | none => simp [first, rest] at found
          | some encodedTail =>
              simp [first, rest] at found
              subst encoded
              simp only [List.map_cons, encode_sort first, ih rest]

/-- Appending a checked result is the only successful write performed by a
constructed step. This is a schema law, not an assumed successful execution. -/
theorem append_schema (declared : List ValueSort) (env results : Domain.Environment carriers) :
    PIR.Yields (fun final => ∃ values, final = env ++ values ∧
      Domain.sortsMatch declared values = true) (Domain.View.append declared env results) := by
  unfold Domain.View.append
  split
  · exact ⟨results, rfl, by assumption⟩
  · trivial

private theorem yields_bind_all {I : PIR.Signature} {A B : Type}
    (process : PIR.Process I A) (property : B → Prop) (next : A → PIR.Process I B)
    (checked : ∀ value, PIR.Yields property (next value)) :
    PIR.Yields property (process.bind next) := by
  induction process with
  | done value => exact checked value
  | halt => trivial
  | call operation continuation ih => exact fun reply => ih reply

/-- All replies retain the input prefix and the actual declared result sorts.
The statement includes malformed metadata: those paths stop explicitly. -/
theorem step_schema (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (instruction : Instruction) (env : Domain.Environment model.toCarriers) :
    PIR.Yields (fun final => ∃ values, final = env ++ values ∧
      Domain.sortsMatch instruction.results values = true)
      (Domain.step model program context instruction env) := by
  rcases instruction with ⟨operation, operands, declared, body⟩
  have appendChecked := append_schema (carriers := model.toCarriers) declared env
  have bindChecked (process : PIR.Process (Domain.effects model.toCarriers)
      (Domain.Environment model.toCarriers)) :=
    yields_bind_all process _ (Domain.View.append declared env) appendChecked
  unfold Domain.step
  split
  all_goals repeat' first
    | exact appendChecked _
    | exact bindChecked _
    | (change True; trivial)
    | (change ∃ values, _ = env ++ values ∧ _; exact ⟨_, rfl, by assumption⟩)
    | (change ∃ values, env = env ++ values ∧ _; exact ⟨[], by simp, by simp_all [Domain.sortsMatch]⟩)
    | (split <;> try dsimp only)
    | (intro reply; try dsimp only)

/-- The complete reached SSA schema follows from the declarations enforced
by Domain, including loop results, without any source relation premise. -/
theorem evaluate_schema (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (instructions : List Instruction) (env : Domain.Environment model.toCarriers) :
    PIR.Yields (fun final => final.map Domain.Value.sort =
      env.map Domain.Value.sort ++ instructions.flatMap Instruction.results)
      (Domain.evaluate model program context instructions env) := by
  induction instructions generalizing env with
  | nil => simp [Domain.evaluate, PIR.Yields]
  | cons instruction rest ih =>
      simp only [Domain.evaluate, PIR.Yields]
      intro _
      apply (step_schema model program context instruction env).bind
      intro final found
      obtain ⟨values, rfl, sorted⟩ := found
      simp only [Domain.sortsMatch, beq_iff_eq] at sorted
      intro _
      exact (ih (env ++ values)).mono fun final found => by
        simpa [List.map_append, sorted, List.flatMap_cons, List.append_assoc] using found

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Totality is a checked operation property, while operand availability and
sorts are explicit scope facts. No mathematical relation is assumed true. -/
theorem calculate_total (calculation : Calculation) (total : calculation.total = true)
    (arguments : Environment F G)
    (data : calculation.op.arguments.all Domain.dataType = true)
    (sorted : arguments.map Domain.Value.sort = calculation.op.arguments.map ValueSort.data) :
    ∃ results, Domain.calculate (Structured.ringModel F G) calculation arguments = .returned results ∧
      results.map Domain.Value.sort = calculation.op.results.map ValueSort.data := by
  obtain ⟨values, decoded⟩ := decodeValues_of_sorts _ arguments sorted
  have evaluates : ∃ results, calculation.evaluate values = .returned results := by
    cases calculation <;> simp [Calculation.total] at total <;>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨results, evaluated⟩ := evaluates
  have eligible : calculation.op.results.all Domain.dataType = true := by
    cases calculation <;>
      simp_all [Calculation.op, Structured.Op.arguments, Structured.Op.results,
        Domain.dataType, Structured.Ty.isService]
  obtain ⟨encoded, encodedEq⟩ := Domain.encodeValues_exists results eligible
  refine ⟨encoded, ?_, encodeValues_sorts results encodedEq⟩
  simp only [Domain.calculate, decoded,
    Uniform.DomainAdapter.operationOn_calculation, evaluated, ofOutcome,
    Domain.closedOutcome, encodedEq]

end Zkc.Executable.DomainVM
