module

public import Zkc.Core.ThreadDefinition
public import Zkc.Core.Serialize

public section

/-! The two rules are sound: what each emits runs as its meaning.

`Emitted.Yields` says what an emitted sequence does with its results: it runs as a
process, after which the environment is a function of the process's result and holds
every earlier value where it was. One operation yields its own process
(`Emitted.operation_yields`), a sequence yields its parts in order
(`Emitted.Yields.andThen`), and a process may be restated through a function of its
result (`Emitted.Yields.reindex`).

`serializeMeaning` and `serializeRule_sound`: an exchange from the prover to the verifier
is a `put` at the prover, and a `take` and a guard of its flag at the verifier; no draw is
rewritten. After the guard the flag holds (`flagGuard_bind`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Source

variable {dialect : Dialect} {I : PIR.Signature} {Δ : List dialect.Ty}

/-- An emitted sequence runs as a process whose result determines the environment it
leaves; every earlier value is where it was. -/
structure Emitted.Yields {results : List dialect.Ty} (emitted : Emitted dialect Δ results)
    (meaning : RegionMeaning dialect I) (env : Environment meaning.Value Δ) {R : Type}
    (process : PIR.Process I R) (later : R → Environment meaning.Value emitted.context) : Prop where
  runs : emitted.Runs meaning env (process.bind fun result => .done (later result))
  keeps : ∀ (result : R) {ty : dialect.Ty} (reference : Var Δ ty),
    later result (reference.extend emitted.grows) = env reference

namespace Emitted

/-- One operation yields its results. -/
theorem operation_yields (meaning : RegionMeaning dialect I) (op : dialect.Op)
    (arguments : Operands Δ (dialect.arguments op)) (bodies : Regions dialect (dialect.regions op))
    (env : Environment meaning.Value Δ) :
    (Emitted.operation op arguments bodies).Yields meaning env
      (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning))
      (fun values => Environment.bindAll env values) :=
  ⟨Emitted.operation_runs meaning op arguments bodies env,
    fun values _ reference => Emitted.operation_keeps meaning op arguments bodies env values reference⟩

/-- A sequence yields the results of its two parts. -/
theorem Yields.andThen {first second results : List dialect.Ty} {meaning : RegionMeaning dialect I}
    {before : Emitted dialect Δ first} {after : Emitted dialect before.context second}
    {env : Environment meaning.Value Δ} {R S : Type} {process : PIR.Process I R}
    {laterBefore : R → Environment meaning.Value before.context} {next : R → PIR.Process I S}
    {laterAfter : R → S → Environment meaning.Value after.context}
    (yieldsBefore : before.Yields meaning env process laterBefore)
    (yieldsAfter : ∀ result, after.Yields meaning (laterBefore result) (next result)
      (laterAfter result))
    (values : Operands after.context results) :
    (before.andThen after values).Yields meaning env
      (process.bind fun result => (next result).bind fun last => .done (result, last))
      (fun pair => laterAfter pair.1 pair.2) := by
  refine ⟨?_, ?_⟩
  · intro out rest
    refine (yieldsBefore.runs (after.wrap rest)).trans ?_
    simp only [PIR.Process.bind_assoc]
    congr 1
    funext result
    refine ((yieldsAfter result).runs rest).trans ?_
    simp only [PIR.Process.bind_assoc]
    rfl
  · intro pair ty reference
    exact (congrArg (laterAfter pair.1 pair.2) (Var.ext (Nat.add_assoc ..).symm)).trans
      (((yieldsAfter pair.1).keeps pair.2 (reference.extend before.grows)).trans
        (yieldsBefore.keeps pair.1 reference))

/-- The same sequence, with its process stated through a function of another result. -/
theorem Yields.reindex {results : List dialect.Ty} {meaning : RegionMeaning dialect I}
    {emitted : Emitted dialect Δ results} {env : Environment meaning.Value Δ} {R R' : Type}
    {process : PIR.Process I R} {later : R → Environment meaning.Value emitted.context}
    (yields : emitted.Yields meaning env process later) (base : PIR.Process I R') (index : R' → R)
    (same : process = base.bind fun result => .done (index result)) :
    emitted.Yields meaning env base (fun result => later (index result)) := by
  refine ⟨?_, fun result _ reference => yields.keeps (index result) reference⟩
  intro out rest
  refine (yields.runs rest).trans ?_
  subst same
  simp only [PIR.Process.bind_assoc]
  rfl

end Emitted

end Zkc.Source

namespace Zkc.Core

open Zkc.Source

section Serialize

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The guard of the flag of a take at a role: continue when the reader had a value, stop
`reject` otherwise. A role outside the side does nothing. -/
abbrev flagGuard (present : Bool) (flag : Held Bool present) :
    PIR.Process (Effects model) (Values (fun type => Held (model.Value type) present) []) :=
  performStep model (inputs := [.bool]) (outputs := [])
    (fun arguments => cond (arguments.get .here) (.done .nil) (.halt Reason.reject.stop))
    present (.cons flag .nil)

/-- After the guard the flag holds: what follows may read it as `true`. -/
theorem flagGuard_bind {α : Type} (present : Bool) (flag : Held Bool present)
    (continuation : Held Bool present →
      Values (fun type => Held (model.Value type) present) [] → PIR.Process (Effects model) α) :
    (flagGuard (model := model) present flag).bind (continuation flag) =
      (flagGuard (model := model) present flag).bind (continuation (Held.of present true)) := by
  cases present with
  | false => cases flag; rfl
  | true =>
      revert flag continuation
      show ∀ (flag : Bool) (continuation : Bool →
        Values (fun type => Held (model.Value type) true) [] → PIR.Process (Effects model) α), _
      intro flag continuation
      cases flag <;> rfl

/-- What the serialize rule does for a side: the prover puts the value on its writer, and
the verifier takes a value from its reader and guards the flag. A role outside the side
does nothing. -/
@[expose] def serializeMeaning (layout : Layout operations) :
    RuleMeaning model ⟨layout.writer, layout.reader⟩ operations where
  exchange := fun prover verifier place _ _ type value state =>
    if populated : Ty.allPopulated [.bool, type, layout.reader] = true then
      match layout.put type, layout.take type with
      | some put, some take =>
          (performStep model (rowProcess model (.of put) .pure layout.writerPopulated)
            prover
            (.cons state.1 (.cons value .nil))).bind fun written =>
            (performStep model (rowProcess model (.of take) .pure populated)
              verifier
              (.cons state.2 .nil)).bind fun taken =>
              (flagGuard (model := model) verifier (taken.get .here)).bind
                fun _ =>
                  .done (taken.tail.get .here, (written.get .here, taken.tail.tail.get .here))
      | _, _ => .halt .refused
    else .halt .refused
  draw := fun _ _ _ _ _ _ _ _ _ => .halt .refused

/-- The serialize rule is sound. -/
theorem serializeRule_sound (layout : Layout operations)
    (functionTable : FunctionTable model functions) :
    RuleSound (serializeRule (functions := functions) layout) (serializeMeaning layout)
      functionTable := by
  refine ⟨?_, ?_⟩
  · intro protocols deployed table label side place site type Δ value first second emitted emits env
    simp only [serializeRule] at emits
    split at emits
    · rename_i populated
      split at emits
      · rename_i put take hasPut hasTake
        have same := Except.ok.inj emits
        subst same
        clear emits
        have key : ∀ (results : List Located) (values : Operands _ results),
            (Emitted.andThen (results := results)
              (Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
                (.at place.roles.prover (.op put layout.writerPopulated) .nil)
                (.cons first (.cons value .nil)) .nil)
              (Emitted.andThen
                (Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
                  (.at place.roles.verifier (.op take populated) .nil)
                  (.cons (second.extend (Emitted.operation
                    (dialect := ProtocolDialect operations functions protocols deployed)
                    (.at place.roles.prover (.op put layout.writerPopulated) .nil)
                    (.cons first (.cons value .nil)) .nil).grows) .nil) .nil)
                (Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
                  (.at place.roles.verifier (.guard .reject) .nil)
                  (.cons ((Emitted.operation
                    (dialect := ProtocolDialect operations functions protocols deployed)
                    (.at place.roles.verifier (.op take populated) .nil)
                    (.cons (second.extend (Emitted.operation
                      (dialect := ProtocolDialect operations functions protocols deployed)
                      (.at place.roles.prover (.op put layout.writerPopulated) .nil)
                      (.cons first (.cons value .nil)) .nil).grows) .nil) .nil).values.get .here)
                    .nil) .nil)
                .nil)
              values).Yields (labelledMeaning model label functionTable table side) env
              ((serializeMeaning layout).exchange (side place.roles.prover) (side place.roles.verifier) place site (label site) type (env value)
                (env first, env second))
              (fun result => Environment.bindAll (Environment.bindAll
                (Environment.bindAll env (Values.cons result.2.1 .nil))
                (Values.cons (Held.of (side place.roles.verifier) true :
                    SideValue model side ⟨.bool, place.roles.verifier⟩)
                  (.cons result.1 (.cons result.2.2 .nil)))) .nil) := by
          intro results values
          refine ((Emitted.operation_yields
              (labelledMeaning model label functionTable table side)
              (.at place.roles.prover (.op put layout.writerPopulated) .nil)
              (.cons first (.cons value .nil)) .nil env).andThen
            (fun written => (Emitted.operation_yields
              (labelledMeaning model label functionTable table side)
              (.at place.roles.verifier (.op take populated) .nil) _ .nil
              (Environment.bindAll env written)).andThen
              (fun taken => Emitted.operation_yields
                (labelledMeaning model label functionTable table side)
                (.at place.roles.verifier (.guard .reject) .nil) _ .nil
                (Environment.bindAll (Environment.bindAll env written) taken)) .nil)
            values).reindex _
            (fun (result : SideValue model side ⟨type, place.roles.verifier⟩ ×
                ThreadState model ⟨layout.writer, layout.reader⟩ (side place.roles.prover)
                  (side place.roles.verifier)) =>
              (Values.cons result.2.1 .nil,
                (Values.cons (Held.of (side place.roles.verifier) true :
                    SideValue model side ⟨.bool, place.roles.verifier⟩)
                  (.cons result.1 (.cons result.2.2 .nil)), Values.nil)))
            ?_
          simp only [serializeMeaning, hasPut, hasTake, populated, ↓reduceDIte, labelledOperation,
            PIR.Process.bind_assoc, PIR.Process.done_bind, Operands.eval, Emitted.operation_keeps]
          refine bind_congr rfl fun written => ?_
          refine bind_congr ?_ fun taken => ?_
          · rfl
          match written, taken with
          | .cons writer .nil, .cons flag (.cons taken (.cons reader .nil)) =>
            refine (bind_congr (other := flagGuard (model := model) (side place.roles.verifier) flag)
              rfl fun _ => rfl).trans ?_
            refine (flagGuard_bind (model := model) (side place.roles.verifier) flag
              (fun flag guarded => PIR.Process.done
                (remapValues (F := SideValue model side) (fun type => ⟨type, place.roles.prover⟩)
                    [layout.writer] (Values.cons writer .nil),
                  remapValues (F := SideValue model side) (fun type => ⟨type, place.roles.verifier⟩)
                    [.bool, type, layout.reader] (Values.cons flag (.cons taken (.cons reader .nil))),
                  remapValues (F := SideValue model side) (fun type => ⟨type, place.roles.verifier⟩)
                    [] guarded))).trans ?_
            exact bind_congr rfl fun guarded => by cases guarded; rfl
        exact ⟨_, (key _ _).runs, fun result =>
          ⟨rfl, rfl, rfl, fun reference => (key _ _).keeps result reference⟩⟩
      · cases emits
    · cases emits
  · intro protocols deployed table label side place site inputs output law Δ first second emitted
      emits
    simp only [serializeRule] at emits
    cases emits

end Serialize

end Zkc.Core
