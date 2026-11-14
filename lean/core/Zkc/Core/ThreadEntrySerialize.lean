module

public import Zkc.Core.ThreadEntry
public import Zkc.Core.ThreadEntryEmitted

public section

/-! What the entry of the serialize rule does, and that it does it.

`serializeEntry`: the rewritten entry has the proof as its first input, held by the
verifier, and as its first output, held by the prover. Before the body the prover opens a
writer with the layout's `start` row and the verifier opens a reader on the proof with the
`read` row. After the body the prover closes its writer into the proof with the `close`
row; the verifier applies the `exhausted` row to its reader and guards the flag with
`reject`. A role outside the side does nothing.

`serializeEntry_sound`: the region that the rule makes of a threaded body runs the start,
the body and the finish in this order, for every side; the start and the finish perform no
effect.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Serialize

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What the two roles do before the body of a serialized entry: the prover opens a writer
and the verifier opens a reader on the proof. A role outside the side does nothing. -/
@[expose] def Layout.opening (layout : Layout operations) (prover verifier : Bool)
    (proof : Held (model.Value layout.proof) verifier) :
    PIR.Process (Effects model)
      (ThreadState model ⟨layout.writer, layout.reader⟩ prover verifier) :=
  (performStep model (rowProcess model (.of layout.start) .pure layout.writerPopulated)
    prover .nil).bind fun opened =>
    (performStep model (rowProcess model (.of layout.read) .pure layout.readerPopulated)
      verifier (.cons proof .nil)).bind fun reading =>
      .done (opened.get .here, reading.get .here)

/-- What the two roles do after the body of a serialized entry: the prover closes its
writer into the proof; the verifier tests whether its reader is exhausted and guards the
flag with `reject`. The result is the prover's proof. A role outside the side does
nothing. -/
@[expose] def Layout.closing (layout : Layout operations) (prover verifier : Bool)
    (state : ThreadState model ⟨layout.writer, layout.reader⟩ prover verifier) :
    PIR.Process (Effects model) (Held (model.Value layout.proof) prover) :=
  (performStep model (rowProcess model (.of layout.close) .pure layout.proofPopulated)
    prover (.cons state.1 .nil)).bind fun closed =>
    (performStep model (rowProcess model (.of layout.exhausted) .pure rfl)
      verifier (.cons state.2 .nil)).bind fun checked =>
      (flagGuard (model := model) verifier (checked.get .here)).bind fun _ =>
        .done (closed.get .here)

/-- What the entry of the serialize rule does. -/
@[expose] def serializeEntry (layout : Layout operations) :
    EntryMeaning model ⟨layout.writer, layout.reader⟩ (serializeRule (functions := functions) layout) where
  arguments := fun _ _ _ values => values.tail
  start := fun side roles _ values =>
    layout.opening (side roles.prover) (side roles.verifier) (values.get .here)
  finish := fun side roles _ result =>
    (layout.closing (side roles.prover) (side roles.verifier) result.2).bind fun proof =>
      .done (.cons proof result.1)

variable {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {side : Side}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- What the serialize rule emits before the body of the entry yields the writer and the
reader. -/
theorem Layout.opening_yields (layout : Layout operations) (roles : TranscriptRoles)
    {Δ results : List Located} (proof : Var Δ ⟨layout.proof, roles.verifier⟩)
    (env : Environment (SideValue model side) Δ) (values : Operands _ results) :
    (Emitted.andThen (results := results)
      (Emitted.operation (dialect := 𝒟)
        (.at roles.prover (.op layout.start layout.writerPopulated) .nil) .nil .nil)
      (Emitted.operation (dialect := 𝒟)
        (.at roles.verifier (.op layout.read layout.readerPopulated) .nil)
        (.cons (proof.weaken [(⟨layout.writer, roles.prover⟩ : Located)]) .nil) .nil)
      values).Yields (labelledMeaning model label functionTable table side) env
      (layout.opening (model := model) (side roles.prover) (side roles.verifier) (env proof))
      (fun state => Environment.bindAll (Environment.bindAll env (Values.cons state.1 .nil))
        (Values.cons state.2 .nil)) := by
  refine ((Emitted.operation_yields (labelledMeaning model label functionTable table side)
      (.at roles.prover (.op layout.start layout.writerPopulated) .nil) .nil .nil env).andThen
    (fun opened => Emitted.operation_yields (labelledMeaning model label functionTable table side)
      (.at roles.verifier (.op layout.read layout.readerPopulated) .nil) _ .nil
      (Environment.bindAll env opened)) values).reindex _
    (fun (state : ThreadState model ⟨layout.writer, layout.reader⟩ (side roles.prover)
        (side roles.verifier)) => (Values.cons state.1 .nil, Values.cons state.2 .nil)) ?_
  simp only [Layout.opening, labelledOperation, PIR.Process.bind_assoc, PIR.Process.done_bind,
    Operands.eval, Emitted.operation_keeps]
  refine bind_congr rfl fun opened => ?_
  refine bind_congr ?_ fun reading => rfl
  exact congrArg (fun value => performStep model
      (rowProcess model (.of layout.read) .pure layout.readerPopulated) (side roles.verifier)
      (Values.cons value .nil))
    (Environment.bindAll_weaken env _ proof)

/-- What the serialize rule emits after the body of the entry gives the proof, which it
leaves at the value that the `close` row produced. -/
theorem Layout.closing_gives (layout : Layout operations) (roles : TranscriptRoles)
    {Δ results : List Located} (writer : Var Δ ⟨layout.writer, roles.prover⟩)
    (reader : Var Δ ⟨layout.reader, roles.verifier⟩)
    (env : Environment (SideValue model side) Δ) (values : Operands _ results) :
    (Emitted.andThen (results := results)
      (Emitted.operation (dialect := 𝒟)
        (.at roles.prover (.op layout.close layout.proofPopulated) .nil) (.cons writer .nil) .nil)
      (Emitted.andThen
        (Emitted.operation (dialect := 𝒟)
          (.at roles.verifier (.op layout.exhausted rfl) .nil)
          (.cons (reader.weaken [(⟨layout.proof, roles.prover⟩ : Located)]) .nil) .nil)
        (Emitted.operation (dialect := 𝒟)
          (.at roles.verifier (.guard .reject) .nil) (.cons .here .nil) .nil)
        .nil)
      values).Gives (labelledMeaning model label functionTable table side) env
      (layout.closing (model := model) (side roles.prover) (side roles.verifier)
        (env writer, env reader))
      (fun later => later (Var.there (head := (⟨.bool, roles.verifier⟩ : Located))
        (Var.here : Var ((⟨layout.proof, roles.prover⟩ : Located) :: Δ) _))) := by
  refine ⟨_, _, _, (Emitted.operation_yields (labelledMeaning model label functionTable table side)
      (.at roles.prover (.op layout.close layout.proofPopulated) .nil) (.cons writer .nil) .nil
      env).andThen
    (fun closed => (Emitted.operation_yields (labelledMeaning model label functionTable table side)
      (.at roles.verifier (.op layout.exhausted rfl) .nil) _ .nil
      (Environment.bindAll env closed)).andThen
      (fun checked => Emitted.operation_yields
        (labelledMeaning model label functionTable table side)
        (.at roles.verifier (.guard .reject) .nil) _ .nil
        (Environment.bindAll (Environment.bindAll env closed) checked)) .nil)
    values, ?_⟩
  simp only [Layout.closing, labelledOperation, PIR.Process.bind_assoc, PIR.Process.done_bind,
    Operands.eval, Emitted.operation_keeps]
  refine bind_congr rfl fun closed => ?_
  refine bind_congr ?_ fun checked => ?_
  · exact congrArg (fun value => performStep model
        (rowProcess model (.of layout.exhausted) .pure rfl) (side roles.verifier)
        (Values.cons value .nil))
      (Environment.bindAll_weaken env _ reader).symm
  · exact bind_congr rfl fun guarded => rfl

/-- The entry of the serialize rule runs as its meaning says. -/
theorem serializeEntry_sound (layout : Layout operations)
    (functionTable : FunctionTable model functions) :
    EntrySound (serializeRule layout) (serializeEntry layout) functionTable := by
  refine ⟨?_, ?_, ?_⟩
  · intro protocols deployed table label side place header body region made inner bodyMeaning
      arguments
    simp only [serializeRule] at made
    split at made
    · rename_i threaded threads
      have same := Except.ok.inj made
      subst same
      have opens := fun {results : List Located} values =>
        layout.opening_yields (model := model) (protocols := protocols) (deployed := deployed)
          (functionTable := functionTable) (table := table) (label := label) (side := side)
          (results := results) place.roles
          ((Var.here : Var [⟨layout.proof, place.roles.verifier⟩] _).weaken header.inputs)
          (Environment.ofValues arguments) values
      refine ((opens .nil).runs _).trans ?_
      refine (PIR.Process.bind_assoc _ _ _).trans (bind_congr ?_ fun state => ?_)
      · exact congrArg (layout.opening (side place.roles.prover) (side place.roles.verifier))
          (Environment.bindAll_weaken (Environment.empty.push (arguments.get .here))
            arguments.tail Var.here)
      · have base : (Renaming.keepAll
            (Mapping.start (Δ := [(⟨layout.proof, place.roles.verifier⟩ : Located)]) 1 rfl)
            header.inputs).Agrees (Environment.ofValues arguments.tail)
            (Environment.ofValues arguments) :=
          Renaming.Agrees.keepAll
            (rename := Mapping.start (Δ := [(⟨layout.proof, place.roles.verifier⟩ : Located)]) 1 rfl)
            (old := Environment.empty) (new := Environment.empty.push (arguments.get .here))
            (fun reference => reference.elimNil) arguments.tail
        let afterOpening : Environment (SideValue model side)
            (bindAll (bindAll [(⟨layout.proof, place.roles.verifier⟩ : Located)] header.inputs)
              [⟨layout.writer, place.roles.prover⟩]) :=
          Environment.bindAll (Environment.ofValues arguments) (Values.cons state.1 .nil)
        let afterReading : Environment (SideValue model side)
            (bindAll (bindAll (bindAll [(⟨layout.proof, place.roles.verifier⟩ : Located)]
              header.inputs) [⟨layout.writer, place.roles.prover⟩])
              [⟨layout.reader, place.roles.verifier⟩]) :=
          Environment.bindAll afterOpening (Values.cons state.2 .nil)
        have agrees : Renaming.Agrees
            (((Renaming.keepAll
              (Mapping.start (Δ := [(⟨layout.proof, place.roles.verifier⟩ : Located)]) 1 rfl)
              header.inputs).extend
                (Extends.bindAll _ [(⟨layout.writer, place.roles.prover⟩ : Located)])).extend
                  (Extends.bindAll _ [(⟨layout.reader, place.roles.verifier⟩ : Located)]))
            (Environment.ofValues arguments.tail) afterReading :=
          Renaming.Agrees.extend
          (Renaming.Agrees.extend base
            (Extends.bindAll _ [(⟨layout.writer, place.roles.prover⟩ : Located)]) afterOpening
            (fun reference => Environment.bindAll_weaken (Environment.ofValues arguments)
              (Values.cons (ty := (⟨layout.writer, place.roles.prover⟩ : Located)) state.1 .nil)
              reference))
          (Extends.bindAll _ [(⟨layout.reader, place.roles.verifier⟩ : Located)]) afterReading
          (fun reference => Environment.bindAll_weaken afterOpening
            (Values.cons (ty := (⟨layout.reader, place.roles.verifier⟩ : Located)) state.2 .nil)
            reference)
        refine bind_congr (bodyMeaning _ _ _ threaded threads arguments.tail afterReading agrees)
          fun values => ?_
        match values with
        | .cons finalWriter (.cons finalReader outputs) =>
          let withFinal : Environment (SideValue model side)
              ((⟨layout.reader, place.roles.verifier⟩ : Located) ::
                ⟨layout.writer, place.roles.prover⟩ ::
                bindAll (bindAll (bindAll [(⟨layout.proof, place.roles.verifier⟩ : Located)]
                  header.inputs) [⟨layout.writer, place.roles.prover⟩])
                  [⟨layout.reader, place.roles.verifier⟩]) :=
            Environment.push (Environment.push afterReading finalWriter) finalReader
          let afterBody : Environment (SideValue model side)
              (bindAll ((⟨layout.reader, place.roles.verifier⟩ : Located) ::
                ⟨layout.writer, place.roles.prover⟩ ::
                bindAll (bindAll (bindAll [(⟨layout.proof, place.roles.verifier⟩ : Located)]
                  header.inputs) [⟨layout.writer, place.roles.prover⟩])
                  [⟨layout.reader, place.roles.verifier⟩]) header.outputs) :=
            Environment.bindAll withFinal outputs
          have closes := layout.closing_gives (model := model) (protocols := protocols)
            (deployed := deployed) (functionTable := functionTable) (table := table)
            (label := label) (side := side) (results := []) place.roles
            ((Var.there .here : Var ((⟨layout.reader, place.roles.verifier⟩ : Located) ::
              ⟨layout.writer, place.roles.prover⟩ :: _) _).weaken header.outputs)
            ((Var.here : Var ((⟨layout.reader, place.roles.verifier⟩ : Located) ::
              ⟨layout.writer, place.roles.prover⟩ :: _) _).weaken header.outputs)
            afterBody .nil
          refine (closes.wrap_denote _
            (fun proof => PIR.Process.done
              (Values.cons (ty := (⟨layout.proof, place.roles.prover⟩ : Located)) proof outputs))
            ?_).trans ?_
          · intro later keeps
            exact congrArg PIR.Process.done (congr (congrArg Values.cons rfl)
              ((Operands.eval_extend _ afterBody later keeps _).trans
                (Operands.eval_newest header.outputs _ outputs)))
          · exact bind_congr
              (congrArg (layout.closing (side place.roles.prover) (side place.roles.verifier))
                (Prod.ext
                  (Environment.bindAll_weaken withFinal outputs (Var.there .here))
                  (Environment.bindAll_weaken withFinal outputs Var.here)))
              fun proof => rfl
    · cases made
  · intro quiet side roles header arguments
    exact PIR.Process.Quiet.bind
      (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _) fun _ =>
        PIR.Process.Quiet.bind
          (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _) fun _ =>
            PIR.Process.Quiet.done _
  · intro quiet side roles header result
    refine PIR.Process.Quiet.bind ?_ fun _ => PIR.Process.Quiet.done _
    refine PIR.Process.Quiet.bind
      (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _) fun _ =>
        PIR.Process.Quiet.bind
          (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _) fun _ =>
            PIR.Process.Quiet.bind (performStep_quiet (fun values => ?_) _ _) fun _ =>
              PIR.Process.Quiet.done _
    cases values.get .here
    · exact PIR.Process.Quiet.halt _
    · exact PIR.Process.Quiet.done _

end Serialize

end Zkc.Core
