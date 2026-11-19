module

public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Driver.SourcePhases

@[expose] public section
namespace Zkc.Frontend.Written

def sourceState (assembly : Assembly) : ExportM Compile.State := do
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    let (report, next) := phase.runIn sourceContext state
    state := next
    if let some diag := state.log.entries.find? (fun d => d.isError || d.isIncomplete) then
      throw s!"{diag.span.file}:{diag.render state.env.renderer}"
    if let some skipped := report.interrupted then throw s!"WK-FRONTEND: {skipped}"
  return state

structure AdmittedRoot where
  id : InstanceId
  state : Compile.State
  emission : Emit.RootEmission
  emitted : Typing.emitRoot state id = .ok emission
  evidence : (emission.package ⟨[],[],[],[],[]⟩).Admission

def admitInstance (state : Compile.State) (id : InstanceId) (place : Syntax.Span) : ExportM AdmittedRoot := do
  let (result, s) := (Typing.typeBody id place).run sourceContext state
  if let some diag := s.log.entries.find? (fun d => d.isError || d.isIncomplete) then
    throw s!"{diag.span.file}:{diag.render s.env.renderer}"
  let .ok _ := result | refuse place "WK-ROOT" "protocol did not typecheck"
  match emitted : Typing.emitRoot s id with
  | .error _ => refuse place "WK-CORE" "protocol did not emit"
  | .ok emission =>
    let .ok evidence := (emission.package ⟨[],[],[],[],[]⟩).checkEvidence
      | refuse place "WK-CORE" "admission refused the emitted program"
    return ⟨id,s,emission,emitted,evidence⟩

/-- Compile an assembly with one protocol root and retain the source state that produced
the admitted term for subsequent clause lookup. -/
def admitSource (assembly : Assembly) : ExportM AdmittedRoot := do
  let state ← sourceState assembly
  let #[id] := state.roots | throw "expected one source protocol root"
  admitInstance state id default

end Zkc.Frontend.Written
