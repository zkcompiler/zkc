module

public import Zkc.Source.Structured.MarkedPrefix
public import Zkc.Source.Structured.OracleLocalAction

@[expose] public section

/-! Successful execution of a lexical mark schedule under the publication
handler. The certificate checks the same cursor operation as the interpreter.
It depends on the definition, block and instruction offset. An enclosing call
or repeat can change the invocation without invalidating it. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol

def advanceMarks (snapshot : Snapshot) (frame : Frame) : List String → Except String Frame
  | [] => .ok frame
  | label :: rest => do
    let after ← sourceStep snapshot frame label
    advanceMarks snapshot after rest

private theorem stepInvocation (snapshot : Snapshot) (frame : Frame)
    (invocation : InvocationCoordinate) (label : String) :
    sourceStep snapshot {frame with invocation} label =
      (sourceStep snapshot frame label).map (fun after ↦ {after with invocation}) := by
  unfold sourceStep
  cases h : sourceSite snapshot {frame with row := frame.block ++ [1, frame.next]} label with
  | error reason =>
    change ((sourceSite snapshot {frame with row := frame.block ++ [1, frame.next]} label).bind _) = _
    simp [h, Except.map, bind, Except.bind]
  | ok row =>
    change ((sourceSite snapshot {frame with row := frame.block ++ [1, frame.next]} label).bind _) = _
    simp [h, Except.map, bind, Except.bind, pure, Except.pure]

theorem advanceInvocation (snapshot : Snapshot) (frame : Frame) (invocation : InvocationCoordinate)
    (labels : List String) :
    advanceMarks snapshot {frame with invocation} labels =
      (advanceMarks snapshot frame labels).map (fun after ↦ {after with invocation}) := by
  induction labels generalizing frame with
  | nil => rfl
  | cons label rest ih =>
    simp only [advanceMarks, stepInvocation]
    cases step : sourceStep snapshot frame label with
    | error reason => rfl
    | ok after => exact ih after

end Zkc.Source.Structured.OracleProtocol

namespace Zkc.Source.Structured.OraclePublication
open OracleProtocol (Frame advanceMarks withMarks)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (Interface model) S E)
local notation "State" => OracleProtocol.State model snapshot domains math S
local notation "action" => actionM model oracles ordinary base publish

/-- A checked prefix always returns. It advances the cursor, retains every
observed mark in order and preserves the store and the caller stack. -/
theorem runCheckedMarks (state : State) (labels : List (String × String)) {after : Frame}
    (aligned : advanceMarks snapshot state.frame (labels.map Prod.fst) = .ok after) :
    (withMarks labels (.done ())).runM action state =
      pure ⟨.returned (), {state with frame := after}, labels.map (fun p ↦ .mark p.2)⟩ := by
  induction labels generalizing state with
  | nil =>
    cases aligned
    rfl
  | cons label labels ih =>
    rcases label with ⟨source, observed⟩
    simp only [List.map_cons, advanceMarks] at aligned
    cases step : OracleProtocol.sourceStep snapshot state.frame source with
    | error reason => simp [step, bind, Except.bind] at aligned
    | ok next =>
      have tail : advanceMarks snapshot next (labels.map Prod.fst) = .ok after := by
        simpa [step, bind, Except.bind] using aligned
      rw [withMarks, PIR.Process.runM, actionM_local _ _ _ _ _ _ rfl, pure_bind]
      simp only [OracleProtocol.handler, step, PIR.Execution.followM]
      rw [ih {state with frame := next} tail, pure_bind]
      rfl

/-- An application resolves its callee once by name and complete signature.
The invocation suffix comes from the caller's current row. -/
def applicationFrame (parent : Frame) (row : List Nat) (definition : Nat) : Frame where
  invocation := {parent.invocation with frames := parent.invocation.frames ++ [.application parent.definition row]}
  definition := definition

theorem runApplicationEntry (state : State) (signature : ProtocolSignature) (site : String)
    {row : List Nat} (located : OracleProtocol.sourceSite snapshot state.frame site = .ok row)
    {function : Function}
    (resolved : snapshot.definitions[snapshot.definitions.findIdx (·.name == signature.name)]? =
      some (.function function))
    (same : resolveProtocolSignature function = .ok signature) :
    action (.application signature site) state =
      pure ⟨.returned (), {state with
        frame := applicationFrame state.frame row (snapshot.definitions.findIdx (·.name == signature.name))
        parents := state.frame :: state.parents}, []⟩ := by
  rw [actionM_local _ _ _ _ _ _ rfl]
  simp [OracleProtocol.handler, located, resolved, same, applicationFrame]

def iterationFrame (parent : Frame) (row : List Nat) (index : Nat) : Frame :=
  {parent with
    invocation.frames := parent.invocation.frames ++ [.iteration parent.definition row index]
    block := row ++ [4, 0, 3]
    next := 0
    row := []}

theorem runIterationEntry (state : State) (site : String) (index : Nat) {row : List Nat}
    (located : OracleProtocol.sourceSite snapshot state.frame site = .ok row) :
    action (.iteration site index) state = pure ⟨.returned (), {state with
      frame := iterationFrame state.frame row index, parents := state.frame :: state.parents}, []⟩ := by
  rw [actionM_local _ _ _ _ _ _ rfl]
  simp only [OracleProtocol.handler, located]
  rfl

theorem runExit (state : State) {parent : Frame} {parents : List Frame}
    (nested : state.parents = parent :: parents) :
    action .leave state = pure ⟨.returned (), {state with frame := parent, parents}, []⟩ := by
  rw [actionM_local _ _ _ _ _ _ rfl]
  simp only [OracleProtocol.handler, nested]

/-- Remove exactly the checked prefix and entry from an actual application.
Retain the source exit in the suffix so that a stop in the child skips it. -/
theorem runMarkedApplication {A : Type} (state : State) (labels : List (String × String))
    (signature : ProtocolSignature) (site : String) (body : PIR.Process (OracleProtocol.Interface model) A)
    {marked : Frame} (aligned : advanceMarks snapshot state.frame (labels.map Prod.fst) = .ok marked)
    {row : List Nat} (located : OracleProtocol.sourceSite snapshot marked site = .ok row)
    {function : Function} (resolved : snapshot.definitions[snapshot.definitions.findIdx (·.name == signature.name)]? =
      some (.function function)) (same : resolveProtocolSignature function = .ok signature) :
    ((withMarks labels (.done ())).bind (fun _ ↦ OracleProtocol.enter model (.application signature site) body)).runM
      action state = (do
        let result ← (body.bind fun value ↦ .call .leave fun _ ↦ .done value).runM action {state with
          frame := applicationFrame marked row (snapshot.definitions.findIdx (·.name == signature.name))
          parents := marked :: state.parents}
        pure {result with events := labels.map (fun p ↦ .mark p.2) ++ result.events}) := by
  rw [PIR.runM_bind, runCheckedMarks oracles ordinary base publish state labels aligned, pure_bind]
  simp only [PIR.Execution.followM, OracleProtocol.enter, PIR.Process.bind, PIR.Process.runM]
  rw [runApplicationEntry oracles ordinary base publish {state with frame := marked} signature site located resolved same,
    pure_bind]
  simp only [List.nil_append, bind_pure_comp]
  simp

/-- A reusable certificate of a particular checked call prefix. All four
equations refer directly to operations used by the source interpreter. -/
structure CheckedCall (snapshot : Snapshot) (parent : Frame) (labels : List String)
    (signature : ProtocolSignature) (site : String) where
  marked : Frame
  row : List Nat
  callee : Function
  aligned : advanceMarks snapshot parent labels = .ok marked
  located : OracleProtocol.sourceSite snapshot marked site = .ok row
  resolved : snapshot.definitions[snapshot.definitions.findIdx (·.name == signature.name)]? = some (.function callee)
  signatureMatches : resolveProtocolSignature callee = .ok signature

namespace CheckedCall

def check (snapshot : Snapshot) (parent : Frame) (labels : List String) (signature : ProtocolSignature) (site : String) :
    Option (CheckedCall snapshot parent labels signature site) :=
  match aligned : advanceMarks snapshot parent labels with
  | .error _ => none
  | .ok marked =>
    match located : OracleProtocol.sourceSite snapshot marked site with
    | .error _ => none
    | .ok row =>
      match resolved : snapshot.definitions[snapshot.definitions.findIdx (·.name == signature.name)]? with
      | some (.function callee) =>
        if same : resolveProtocolSignature callee = .ok signature then
          some ⟨marked, row, callee, aligned, located, resolved, same⟩
        else none
      | _ => none

variable {parent : Frame} {source : List String} {signature : ProtocolSignature} {site : String}

def entered (call : CheckedCall snapshot parent source signature site) : Frame :=
  applicationFrame call.marked call.row (snapshot.definitions.findIdx (·.name == signature.name))

/-- The same lexical prefix works at another dynamic occurrence. Keep its
actual invocation in the callee's address, even when the labels agree. -/
def atInvocation (call : CheckedCall snapshot parent source signature site) (invocation : InvocationCoordinate) :
    CheckedCall snapshot {parent with invocation} source signature site where
  marked := {call.marked with invocation}
  row := call.row
  callee := call.callee
  aligned := by rw [OracleProtocol.advanceInvocation, call.aligned]; rfl
  located := call.located
  resolved := call.resolved
  signatureMatches := call.signatureMatches

theorem run {A : Type} (state : State) (labels : List (String × String))
    (call : CheckedCall snapshot state.frame (labels.map Prod.fst) signature site)
    (body : PIR.Process (OracleProtocol.Interface model) A) :
    ((withMarks labels (.done ())).bind (fun _ ↦ OracleProtocol.enter model (.application signature site) body)).runM
      action state = (do
        let result ← (body.bind fun value ↦ .call .leave fun _ ↦ .done value).runM action {state with
          frame := call.entered
          parents := call.marked :: state.parents}
        pure {result with events := labels.map (fun p ↦ .mark p.2) ++ result.events}) :=
  runMarkedApplication oracles ordinary base publish state labels signature site body
    call.aligned call.located call.resolved call.signatureMatches

end CheckedCall
end Zkc.Source.Structured.OraclePublication
