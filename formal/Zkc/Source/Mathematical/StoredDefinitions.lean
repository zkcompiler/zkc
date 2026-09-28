import Zkc.Source.Mathematical.ProtocolMeaning
import Zkc.Source.Mathematical.ProtocolAdmission
import Zkc.Source.Mathematical.CapabilityRoots
import Zkc.Source.Mathematical.ProtocolInvocations

/-! Stored acyclic definitions with explicit, fixed root bindings.

Each stored target is already instantiated in one role/type coordinate system.
Calls select earlier targets and must pass exactly their stored root tuple.
This is the execution table after source closure; constructing that table from
raw calls (including role/static substitution) remains a separate check. The
proof table appends callees before callers. A raw closure keeps its specified
instance IDs and supplies a checked mapping into this table; this definition
does not prescribe reordering the native graph or its canonical bytes.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}

structure Target (Role : Type) (vocabulary : Vocabulary) where
  parties : List Role
  capabilities : List (Capability Role vocabulary.Service)
  arguments : List (Port Role vocabulary.Ty)
  results : List (Port Role vocabulary.Ty)

def Target.signature (target : Target Role vocabulary) : Signature Role vocabulary :=
  ⟨target.parties, target.capabilities.map Capability.toPermission, target.arguments, target.results⟩

def targetRoots : {targets : List (Target Role vocabulary)} → {signature : Signature Role vocabulary} →
    Var (targets.map Target.signature) signature → List Nat
  | target :: _, _, .here => target.capabilities.map Capability.root
  | _ :: _, _, .there reference => targetRoots reference

def Program.callsMatch {parties capabilities scope Γ results start finish}
    (roots : {signature : Signature Role vocabulary} → Var scope signature → List Nat) :
    Program parties vocabulary capabilities scope Γ results start finish → Bool
  | .ret _ | .stop .. => true
  | .pure _ _ next | .local _ _ _ _ _ _ next | .query _ _ _ _ _ _ next |
    .guard _ _ _ next | .message _ _ _ _ _ _ _ next => next.callsMatch roots
  | .invoke callee _ bindings _ next => bindings.roots == roots callee && next.callsMatch roots
  | .repeat _ _ _ body next => body.callsMatch roots && next.callsMatch roots

theorem Program.callsMatch_iff {parties capabilities scope Γ results start finish}
    (roots : {signature : Signature Role vocabulary} → Var scope signature → List Nat)
    (program : Program parties vocabulary capabilities scope Γ results start finish) :
    program.callsMatch roots = true ↔ program.CallsSatisfy (fun callee bindings => bindings.roots = roots callee) := by
  induction program <;> simp_all [Program.callsMatch, Program.CallsSatisfy, Bool.and_eq_true, beq_iff_eq]

/-- Each body sees the prefix of the proof table containing its callees. -/
inductive Definitions (table : List (Capability Role vocabulary.Service)) : List (Target Role vocabulary) → Type where
  | nil : Definitions table []
  | snoc {targets : List (Target Role vocabulary)} (previous : Definitions table targets)
      (target : Target Role vocabulary) {finish : Nat}
      (body : Program target.parties vocabulary target.capabilities
        (targets.map Target.signature) target.arguments target.results 0 finish)
      (rooted : Rooted table target.capabilities)
      (roots : body.rootsValid = true)
      (bindings : body.callsMatch targetRoots = true) : Definitions table (targets ++ [target])

/-- Calls in the actual stored bodies, in execution-table order. Repeats keep
one syntactic copy of their body, including when the count is zero. -/
def Definitions.invocationTable {table : List (Capability Role vocabulary.Service)} :
    {targets : List (Target Role vocabulary)} → Definitions table targets → List (List Invocation)
  | _, .nil => []
  | _, .snoc previous _ body _ _ _ => previous.invocationTable ++ [body.invocations]

def Definitions.reindex {table : List (Capability Role vocabulary.Service)}
    {first second : List (Target Role vocabulary)} (same : first = second)
    (definitions : Definitions table first) : Definitions table second := same ▸ definitions

theorem Definitions.invocationTable_reindex {table : List (Capability Role vocabulary.Service)}
    {first second : List (Target Role vocabulary)} (same : first = second)
    (definitions : Definitions table first) :
    (definitions.reindex same).invocationTable = definitions.invocationTable := by
  cases same
  rfl

abbrev StoredMeanings (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (targets : List (Target Role vocabulary)) :=
  {capabilities : List (Capability Role vocabulary.Service)} →
    CheckedCallMeaning (capabilities := capabilities) meaning self (targets.map Target.signature)
      (fun callee bindings => bindings.roots = targetRoots callee)

def appendMeaning (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (last : Target Role vocabulary)
    (value : {capabilities : List (Capability Role vocabulary.Service)} →
      (bindings : CapabilityBindings capabilities last.signature.capabilities) →
      bindings.roots = last.capabilities.map Capability.root → List LocatedExecution.Frame →
      Values (Component meaning.Value self) last.arguments →
      PIR.Proc (interface self vocabulary meaning.Value) (Values (Component meaning.Value self) last.results)) :
    {targets : List (Target Role vocabulary)} → StoredMeanings meaning self targets →
      StoredMeanings meaning self (targets ++ [last])
  | [], _, _, _, .here => value
  | _ :: _, env, _, _, .here => env .here
  | _ :: _, env, _, _, .there reference => appendMeaning meaning self last value (fun ref => env (.there ref)) reference

/-- References to an appended definition and to a preserved prefix. These
constructors share the execution table's existing declaration order. -/
def lastReference (last : Target Role vocabulary) : (targets : List (Target Role vocabulary)) →
    Var ((targets ++ [last]).map Target.signature) last.signature
  | [] => .here
  | _ :: rest => .there (lastReference last rest)

def prefixReference {last : Target Role vocabulary} : {targets : List (Target Role vocabulary)} →
    {signature : Signature Role vocabulary} → Var (targets.map Target.signature) signature →
    Var ((targets ++ [last]).map Target.signature) signature
  | _ :: _, _, .here => .here
  | _ :: _, _, .there reference => .there (prefixReference reference)

omit [DecidableEq Role] in
theorem reference_append_cases {last : Target Role vocabulary} {targets : List (Target Role vocabulary)}
    {signature : Signature Role vocabulary}
    (reference : Var ((targets ++ [last]).map Target.signature) signature) :
    (∃ same : last.signature = signature, reference = same ▸ lastReference last targets) ∨
      ∃ earlier, reference = prefixReference earlier := by
  induction targets with
  | nil => cases reference with
    | here => exact Or.inl ⟨rfl, rfl⟩
    | there reference => nomatch reference
  | cons first rest ih =>
    cases reference with
    | here => exact Or.inr ⟨.here, rfl⟩
    | there reference =>
      rcases ih reference with ⟨same, equal⟩ | ⟨earlier, equal⟩
      · cases same; cases equal; exact Or.inl ⟨rfl, rfl⟩
      · cases equal; exact Or.inr ⟨.there earlier, rfl⟩

omit [DecidableEq Role] in
theorem lastReference_index (last : Target Role vocabulary) (targets : List (Target Role vocabulary)) :
    (lastReference last targets).index = targets.length := by
  induction targets <;> simp_all [lastReference, Var.index]

omit [DecidableEq Role] in
theorem prefixReference_index {last : Target Role vocabulary} {targets : List (Target Role vocabulary)}
    {signature : Signature Role vocabulary} (reference : Var (targets.map Target.signature) signature) :
    (prefixReference (last := last) reference).index = reference.index := by
  induction targets generalizing signature with
  | nil => nomatch reference
  | cons first rest ih =>
    cases reference with
    | here => rfl
    | there reference => exact congrArg (· + 1) (ih reference)

omit [DecidableEq Role] in
theorem targetRoots_last (last : Target Role vocabulary) (targets : List (Target Role vocabulary)) :
    targetRoots (lastReference last targets) = last.capabilities.map Capability.root := by
  induction targets with
  | nil => rfl
  | cons first rest ih => exact ih

omit [DecidableEq Role] in
theorem targetRoots_prefix {last : Target Role vocabulary} {targets : List (Target Role vocabulary)}
    {signature : Signature Role vocabulary} (reference : Var (targets.map Target.signature) signature) :
    targetRoots (prefixReference (last := last) reference) = targetRoots reference := by
  induction targets generalizing signature with
  | nil => nomatch reference
  | cons first rest ih =>
    cases reference with
    | here => rfl
    | there reference => exact ih reference

omit [DecidableEq Role] in
theorem appendMeaning_last (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (last : Target Role vocabulary) (value) (targets : List (Target Role vocabulary))
    (earlier : StoredMeanings meaning self targets) {capabilities}
    (bindings : CapabilityBindings capabilities last.signature.capabilities)
    (roots : bindings.roots = targetRoots (lastReference last targets)) (path) (arguments) :
    appendMeaning meaning self last value earlier (lastReference last targets) bindings roots path arguments =
      value bindings (roots.trans (targetRoots_last last targets)) path arguments := by
  induction targets with
  | nil => rfl
  | cons first rest ih => exact ih (fun ref => earlier (.there ref)) _

omit [DecidableEq Role] in
theorem appendMeaning_prefix (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (last : Target Role vocabulary) (value) {targets : List (Target Role vocabulary)}
    (earlier : StoredMeanings meaning self targets) {signature}
    (reference : Var (targets.map Target.signature) signature) {capabilities}
    (bindings : CapabilityBindings capabilities signature.capabilities)
    (roots : bindings.roots = targetRoots (prefixReference (last := last) reference)) (path) (arguments) :
    appendMeaning meaning self last value earlier (prefixReference reference) bindings roots path arguments =
      earlier reference (bindings) (roots.trans (targetRoots_prefix reference)) path arguments := by
  induction targets generalizing signature with
  | nil => nomatch reference
  | cons first rest ih =>
    cases reference with
    | here => rfl
    | there reference => exact ih (fun ref => earlier (.there ref)) reference bindings roots arguments

/-- Only exact stored root bindings can enter a callee. The contract proof is
consumed before execution; there is no runtime root-mismatch refusal branch. -/
def Definitions.denote (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    {table : List (Capability Role vocabulary.Service)} :
    {targets : List (Target Role vocabulary)} → Definitions table targets → StoredMeanings meaning self targets
  | _, .nil => fun ref => nomatch ref
  | _, .snoc previous target body _ _ valid =>
      let earlier : StoredMeanings meaning self _ := previous.denote meaning self
      appendMeaning meaning self target (fun _ _ path arguments =>
        body.denoteChecked meaning self earlier path ((body.callsMatch_iff targetRoots).mp valid)
          (fun ref => arguments.get ref)) earlier

theorem Definitions.denote_reindex (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    {table : List (Capability Role vocabulary.Service)} {first second : List (Target Role vocabulary)}
    (same : first = second) (definitions : Definitions table first) {signature}
    (reference : Var (second.map Target.signature) signature) {capabilities}
    (bindings : CapabilityBindings capabilities signature.capabilities)
    (roots : bindings.roots = targetRoots reference) (path) (arguments) :
    (definitions.reindex same).denote meaning self reference bindings roots path arguments =
      definitions.denote meaning self (same.symm ▸ reference) bindings
        (by cases same; exact roots) path arguments := by
  cases same
  rfl

/-- An entry points at a stored target, so that target's direct root obligations
are already discharged. Its actual table bindings must match the target exactly. -/
structure Entry (table : List (Capability Role vocabulary.Service)) (targets : List (Target Role vocabulary))
    (index : Nat) (indices : List Nat) where
  signature : Signature Role vocabulary
  target : Var (targets.map Target.signature) signature
  targetIndex : target.index = index
  bindings : CapabilityBindings table signature.capabilities
  bindingIndices : bindings.indices = indices
  roots : bindings.roots = targetRoots target

def entry [DecidableEq vocabulary.Service]
    (table : List (Capability Role vocabulary.Service)) (targets : List (Target Role vocabulary))
    (index : Nat) (indices : List Nat) : StateT Nat (Except Error) (Entry table targets index indices) := do
  let cost := 1 + targets.length + min index targets.length + indices.length * (table.length + 1)
  let remaining ← get
  if cost > remaining then throw .resource
  set (remaining - cost)
  let target ← (Graph.select (targets.map Target.signature) index).mapError Error.graph
  let bindings ← selectCapabilities table target.ty.capabilities indices
  if roots : bindings.val.roots = targetRoots target.value then
    return ⟨target.ty, target.value, target.erasure, bindings.val, bindings.property, roots⟩
  else throw .alias

/-- The source-facing wrapper must instantiate `table` with its admitted
header's capabilities and retain source-instance/call-edge provenance. -/
structure Closed (table : List (Capability Role vocabulary.Service)) where
  rootTable : RootTable table
  targets : List (Target Role vocabulary)
  definitions : Definitions table targets
  entryIndex : Nat
  rootIndices : List Nat
  entry : Entry table targets entryIndex rootIndices

def Closed.denote {table : List (Capability Role vocabulary.Service)} (closed : Closed table)
    (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (arguments : Values (Component meaning.Value self) closed.entry.signature.arguments) :=
  closed.definitions.denote meaning self closed.entry.target closed.entry.bindings closed.entry.roots [] arguments

/-- A successful call-closure check proves the concrete root tuple expected
by the selected stored target, including all aliases. -/
theorem Program.call_roots {parties capabilities scope Γ results site finish signature}
    (callee : Var scope signature) (participates : ∀ role ∈ signature.parties, role ∈ parties)
    (binding : CapabilityBindings capabilities signature.capabilities)
    (arguments : Bindings Γ signature.arguments)
    (next : Program parties vocabulary capabilities scope (signature.results ++ Γ) results (site + 1) finish)
    (roots : {signature : Signature Role vocabulary} → Var scope signature → List Nat)
    (valid : (Program.invoke callee participates binding arguments next).callsMatch roots = true) :
    binding.roots = roots callee := by
  simp only [Program.callsMatch, Bool.and_eq_true, beq_iff_eq] at valid
  exact valid.1

end Zkc.Source.Mathematical.Protocol
