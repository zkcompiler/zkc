module

public import ZkcTools.StructuredSource.Bindings.Calls
public import ZkcTools.StructuredSource.Bindings.Helpers
public import ZkcTools.StructuredSource.LibraryAssociation

@[expose] public section

/-! Bounded candidate queries over the existing checked tables and normal form.
These functions retrieve syntax; generated body and occurrence equations remain
the authority. There is no registry, source evaluator or additional proof IR. -/
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings

/-- Origins include all typed static arguments. The existing metadata join is
only candidate retrieval; normalizer/source equations check the selected body. -/
def uniqueProtocol (program : Program) (origin : ProtocolOrigin) : Except String Nat := do
  let mut candidates := []
  for (definition, index) in program.payload.protocols.zipIdx do
    let found ← ZkcTools.StructuredSource.LibraryAssociation.originFor program.snapshot definition
    if found == origin then candidates := candidates ++ [index]
  uniqueCandidate "source-protocol-ambiguous-or-missing" candidates

def sourceSignature (program : Program) : Signature :=
  ⟨[], false, false, program.payload.definitions.map (·.helper), keys program⟩

/-- Helper occurrences along the same pure prefix supported by callSplitSource.
Stop at every effect, branch, repeat or protocol application. -/
def prefixHelpers {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty} :
    {scope : Scope} → Form laws callees scope outputs → List Helper
  | _, .owned _ helper _ next | _, .math helper _ next | _, .strict helper _ next =>
      helper :: prefixHelpers next
  | _, .compute _ _ _ next | _, .byLaw _ _ next => prefixHelpers next
  | _, _ => []

/-- Select the prefix immediately following the first repeat on a pure spine.
Branches and effects are refused rather than silently skipped. -/
def afterRepeatHelpers {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty} :
    {scope : Scope} → Form laws callees scope outputs → Except String (List Helper)
  | _, .repeat _ _ _ _ _ _ next => pure (prefixHelpers next)
  | _, .owned _ _ _ next | _, .math _ _ next | _, .strict _ _ next |
      _, .compute _ _ _ next | _, .byLaw _ _ next => afterRepeatHelpers next
  | _, _ => throw "source-linear-repeat-required"

/-- The first application after a pure prefix, with its full callee key and
actual site. A label is never needed to discover this occurrence. -/
def prefixApplication {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty} :
    {scope : Scope} → Form laws callees scope outputs → Option (CalleeKey × String)
  | _, .apply callee _ _ site _ _ => some (calleeAt callees callee, site)
  | _, .owned _ _ _ next | _, .math _ _ next | _, .strict _ _ next |
      _, .compute _ _ _ next | _, .byLaw _ _ next => prefixApplication next
  | _, _ => none

structure SelectedCallback where
  protocolIndex : Nat
  callbackIndex : Nat
  callback : RepeatSite

/-- Callback selection uses its full retained typed descriptor. Equal candidates
remain ambiguous even when their callback bodies happen to be identical. -/
def uniqueCallback (program : Program) (protocolIndex : Nat) (predicate : RepeatSite → Bool) :
    Except String SelectedCallback := do
  let some definition := program.payload.protocols[protocolIndex]? | throw "source-protocol-index"
  let (callback, index) ← uniqueCandidate "source-callback-ambiguous-or-missing"
    ((callbacks definition.body).zipIdx.filter fun (callback, _) => predicate callback)
  return ⟨protocolIndex, index, callback⟩

/-- Select a callback by its actual first normalized call, including the full
callee signature and role. No source label or protocol spelling is built in. -/
def callbackCalling (program : Program) (protocolIndex role : Nat) (callee : ProtocolSignature)
    (calleeRole : Nat := role) :
    Except String (SelectedCallback × String) := do
  let some definition := program.payload.protocols[protocolIndex]? | throw "source-protocol-index"
  unless role < definition.roles.length do throw "source-role-index"
  let mut candidates := []
  for (callback, index) in (callbacks definition.body).zipIdx do
    let form ← normalize (sourceSignature program) callback.body role definition.roles.length
      (optionalPattern (.index :: (callback.spec.state ++ callback.spec.captures)))
    if let some (key, site) := prefixApplication form then
      if key.signature == callee && key.role == calleeRole then
        candidates := candidates ++ [(SelectedCallback.mk protocolIndex index callback, site)]
  uniqueCandidate "source-callback-call-ambiguous-or-missing" candidates

end ZkcTools.StructuredSource.Bindings
