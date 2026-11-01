module

public import Zkc.Source.Structured.ContractInstantiation
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! Complete lexical call inventories of the existing typed protocol carrier.
An inventory element is structural evidence in Type, so it is both enumerable
and tied to the exact source tree. It is not an execution or reachability claim.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

/-- An exact typed call header and its actual SSA operands. -/
structure CallSite where
  context : List Ty
  signature : ProtocolSignature
  roles : List Nat
  site : String
  operands : Operands context signature.inputs

/-- Existential packaging of the canonical typed occurrence witness. -/
structure CallOccurrence {Γ out : List Ty} (body : Region protocolDialect Γ out) where
  callSite : CallSite
  occurrence : ApplicationOccurrence callSite.signature callSite.roles callSite.site
    callSite.operands body

/-- Forget only the additional checked role-substitution proof. The lexical
call and its path are the original canonical witness, not a second site proof. -/
def CheckedApplication.toCallOccurrence {snapshot : Snapshot} {imported : Imported snapshot}
    {callee : ContractBinding imported} {Γ : List Ty} (call : CheckedApplication callee Γ) :
    CallOccurrence call.caller.protocol.body :=
  ⟨⟨Γ, callee.protocol.signature, call.roles, call.site, call.operands⟩, call.occurrence⟩

/-- Recover the exact source continuation at the witnessed application, not
an arbitrary replacement suffix. Ancestor result contexts may differ. -/
def ApplicationOccurrence.continuation {signature : ProtocolSignature} {roles : List Nat}
    {site : String} {Γ : List Ty} {operands : Operands Γ signature.inputs} :
    {Δ out : List Ty} → {body : Region protocolDialect Δ out} →
      ApplicationOccurrence signature roles site operands body →
      Σ result, Region protocolDialect (signature.outputs ++ Γ) result
  | _, _, _, .here suffix => ⟨_, suffix⟩
  | _, _, _, .next _ _ _ _ occurrence => occurrence.continuation
  | _, _, _, .bindBody _ _ occurrence => occurrence.continuation
  | _, _, _, .bindNext _ _ occurrence => occurrence.continuation
  | _, _, _, .repeatBody _ _ _ _ _ occurrence => occurrence.continuation

namespace CallOccurrence

def continuation {Γ out} {body : Region protocolDialect Γ out} (call : CallOccurrence body) :=
  call.occurrence.continuation

/-- The local source subtree recovered from this inventory element. -/
def application {Γ out} {body : Region protocolDialect Γ out} (call : CallOccurrence body) :
    Region protocolDialect call.callSite.context call.continuation.1 :=
  .letOp (.protocolApply call.callSite.signature call.callSite.roles call.callSite.site)
    call.callSite.operands .nil call.continuation.2

/-- Canonical position, independent of callee names and runtime iterations. -/
def position {Γ out} {body : Region protocolDialect Γ out} (call : CallOccurrence body) : List Nat :=
  call.occurrence.position

/-- Enclosing lexical repeats and their static bounds, in outermost-first order. -/
def repeats {Γ out} {body : Region protocolDialect Γ out} (call : CallOccurrence body) :
    List (List Nat × Nat) := call.occurrence.repeats


def here {Γ out} (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out) :
    CallOccurrence (.letOp (.protocolApply signature roles site) operands .nil next) :=
  ⟨⟨Γ, signature, roles, site, operands⟩, .here next⟩

def next {Γ out} (op : ProtocolOp) (args : Operands Γ op.arguments)
    (bodies : Regions protocolDialect op.regions)
    (tail : Region protocolDialect (op.results ++ Γ) out) (call : CallOccurrence tail) :
    CallOccurrence (.letOp op args bodies tail) :=
  ⟨call.callSite, .next op args bodies tail call.occurrence⟩

def bindBody {Γ mid out} (body : Region protocolDialect Γ mid)
    (next : Region protocolDialect (mid ++ Γ) out) (call : CallOccurrence body) :
    CallOccurrence (.bind body next) :=
  ⟨call.callSite, .bindBody body next call.occurrence⟩

def bindNext {Γ mid out} (body : Region protocolDialect Γ mid)
    (next : Region protocolDialect (mid ++ Γ) out) (call : CallOccurrence next) :
    CallOccurrence (.bind body next) :=
  ⟨call.callSite, .bindNext body next call.occurrence⟩

def repeatBody {Γ out} (spec : RepeatSpec) (site : String)
    (args : Operands Γ (.index :: (spec.state ++ spec.captures)))
    (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
    (next : Region protocolDialect (spec.state ++ Γ) out) (call : CallOccurrence body) :
    CallOccurrence (.letOp (.repeat spec site) args (.cons body .nil) next) :=
  ⟨call.callSite, .repeatBody spec site args body next call.occurrence⟩

end CallOccurrence

/-- Only an actual application constructor contributes a call at this node. -/
def headCallInventory {Γ out} (op : ProtocolOp) (args : Operands Γ op.arguments)
    (bodies : Regions protocolDialect op.regions)
    (next : Region protocolDialect (op.results ++ Γ) out) :
    List (CallOccurrence (.letOp op args bodies next)) :=
  match op, args, bodies, next with
  | .protocolApply signature roles site, args, .nil, next =>
      [CallOccurrence.here signature roles site args next]
  | _, _, _, _ => []

/-- Repeat is the only protocol operation with a callback. Both bind children
and every continuation are traversed, independently of execution reachability. -/
def callInventory {Γ out} (body : Region protocolDialect Γ out) : List (CallOccurrence body) :=
  match body with
  | .ret _ | .stop _ => []
  | .letOp op args bodies next =>
      headCallInventory op args bodies next ++
      (callInventory next).map (CallOccurrence.next op args bodies next) ++
      (match op, args, bodies, next with
       | .repeat spec site, args, .cons body tail, next =>
           match tail with
           | .nil => (callInventory body).map (CallOccurrence.repeatBody spec site args body next)
       | _, _, _, _ => [])
  | .bind body next => (callInventory body).map (CallOccurrence.bindBody body next) ++
      (callInventory next).map (CallOccurrence.bindNext body next)

/-- Select one complete lexical occurrence by its exact callee signature and,
when needed, source path. Ambiguous matches remain unresolved. This query does
not assert that execution reaches the selected call. -/
def selectCall {Γ out} (body : Region protocolDialect Γ out)
    (signature : ProtocolSignature) (position : Option (List Nat) := none) :
    Option (CallOccurrence body) :=
  match (callInventory body).filter (fun call =>
      call.callSite.signature == signature &&
        position.all (fun path => call.position == path)) with
  | [call] => some call
  | _ => none

/-- Every canonical occurrence is in the computable inventory. -/
theorem callInventory_complete {Γ out} {body : Region protocolDialect Γ out}
    (call : CallOccurrence body) : call ∈ callInventory body := by
  rcases call with ⟨⟨context, signature, roles, site, operands⟩, occurrence⟩
  induction occurrence with
  | here next => simp [callInventory, headCallInventory, CallOccurrence.here]
  | next op args bodies tail occurrence ih =>
    unfold callInventory
    split
    all_goals exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨CallOccurrence.mk _ occurrence, ih, rfl⟩))
  | bindBody body next occurrence ih =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨CallOccurrence.mk _ occurrence, ih, rfl⟩)
  | bindNext body next occurrence ih =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨CallOccurrence.mk _ occurrence, ih, rfl⟩)
  | repeatBody spec site args body next occurrence ih =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨CallOccurrence.mk _ occurrence, ih, rfl⟩)

theorem CheckedApplication.toCallOccurrence_mem {snapshot : Snapshot}
    {imported : Imported snapshot} {callee : ContractBinding imported} {Γ : List Ty}
    (call : CheckedApplication callee Γ) :
    call.toCallOccurrence ∈ callInventory call.caller.protocol.body :=
  callInventory_complete _

/-- Erased enumeration remains sound and complete relative to structural
occurrence evidence. A wrong signature, operand, role map or path cannot appear
without an actual occurrence exposing exactly that data. -/
def callSites {Γ out} (body : Region protocolDialect Γ out) : List CallSite :=
  (callInventory body).map (fun call => call.callSite)

theorem mem_callSites_iff {Γ out} {body : Region protocolDialect Γ out}
    (site : CallSite) :
    site ∈ callSites body ↔ ∃ call : CallOccurrence body, call.callSite = site := by
  simp only [callSites, List.mem_map]
  constructor
  · rintro ⟨call, _, same⟩
    exact ⟨call, same⟩
  · rintro ⟨call, same⟩
    exact ⟨call, callInventory_complete call, same⟩

/-- A computable public projection retains the exact lexical address. -/
def locatedCallSites {Γ out} (body : Region protocolDialect Γ out) : List (List Nat × CallSite) :=
  (callInventory body).map (fun call => (call.position, call.callSite))

theorem mem_locatedCallSites_iff {Γ out} {body : Region protocolDialect Γ out}
    (position : List Nat) (site : CallSite) :
    (position, site) ∈ locatedCallSites body ↔
      ∃ call : CallOccurrence body, call.position = position ∧ call.callSite = site := by
  simp only [locatedCallSites, List.mem_map]
  constructor
  · rintro ⟨call, _, same⟩
    exact ⟨call, (Prod.mk.inj same).1, (Prod.mk.inj same).2⟩
  · rintro ⟨call, positionEq, siteEq⟩
    exact ⟨call, callInventory_complete call, by rw [positionEq, siteEq]⟩

/-- The selected consumer supplies the type of each local request. Enumerating
calls never manufactures evidence, even for a callee with no declared clauses. -/
abbrev CallObligations {Γ out} (body : Region protocolDialect Γ out)
    (Request : CallOccurrence body → Sort _) :=
  (call : {call : CallOccurrence body // call ∈ callInventory body}) → Request call.val

/-- Resolution is available at every actual call because inventory is complete. -/
def CallObligations.resolve {Γ out} {body : Region protocolDialect Γ out}
    {Request : CallOccurrence body → Sort _} (resolved : CallObligations body Request)
    (call : CallOccurrence body) : Request call :=
  resolved ⟨call, callInventory_complete call⟩

/-- Distinct repeat indices produce distinct logical invocation coordinates.
This is injectivity of labels, not evidence that an execution reached either
index. Retained repeat intentionally reuses the operational context. -/
theorem CheckedApplication.childInvocation_iterations_injective
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} (call : CheckedApplication callee Γ) (parent : InvocationCoordinate) :
    Function.Injective (call.childInvocation parent) := by
  intro left right same
  have frames := congrArg InvocationCoordinate.frames same
  change parent.frames ++ List.ofFn _ ++ _ = parent.frames ++ List.ofFn _ ++ _ at frames
  have repeated := List.append_cancel_left (List.append_cancel_right frames)
  have functions := List.ofFn_injective repeated
  funext index
  have one := congrFun functions index
  exact Fin.ext (InvocationFrame.iteration.inj one).2.2

end Zkc.Source.Structured
