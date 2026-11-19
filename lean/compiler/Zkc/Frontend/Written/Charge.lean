module

public import Zkc.Frontend.Written.ChargeData
public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Written.Root

@[expose] public section
namespace Zkc.Frontend.Written

structure DeclaredDraw where
  event : Nat
  ceiling : Rat

/-- Resolve the authored clause in its closed instance, before looking up realized addresses. -/
def declaredDraw (s : Compile.State) (owner : Core.Key) (name : String)
    (specification : Array Nat := #[]) : ExportM DeclaredDraw := do
  let some entry := s.table.entries[owner.number]? | throw "missing charge instance"
  let id := entry.key.declaration
  let some decl := s.program.declarations[id]? | throw "missing charge declaration"
  let some {content := .protocol head .., ..} := s.env.modules.lowered? id
    | throw "expected a resolved protocol"
  let #[(source, event)] := head.events.zipIdx.filter (fun (e, _) => e.name == some name)
    | throw s!"expected one source event named {name}"
  let .transfer _ (some _) := source.audience | throw s!"{name} is not a draw"
  let #[bound] := (← contractOf s id source.span).filterMap (fun
    | .charge _ site expr => if site.names.map (·.text) == #[name] then some expr else none
    | _ => none) | throw s!"expected one charge on sites.{name}"
  unless (Static.specificationParameters s.program decl).size == specification.size do
    refuse bound.span "SP11" "the selected charge requires its proof arguments"
  let env := Static.instanceEnv s.program decl entry.key.arguments specification
  let (result, after) := (Static.evalRational env bound).run sourceContext s
  let .ok amount := result | do
    let diagnostics := after.log.entries.extract s.log.entries.size after.log.entries.size
    let messages := diagnostics.toList.map (·.render after.env.renderer)
    throw s!"{location bound.span}: cannot close the rational ceiling: {String.intercalate "; " messages}"
  if amount.num < 0 then throw "a draw ceiling must be nonnegative"
  return ⟨event, amount⟩

/-- A zero-trip loop retains its declaration. Every realized draw must have a unique address. -/
def drawCharge {V : Core.Vocabulary} (s : Compile.State) (program : Core.Typed V)
    (owner : Core.Key) (name : String) (specification : Array Nat := #[]) : ExportM DrawCharge := do
  let ⟨event, amount⟩ ← declaredDraw s owner name specification
  let some (.protocol code) := s.results.body? owner.number | throw "missing elaborated charge owner"
  let some addresses := Emit.SiteAddresses.forProtocol program owner | throw "missing admitted charge owner"
  let occurrences := Typing.SiteEntry.realizations code.sites event "value"
  let some draws := occurrences.toList.mapM addresses.resolve | throw "ambiguous or missing draw address"
  return ⟨owner,amount.num.toNat,amount.den,draws⟩

/-- Follow an emitted application instruction, evaluating its retained lexical closure in
the proof environment of this use of the caller. -/
def ProofSubject.child (parent : ProofSubject) (c : AdmittedRoot) (site : Core.Key) :
    ExportM ProofSubject := do
  let #[origin] := c.emission.origins.filter (·.definition.number == parent.protocol)
    | throw "missing caller in the root emission"
  let #[call] := origin.specification.filter (·.instruction == site)
    | throw "expected an application at the selected instruction"
  let some closure := call.proofArguments | return ⟨call.callee, #[]⟩
  let s := c.state
  let some key := s.results.key? parent.protocol | throw "missing calling instance"
  let some decl := s.program.declarations[key.declaration]? | throw "missing calling declaration"
  let parameters := Static.specificationParameters s.program decl
  unless parameters.size == parent.specification.size do throw "SP11: missing caller proof arguments"
  let inherited := (parameters.zip parent.specification).foldl (init := {}) fun env ((ref, _), n) =>
    env.insert ref (.natural n)
  let place := (decl.name.map (·.span)).getD default
  let (values, _) ← evaluate s place (closure.close call.callee inherited place)
  return ⟨call.callee, values⟩

/-- The named request selects the deployed root even in an assembly with several schemes. -/
def admitSoundnessGoal (assembly : Assembly) (name : String) : ExportM AdmittedRoot := do
  let (selected, state) ← selectNamedGoal (← sourceState assembly) name .soundness
  admitInstance state selected.scheme.protocol selected.scheme.span

/-- Read the charge at a path of application instructions from the named goal's root. -/
def goalDrawCharge (c : AdmittedRoot) (goal : String) (path : List Core.Key) (draw : String) :
    ExportM DrawCharge := do
  let (selected, _) ← selectNamedGoal c.state goal .soundness
  unless selected.scheme.protocol == c.id do throw "GL3: goal selects a different protocol"
  let root := ProofSubject.mk c.id selected.specification
  let subject ← path.foldlM (fun parent site => parent.child c site) root
  drawCharge c.state c.evidence.admitted.program ⟨subject.protocol⟩ draw subject.specification

end Zkc.Frontend.Written
