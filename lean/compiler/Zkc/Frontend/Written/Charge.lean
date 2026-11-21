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

/-- The names of the sites that the contract of an instance's declaration charges, each with
the place of its clause, and the name and the place of the declaration. -/
def chargedSites (s : Compile.State) (owner : InstanceId) :
    ExportM (Array (Array String × Syntax.Span) × String × Syntax.Span) := do
  let some entry := s.table.entries[owner]? | throw "missing charge instance"
  let some declaration := s.program.declarations[entry.key.declaration]?
    | throw "missing charge declaration"
  let place := (declaration.name.map (·.span)).getD default
  let charged := (← contractOf s entry.key.declaration place).filterMap fun
    | .charge span site _ => some (site.names.map (·.text), span)
    | _ => none
  return (charged, s.program.nameOf entry.key.declaration, place)

/-- Whether the one event of a declaration that a site names is a draw. -/
def namesDraw (s : Compile.State) (owner : InstanceId) (name : String) : ExportM Bool := do
  let some entry := s.table.entries[owner]? | throw "missing charge instance"
  let some {content := .protocol head .., ..} := s.env.modules.lowered? entry.key.declaration
    | throw "expected a resolved protocol"
  let #[(source, _)] := head.events.zipIdx.filter (fun (e, _) => e.name == some name)
    | throw s!"expected one source event named {name}"
  return source.audience matches .transfer _ (some _)

/-- The charged draws of a use by the names of their sites: each name with the keys of the
draws that realize it (one, or one for each block of a stepped loop). -/
abbrev SiteKeys := List (String × List Core.Key)

/-- The use of a definition at its proof arguments, in a table under construction: its place.
A use that the table has is found again, so two applications that give a callee the same proof
arguments are calls of one use. The calls of a new use are the applications of the stored
definition, in the order of its body, each with the use of its callee at the proof arguments of
that application; its draws are the realizations of the draws that the contract of its
definition charges, at the cap that the charge has at these proof arguments. The counts are
those of the stored body. -/
partial def capsOfUse (c : AdmittedRoot) (subject : ProofSubject) :
    StateT (Array (ProofSubject × UseCaps × SiteKeys)) ExportM Nat := do
  if let some place := (← get).findIdx? (·.1 == subject) then return place
  let named := (c.emission.package ⟨[], [], [], [], []⟩).named
  let some (.protocol _ _ _ _ body) := named.definitions.find? (·.key.number == subject.protocol)
    | throw "WK-CHARGE: a use of the table is of no protocol of the package"
  let found := body.counted (some 1)
  let (charged, name, place) ← chargedSites c.state subject.protocol
  let mut calls : Array CallCap := #[]
  for (key, operation, count) in found do
    let .apply _ _ := operation | continue
    let some count := count
      | refuse place "WK-CHARGE" (s!"an application in `{name}` is under a loop whose count is read " ++
          s!"at run time, or in an attempt (instruction {key.number}): it has no count in a table " ++
          "of caps yet")
    let child ← subject.child c key
    calls := calls.push ⟨key, count, ← capsOfUse c child⟩
  -- a site has one cap: a second charge on it is refused before any charge is read
  let mut capped : Array (Array String) := #[]
  for (names, span) in charged do
    if capped.contains names then
      refuse span "WK-CHARGE"
        s!"a second charge on `sites.{".".intercalate names.toList}`: a site has one cap"
    capped := capped.push names
  let mut draws : Array DrawCap := #[]
  let mut sites : SiteKeys := []
  for (names, span) in charged do
    let #[site] := names
      | refuse span "WK-CHARGE" "a charge on a site of a callee is not in a table of caps yet"
    unless ← namesDraw c.state subject.protocol site do
      refuse span "WK-CHARGE" (s!"`sites.{site}` is no draw: a charge on an application or an " ++
        "attempt is not in a table of caps yet")
    let charge ← drawCharge c.state c.evidence.admitted.program ⟨subject.protocol⟩ site
      subject.specification
    for (_, key) in charge.draws do
      let some (_, _, some count) := found.find? (·.1 == key)
        | refuse span "WK-CHARGE" (s!"the draw `{site}` of `{name}` is under a loop whose count is " ++
            "read at run time, or in an attempt: it has no count in a table of caps yet")
      draws := draws.push ⟨key, charge.numerator, charge.denominator, count⟩
    sites := sites ++ [(site, charge.draws.map (·.2))]
  modify (·.push (subject, ⟨⟨subject.protocol⟩, draws.toList, calls.toList⟩, sites))
  return (← get).size - 1

/-- The draws of the root by the names that the source gives them, each with the keys of the
draws that realize it (one, or one for each block of a stepped loop): every draw that has a
name and is emitted, whether the contract charges it or not. A draw of a loop that does not
run is realized by no instruction and has no name here. -/
def drawSites (c : AdmittedRoot) : ExportM SiteKeys := do
  let s := c.state
  let some entry := s.table.entries[c.id]? | throw "missing root instance"
  let some {content := .protocol head .., ..} := s.env.modules.lowered? entry.key.declaration
    | throw "expected a resolved protocol"
  let some (.protocol code) := s.results.body? c.id | throw "missing elaborated root"
  let some addresses := Emit.SiteAddresses.forProtocol c.evidence.admitted.program ⟨c.id⟩
    | throw "missing admitted root"
  let mut sites : SiteKeys := []
  for (source, event) in head.events.zipIdx do
    let some name := source.name | continue
    let .transfer _ (some _) := source.audience | continue
    let occurrences := Typing.SiteEntry.realizations code.sites event "value"
    let some draws := occurrences.toList.mapM addresses.resolve
      | throw s!"ambiguous or missing address of the draw {name}"
    unless draws.isEmpty do sites := sites ++ [(name, draws.map (·.2))]
  return sites

/-- **The table of caps of a goal's root** (SX8): the uses that the root reaches at the goal's
proof arguments, callees first and the root's last, each with the caps that the contract of its
definition gives its charged draws at the proof arguments of that use. No caller names a draw:
the table is of every charge that the root reaches. With it, the draws of the root by the names
of their sites (`drawSites`), for a text that names a draw as the source does. -/
def goalCaps (c : AdmittedRoot) (specification : Array Nat) : ExportM (CapTable × SiteKeys) := do
  let (_, uses) ← (capsOfUse c ⟨c.id, specification⟩).run #[]
  return (⟨uses.toList.map (·.2.1)⟩, ← drawSites c)

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
