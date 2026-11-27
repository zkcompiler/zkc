module

public import Zkc.Subject.Charges
public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Written.Root

@[expose] public section
namespace Zkc.Frontend.Written
open Zkc.Subject

structure DeclaredDraw where
  event : Nat
  ceiling : Rat

/-- The rational total at the root: the bound of a goal that writes no ceiling (GL4). -/
def _root_.Zkc.Subject.CapTable.ratio (table : CapTable) : Rat := table.totalAt Rat table.root

/-- The amount of a charge of a definition at its proof arguments. It is not negative. -/
def chargeAmount (s : Compile.State) (owner : Core.Key) (amount : Lowered.Expr)
    (specification : Array Nat) : ExportM Rat := do
  let some instanceKey := s.table.allocatedKey? owner.number | throw "missing charge instance"
  let some decl := s.program.declarations[instanceKey.declaration]? | throw "missing charge declaration"
  unless (Static.specificationParameters s.program decl).size == specification.size do
    refuse amount.span "SP11" "the selected charge requires its proof arguments"
  let env := Static.instanceEnv s.program decl instanceKey.arguments specification
  let (value, _) ← evaluate s amount.span (Static.evalRational env amount)
  if value.num < 0 then refuse amount.span "WK-CHARGE" "a charge is not negative"
  if value > 1 then refuse amount.span "WK-CHARGE" s!"a charge is a probability, at most one; this one is {value}"
  return value

/-- Resolve the authored clause in its closed instance, before looking up realized addresses. -/
def declaredDraw (s : Compile.State) (owner : Core.Key) (name : String)
    (specification : Array Nat := #[]) : ExportM DeclaredDraw := do
  let some instanceKey := s.table.allocatedKey? owner.number | throw "missing charge instance"
  let id := instanceKey.declaration
  let some {content := .protocol head .., ..} := s.env.modules.lowered? id
    | throw "expected a resolved protocol"
  let #[(source, event)] := head.events.zipIdx.filter (fun (e, _) => e.name == some name)
    | throw s!"expected one source event named {name}"
  let .transfer _ (some _) := source.audience | throw s!"{name} is not a draw"
  let #[bound] := (← contractOf s id source.span).filterMap (fun
    | .charge _ site expr => if site.names.map (·.text) == #[name] then some expr else none
    | _ => none) | throw s!"expected one charge on sites.{name}"
  return ⟨event, ← chargeAmount s owner bound specification⟩

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
the place of its clause and its amount, and the name and the place of the declaration. -/
def chargedSites (s : Compile.State) (owner : InstanceId) :
    ExportM (Array (Array String × Syntax.Span × Lowered.Expr) × String × Syntax.Span) := do
  let some instanceKey := s.table.allocatedKey? owner | throw "missing charge instance"
  let some declaration := s.program.declarations[instanceKey.declaration]?
    | throw "missing charge declaration"
  let place := (declaration.name.map (·.span)).getD default
  let charged := (← contractOf s instanceKey.declaration place).filterMap fun
    | .charge span site amount => some (site.names.map (·.text), span, amount)
    | _ => none
  return (charged, s.program.nameOf instanceKey.declaration, place)

/-- **The site of a charge**: the kind of the one event of a declaration that `name` names. The
kind is the declaration's (`SourceEvent.kind`), the same for every instance and for an event of a
loop that does not run. A name that names no one event of the declaration is an error of the
source at the charge. -/
def siteKind (s : Compile.State) (declaration : DeclarationId) (place : Syntax.Span) (path name : String) :
    ExportM SourceEventKind := do
  let some {content := .protocol head .., ..} := s.env.modules.lowered? declaration
    | throw "expected a resolved protocol"
  let #[source] := head.events.filter (·.name == some name)
    | refuse place "WK-CHARGE"
        s!"`sites.{path}`: `{name}` names no one event of `{s.program.nameOf declaration}`"
  return source.kind

/-- What a charge is on: a draw of the charging declaration, or what a table of caps has no place
for yet. -/
inductive ChargedSite where
  | draw (name : String)
  | limit (message : String)

/-- **What a charge of a declaration is on** (SX8: a charge belongs to a draw, an application or
an attempt). A path goes through applications, each determined by its text, to a draw, an
application or an attempt of the last. Every other site is an error of the source at the
charge, whatever loops stand around it:

| the site | alone | before the end of a path |
|---|---|---|
| a draw | the draw | an error: no application |
| an application | a limit | the path goes on in its callee |
| an attempt | a limit | an error: no application |
| a send, an oracle send, a query, an opening, a sample | an error | an error: no application |
| no event, or several, of the name | an error | an error |

An application whose callee the text does not determine (a protocol given through a parameter)
has sites that are not read here: a path through it is refused in those words, and is no limit. -/
def chargedSite (s : Compile.State) (declaration : DeclarationId) (place : Syntax.Span)
    (names : Array String) : ExportM ChargedSite := do
  let path := ".".intercalate names.toList
  let mut at_ := declaration
  for (name, i) in names.toList.zipIdx do
    let kind ← siteKind s at_ place path name
    let last := i + 1 == names.size
    let other (what : String) : ExportM PUnit :=
      if last then
        refuse place "WK-CHARGE"
          s!"`sites.{path}` is {what}; a charge belongs to a draw, an application or an attempt"
      else refuse place "WK-CHARGE" s!"`sites.{path}`: `{name}` is no application, and has no sites"
    match kind with
    | .draw => unless last do other "a draw"
    | .attempt => unless last do other "an attempt"
    | .application callee =>
      unless last do
        let some callee := callee
          | refuse place "WK-CHARGE" (s!"`sites.{path}`: the protocol that `{name}` applies is given " ++
              "through a parameter, and its sites are not read from the text; a charge on a site " ++
              "of it is not read")
        at_ := callee
    | .send => other "a send"
    | .oracleSend => other "an oracle send"
    | .query => other "a query"
    | .opening => other "an opening"
    | .sample => other "a sample"
    if last then
      if names.size > 1 then return .limit "a charge on a site of a callee is not in a table of caps yet"
      match kind with
      | .draw => return .draw name
      | _ => return .limit (s!"`sites.{name}` is no draw: a charge on an application or an " ++
          "attempt is not in a table of caps yet")
  throw "a charge names no site"

/-- **A limit of a table of caps**: what a legal source has and a table has no place for yet. They
are four: a charge on an application or on an attempt; a charge on a site of an applied protocol;
a charged draw under a loop whose count is read at run time, or in an attempt; an application
under such a loop or in an attempt, whether or not its callee charges anything. A goal that
writes its ceiling is issued without a table; a goal that takes its bound from the table is
refused with the limit. This is a limit of the written stage, not a rule of the language: the
language gives each of these a total (SX8). -/
structure TableLimit where
  place : Syntax.Span
  message : String

def TableLimit.describe (limit : TableLimit) : String :=
  s!"{location limit.place}: WK-CHARGE: {limit.message}"

/-- A table under construction: the uses read so far, and the first limit that the walk met. The
walk goes on after a limit, so an error of the source that stands after one is still an error;
the uses of a walk that met a limit are no table. -/
structure TableWalk where
  uses : Array (ProofSubject × UseCaps) := #[]
  limit : Option TableLimit := none

abbrev TableM := StateT TableWalk ExportM

/-- Note a limit; the first one stays. -/
def atLimit (place : Syntax.Span) (message : String) : TableM Unit :=
  modify fun walk => if walk.limit.isSome then walk else { walk with limit := some ⟨place, message⟩ }

mutual

/-- The caps of a use as they add up along one run of its definition: the tally of the stored
body, with each application as a call of the use of its callee at the proof arguments of that
application, each charged draw at its cap, and everything else left out. A choice of which
neither arm has a charged draw or a call is no choice, as in `Core.Tally.filterMap`, by which a
module checks this tally against the stored program. -/
partial def capsOfTally {V : Core.Vocabulary} (c : AdmittedRoot) (subject : ProofSubject)
    (name : String) (place : Syntax.Span) (capped : Array (Core.Key × Nat × Nat)) :
    Core.Tally (Core.Key × Core.ProtocolRaw V × Option Nat) → TableM (Core.Tally Cap)
  | .nil => pure .nil
  | .item (key, operation, count) rest => do
    match operation with
    | .apply _ _ =>
      if count.isNone then
        atLimit place (s!"an application in `{name}` is under a loop whose count is read " ++
          s!"at run time, or in an attempt (instruction {key.number}): it has no count in a table " ++
          "of caps yet")
      -- the callee is read also where the application has no count: its charges may be in error
      let child ← subject.child c key
      let callee ← capsOfUse c child
      let rest ← capsOfTally c subject name place capped rest
      match count with
      | some count => return .item (.call ⟨key, count, callee⟩) rest
      | none => return rest
    | _ =>
      match capped.find? (·.1 == key), count with
      | some (_, numerator, denominator), some count =>
        return .item (.draw ⟨key, numerator, denominator, count⟩)
          (← capsOfTally c subject name place capped rest)
      | _, _ => capsOfTally c subject name place capped rest
  | .choice left right rest => do
    let left ← capsOfTally c subject name place capped left
    let right ← capsOfTally c subject name place capped right
    let rest ← capsOfTally c subject name place capped rest
    match left, right with
    | .nil, .nil => return rest
    | _, _ => return .choice left right rest

/-- The use of a definition at its proof arguments, in a table under construction: its place.
A use that the table has is found again, so two applications that give a callee the same proof
arguments are calls of one use. The calls of a new use are the applications of the stored
definition, each with the use of its callee at the proof arguments of that application; its
draws are the realizations of the draws that the contract of its definition charges, at the cap
that the charge has at these proof arguments. The counts are those of the stored body, and the
draws and the calls stand as the body has them: in its order, and in the arms of its choices
(`capsOfTally`). -/
partial def capsOfUse (c : AdmittedRoot) (subject : ProofSubject) : TableM Nat := do
  if let some place := (← get).uses.findIdx? (·.1 == subject) then return place
  let named := (c.emission.package ⟨[], [], [], [], []⟩).named
  let some (.protocol _ _ _ _ body) := named.definitions.find? (·.key.number == subject.protocol)
    | throw "WK-CHARGE: a use of the table is of no protocol of the package"
  let found := body.counted (some 1)
  let (charged, name, place) ← chargedSites c.state subject.protocol
  -- a site has one cap: a second charge on it is refused before any charge is read
  let mut seen : Array (Array String) := #[]
  for (names, span, _) in charged do
    if seen.contains names then
      refuse span "WK-CHARGE"
        s!"a second charge on `sites.{".".intercalate names.toList}`: a site has one cap"
    seen := seen.push names
  let mut capped : Array (Core.Key × Nat × Nat) := #[]
  -- A charge's site and amount are read before a limit is noted for it: a site that is no site of
  -- a charge, and an amount in error, are errors.
  let some owner := c.state.table.allocatedKey? subject.protocol | throw "missing charge instance"
  for (names, span, amount) in charged do
    let site ← match ← chargedSite c.state owner.declaration span names with
      | .draw site => pure site
      | .limit message =>
        discard <| chargeAmount c.state ⟨subject.protocol⟩ amount subject.specification
        atLimit span message
        continue
    let charge ← drawCharge c.state c.evidence.admitted.program ⟨subject.protocol⟩ site
      subject.specification
    for (_, key) in charge.draws do
      match found.find? (·.1 == key) with
      | some (_, _, some _) => capped := capped.push (key, charge.numerator, charge.denominator)
      | some (_, _, none) => atLimit span (s!"the draw `{site}` of `{name}` is under a loop whose count is " ++
          "read at run time, or in an attempt: it has no count in a table of caps yet")
      | none => throw s!"missing the draw `{site}` of `{name}` among the instructions of its definition"
  let caps ← capsOfTally c subject name place capped (body.tally (some 1))
  modify fun walk => { walk with uses := walk.uses.push (subject, ⟨⟨subject.protocol⟩, caps⟩) }
  return (← get).uses.size - 1

end

/-- **The table of caps of a goal's root** (SX8): the uses that the root reaches at the goal's
proof arguments, callees first and the root's last, each with the caps that the contract of its
definition gives its charged draws at the proof arguments of that use. No caller names a draw:
the table is of every charge that the root reaches. Where a charge that the root reaches has no
place in a table, the result is that limit, the first in the order of the walk; an error of the
source is an error whether or not a limit stands before it. -/
def goalCaps (c : AdmittedRoot) (specification : Array Nat) :
    ExportM (Except TableLimit CapTable) := do
  let (_, walk) ← (capsOfUse c ⟨c.id, specification⟩).run {}
  let table := match walk.limit with
    | some limit => .error limit
    | none => .ok ⟨walk.uses.toList.map (·.2)⟩
  return table

/-- The named request selects the deployed root even in an assembly with several schemes. -/
def admitSoundnessGoal (assembly : Assembly) (name : String) : ExportM AdmittedRoot := do
  let (selected, closed) ← (← resolveGoals assembly).selectNamed name .soundness
  closed.admitScheme selected.scheme

/-- Read the charge at a path of application instructions from the named goal's root. -/
def goalDrawCharge (c : AdmittedRoot) (goal : String) (path : List Core.Key) (draw : String) :
    ExportM DrawCharge := do
  let (selected, _) ← c.goalSource.selectNamed goal .soundness
  unless selected.scheme.protocol == c.id do throw "GL3: goal selects a different protocol"
  let root := ProofSubject.mk c.id selected.specification
  let subject ← path.foldlM (fun parent site => parent.child c site) root
  drawCharge c.state c.evidence.admitted.program ⟨subject.protocol⟩ draw subject.specification

end Zkc.Frontend.Written
