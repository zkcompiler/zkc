module

public import Zkc.Frontend.Written.Algorithm
public import Zkc.Frontend.Driver.Bodies

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Syntax

def portView (code : Typing.ProtocolCode) (where_ : Span) : ExportM View := do
  let #[.exchange p v pt ci, .draw owner #[peer] _ di, .exchange sender receiver fr ri] := code.flows
    | refuse where_ "WK-VIEW" "expected a commitment, a verifier draw and a response"
  unless code.roles.size == 2 && p != v && owner == v && peer == p && sender == p && receiver == v &&
      StandardNames.fieldOf? fr == some .bls12381Fr do
    refuse where_ "WK-VIEW" "incompatible message roles or types"
  let site i := do
    let some s := code.sites[i]? | refuse where_ "WK-VIEW" "missing emitted occurrence"
    unless s.part == "value" && s.instruction.isSome && s.iteration.isEmpty &&
        (Typing.SiteEntry.realizations code.sites s.event s.part).size == 1 do
      refuse s.place "WK-VIEW" "expected an unambiguous top-level event"
    pure s
  let (commitment, challenge, response) := (← site ci, ← site di, ← site ri)
  unless [commitment.fieldName, challenge.fieldName, response.fieldName].Nodup do
    refuse where_ "WK-VIEW" "two run fields have the same selector"
  return ⟨commitment, challenge, response, p, v, ← historySort pt where_⟩

def reference (s : Compile.State) (file : FileId) (path : Path) : ExportM DeclarationId := do
  let some resolution := s.resolutions.find? file path | refuse path.span "WK-REF" "unresolved path"
  unless resolution.segments.all (·.staticArgs.isNone) do
    refuse path.span "WK-REF" "explicit or import-fixed static arguments on a clause reference"
  let some (Step.declaration id) := resolution.segments.back?.map (·.step)
    | refuse path.span "WK-REF" "expected a declaration"
  return id

def location (s : Span) := s!"{s.file}:{s.render}"

structure ClauseSource where
  where_ : Span
  file : FileId
  rel : Path
  args : Array Argument
  extractor : Path

/-- SX5 assigns one contract to the defining module. Use the same lookup for a
protocol and for its two local functions, including contracts without knowledge clauses. -/
def clausesOf (s : Compile.State) (id : DeclarationId) (at_ : Span) :
    ExportM (Array Clause) := do
  let some owner := s.program.declarations[id]? | refuse at_ "WK-REF" "missing contract owner"
  let mut found := none
  for d in s.program.declarations do
    let .contract c := d.node | continue
    let some (Step.declaration target) := (s.resolutions.find? d.file c.target).bind (fun r => r.segments.back?.map (·.step))
      | continue
    if target != id then continue
    unless d.file == owner.file && d.namespace == owner.namespace do
      refuse c.span "WK-CLAUSE" "the contract must be in the module that defines its target"
    if found.isSome then refuse c.span "WK-CLAUSE" "a declaration has more than one contract"
    unless d.scopes.all (fun scope => owner.scopes.contains scope ||
        (s.program.scopes[scope]?).any (fun item => item.parameters.isEmpty && item.whereClause.isNone)) do
      refuse c.span "WK-CLAUSE" "the contract has additional parameter scopes"
    let _ ← reference s d.file c.target
    found := some c.clauses
  return found.getD #[]

def clause (s : Compile.State) (root : DeclarationId) (file : FileId) (decider : String) (where_ : Span) : ExportM ClauseSource := do
  let mut candidates := #[]
  for cl in ← clausesOf s root where_ do
    match cl with
    | .proves sp (some role) .. | .reduces sp (some role) .. =>
      unless decider == role.text do refuse sp "SX6" "the written fork must use the designated deciding role"
    | .knowledge sp _ (.call _ rel (.callArgs _ args none)) (.path ext) none =>
      candidates := candidates.push ⟨sp, file, rel, args, ext⟩
    | .knowledge sp .. => refuse sp "WK-CLAUSE" "expected a relation call and one source extractor"
    | .requires sp .. => refuse sp "WK-CLAUSE" "unsupported protocol precondition"
    | _ => pure ()
  let #[item] := candidates | refuse where_ "WK-CLAUSE" s!"expected one written knowledge clause, found {candidates.size}"
  return item

def evaluated {α : Type} (s : Compile.State) (at_ : Span) (attempt : CompileM α) : ExportM α :=
  match attempt.run {vocabulary} s with
  | (.ok a, after) =>
    match (after.log.entries.extract s.log.entries.size after.log.entries.size).find? (fun d => d.isError || d.isIncomplete) with
    | some diagnostic => refuse at_ "WK-TYPE" (diagnostic.render after.env.renderer)
    | none => pure a
  | (.error _, after) =>
    let messages := after.log.entries.extract s.log.entries.size after.log.entries.size
    let detail := (messages.back?.map (·.render after.env.renderer)).getD "could not evaluate at the selected protocol instance"
    refuse at_ "WK-TYPE" detail

def checkType (s : Compile.State) (env : Static.Env) (t : TypeExpr) (expected : ClosedType) : ExportM Unit := do
  let actual ← evaluated s t.span (Static.evalWrittenType env t)
  unless actual == expected do refuse t.span "WK-TYPE" "unexpected type at the selected protocol instance"

def checkRuns (s : Compile.State) (env : Static.Env) (t : TypeExpr) (key : InstanceKey) : ExportM Unit := do
  let .path _ path := t | refuse t.span "WK-VIEW" "expected a two-leaf run view"
  let some resolution := s.resolutions.find? env.file path | refuse t.span "WK-VIEW" "unresolved run-view type"
  let some last := resolution.segments.back? | refuse t.span "WK-VIEW" "missing run-view type"
  let .generated "Runs" := last.step | refuse t.span "WK-VIEW" "extractor requires Runs<2>"
  let some #[.term _ none count] := last.staticArgs | refuse t.span "WK-VIEW" "expected one leaf count"
  unless (← evaluated s t.span (Static.evalSize env count)) == 2 do refuse t.span "WK-VIEW" "expected two leaves"
  let protocolPath := resolution.segments.pop
  let some (Step.declaration id) := protocolPath.back?.map (·.step) | refuse t.span "WK-VIEW" "missing run-view protocol"
  unless id == key.declaration do refuse t.span "WK-VIEW" "extractor belongs to another protocol"
  -- SP2 fixes a positional argument where its import was written. The extractor can
  -- share the protocol's section even when the importing declaration stood outside it.
  let applied := protocolPath.filter (fun part => part.staticArgs.any (!·.isEmpty))
  let bindingEnv ← match applied.toList with
    | [part] =>
      if let some origin := part.fixedBy then
        let some imp := s.program.imports[origin]? | refuse t.span "WK-VIEW" "missing defining import"
        pure {env with file := imp.file, values := env.values.filter (fun ref _ => imp.scopes.contains ref.scope)}
      else pure env
    | [] => pure env
    | _ => refuse t.span "WK-VIEW" "expected one applied group parameter"
  let arguments ← evaluated s t.span do
    let .declarations steps scopes ← Static.evalWrittenSteps bindingEnv protocolPath t.span "" | throw .abandoned
    Static.bindArguments bindingEnv steps scopes t.span
  unless key.arguments == arguments do refuse t.span "WK-VIEW" "different protocol specialization"

/-- Elaborate the selected declaration by its resolved binder IDs. The extractor input is the
fixed-length sequence of generated Run records for the selected specialization. -/
def checkedClause (label : String) (s : Compile.State) (id : DeclarationId) (args : Array StaticValue)
    (inputs : Array ClosedType) (result : ClosedType) (specification : Bool) (at_ : Span) :
    ExportM String := do
  let action : CompileM (Except String String) := do
    let d ← Static.declaration id
    let inst ← Static.instantiate id args ⟨s.program.nameOf id, at_⟩
    let some decl := (← getModules).lowered? id | throw (.defect "missing lowered declaration")
    let .function head (.body expr) := decl.content | throw (.defect "expected a function body")
    let (code, _, tree, _) ← Emit.elaborateBody inst (s.program.nameOf id)
      (Static.instanceEnv s.program d args) ((head.parameters.map (·.binder)).zip inputs)
      result expr specification decl.locals Typing.typeBody
    if let some why := code.waiting then throw (.waiting why)
    if specification && code.canStop then throw (.defect "a relation can stop")
    let state ← get
    let emission : Typing.EmitM String := do
      let b ← Emit.bindCalls {} (Emit.calledIn tree)
      let (definition, _) ← Emit.Named.functionDefinition (← Emit.bodyContext b) ⟨inst⟩ result tree
      let package : SourcePackage := ⟨b, ⟨[definition]⟩, ⟨[],[],[],[],[]⟩⟩
      let .ok evidence := package.checkEvidence | Typing.defect "admission refused the selected function"
      match functionDeclarations label package evidence with
      | .ok text => return text
      | .error message => throw (.noCoreForm message)
    return match emission.run state with
      | .ok text => .ok text
      | .error (.defect msg) | .error (.waiting msg) | .error (.noCoreForm msg) => .error msg
  match action.run {vocabulary} s with
  | (.ok value, state) =>
    if let some diagnostic := (state.log.entries.extract s.log.entries.size state.log.entries.size).find? (fun d => d.isError || d.isIncomplete) then
      refuse at_ "WK-FUNCTION" (diagnostic.render state.env.renderer)
    value.mapError fun msg => s!"{at_.file}:{at_.render}: WK-FUNCTION: {msg}"
  | (.error err, state) =>
    let details := state.log.entries.extract s.log.entries.size state.log.entries.size
    refuse at_ "WK-FUNCTION" (String.intercalate "; " ((details.map fun d => d.render state.env.renderer).toList ++ [match err with | .waiting why | .defect why => why | _ => "function elaboration refused"]))

structure WrittenClause where
  view : View
  publicCount : Nat
  source : ClauseSource
  verifierSpan : Span
  relationName : String
  relationSpan : Span
  extractorName : String
  extractorSpan : Span
  calculations : ExportM (String × String)
  storedRelation : String
  storedExtractor : String
  operands : List Nat

/-- The written fork uses the scheme's online roles and public statement (SC2–SC4).
Construction and layout directives take effect after this stage. -/
def checkSchemeView (scheme : SchemeEntry) (code : Typing.ProtocolCode) (view : View) : ExportM Unit := do
  let mut interactive := false
  for line in scheme.lines do
    match line with
    | .context sp .. => refuse sp "WK-PORT" "scheme context must be represented in the public statement"
    | .offline sp .. | .ideal sp .. => refuse sp "WK-VIEW" "the written fork requires two online roles"
    | .construction _ (.interactive _) => interactive := true
    | _ => pure ()
  if let .error d := scheme.checkProver (code.roles.getD view.prover "") interactive then
    refuse d.span d.rule d.message

def declarations (s : Compile.State) (scheme : SchemeEntry) : ExportM WrittenClause := do
  let some key := s.results.key? scheme.protocol | refuse scheme.span "WK-ROOT" "missing instance"
  let some root := s.program.declarations[key.declaration]? | refuse scheme.span "WK-ROOT" "missing declaration"
  let .protocol proto := root.node | refuse scheme.span "WK-ROOT" "expected a protocol"
  let some (.protocol code) := s.results.body? scheme.protocol | refuse scheme.span "WK-ROOT" "missing typed protocol"
  if code.specificationOnly then refuse proto.span "WK-ROOT" "the selected protocol must be executable"
  let view ← portView code scheme.span
  checkSchemeView scheme code view
  let item ← clause s key.declaration root.file (code.roles.getD view.verifier "") scheme.span
  let relId ← reference s item.file item.rel
  let extId ← reference s item.file item.extractor
  let some rd := s.program.declarations[relId]? | refuse item.rel.span "WK-REF" "missing relation"
  let some ed := s.program.declarations[extId]? | refuse item.extractor.span "WK-REF" "missing extractor"
  let .relation r := rd.node | refuse item.rel.span "WK-REF" "expected a relation"
  let .def e := ed.node | refuse item.extractor.span "WK-REF" "expected a function"
  if let some (.spec sp) := e.modifier then refuse sp "WK-TYPE" "the extractor must be executable"
  for (id, sp) in [(extId, e.span), (relId, r.span)] do
    for spec in ← clausesOf s id sp do
      if let .requires sp .. := spec then refuse sp "WK-CLAUSE" "unsupported precondition on a selected declaration"
  let .body rb := r.binding | refuse r.span "WK-BODY" "relation must have a source body"
  let .body eb := e.binding | refuse e.span "WK-BODY" "extractor must have a source body"
  for d in [root, rd, ed] do
    unless (Static.deployedParameters s.program d).size == 1 &&
        (Static.specificationParameters s.program d).isEmpty &&
        d.scopes.all (fun i => (s.program.scopes[i]?).all (·.whereClause.isNone)) do
      refuse item.where_ "WK-TYPE" "expected one deployed group parameter and no additional constraints"
  let point := StandardNames.groupType .g1
  let scalar := StandardNames.fieldType .bls12381Fr
  unless key.arguments == #[.type point] do refuse scheme.span "WK-ROOT" "expected a G1 specialization"
  let some (.port ..) := proto.head.ports.back?
    | refuse proto.span "WK-PORT" "expected a prover witness"
  let publicNames ← proto.head.ports.pop.mapM fun
    | .port _ name _ _ false => pure name.text
    | _ => refuse proto.span "WK-PORT" "expected public group ports before the witness"
  unless !publicNames.isEmpty && r.statement.size == publicNames.size &&
      e.params.size == r.statement.size + 1 && item.args.size == r.statement.size do
    refuse item.where_ "WK-PORT" "statement, relation and extractor arities must agree"
  let some #[w] := r.witness | refuse r.span "WK-TYPE" "expected one relation witness"
  let some runs := e.params.back? | refuse e.span "WK-VIEW" "missing extractor run view"
  let some result := e.result | refuse e.span "WK-TYPE" "extractor needs a witness result"
  let re := Static.instanceEnv s.program rd key.arguments
  let ee := Static.instanceEnv s.program ed key.arguments
  evaluated s r.span (Static.checkBounds re rd r.name.text)
  evaluated s e.span (Static.checkBounds ee ed e.name.text)
  for param in r.statement do checkType s re param.type point
  checkType s re w.type scalar
  for param in e.params.pop do checkType s ee param.type point
  checkType s ee result scalar
  checkRuns s ee runs.type key
  let operand := fun arg => do
    let .positional sp expr := arg | refuse item.where_ "WK-PORT" "expected positional statement operands"
    let n ← localName expr
    let some index := publicNames.idxOf? n | refuse sp "WK-PORT" s!"unknown public input {n}"
    pure index
  let operands ← item.args.mapM operand
  let bind (params : Array Param) : Locals := (params.zip operands).toList.map fun (p, v) =>
    (p.name.text, ⟨.point, component "statement" v (v + 1 == publicNames.size)⟩)
  let #[.exchange _ _ history _, _, _] := code.flows | refuse e.span "WK-VIEW" "missing first message"
  let fields := #[(view.commitment.fieldName, history), (view.challenge.fieldName, scalar),
    (view.response.fieldName, scalar)]
  let (signatures, leaf, _) := s.results.signatures.intern {key with runRecord := true}
    ⟨.ofText "generated Run record", runs.type.span⟩ none
  let extractorResults := {s.results with signatures := signatures.setState leaf (.done (.data (.record false fields)))}
  let extractorState := {s with env := {s.env with results := extractorResults}}
  let fork := ClosedType.seq (.record leaf) (some 2)
  let publics := Array.replicate publicNames.size point
  let rt ← checkedClause "Relation" s relId key.arguments (publics.push scalar) .bool true r.span
  let et ← checkedClause "Extractor" extractorState extId key.arguments (publics.push fork) scalar false e.span
  let calculations : ExportM (String × String) := do
    let relation ← algorithm view ((w.name.text, ⟨.scalar,"witness"⟩) :: bind r.statement) .boolean rb
    let extraction ← algorithm view ((runs.name.text, ⟨.runs,""⟩) :: bind e.params.pop) .scalar eb
    return (relation, extraction)
  return ⟨view,publicNames.size,item,proto.span,r.name.text,r.span,e.name.text,e.span,calculations,rt,et,operands.toList⟩

end Zkc.Frontend.Written
