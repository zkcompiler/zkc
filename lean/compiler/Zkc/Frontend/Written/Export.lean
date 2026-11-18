module

public import Zkc.Frontend.Written.Contract
public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Driver.SourcePhases

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

def preamble (withProof : Bool) : String :=
  let library := if withProof then "Zkc.Formal.Written.GroupReplay" else "Zkc.Formal.Written.FunctionMeaning"
  "module\n\npublic import " ++ library ++ "\n\n@[expose] public section\nopen Zkc.Core Zkc.Formal.Written Std.WP\nset_option experimental.vcgen true\nset_option maxRecDepth 4000\nset_option maxHeartbeats 1800000\nset_option linter.unusedVariables false\nnamespace WrittenKnowledge\n"

def target (c : WrittenClause) (historyType : String) : String := Id.run do
  let (v,p) := (c.view.verifier,c.view.prover)
  let sites := [c.view.commitment,c.view.challenge,c.view.response]
  let keys := " ".intercalate (sites.map fun site => s!"⟨{site.instruction.get!}⟩")
  let places := [("clause", c.source.where_), (c.relationName, c.relationSpan),
    (c.extractorName, c.extractorSpan)] ++ (sites.map fun site => (site.name.get!, site.place))
  let provenance := list (places.map fun (name,sp) => s!"({reprStr name}, {reprStr (location sp)})")
  let params := (List.range c.publicCount).map fun i => component "s" i (i + 1 == c.publicCount)
  let clauseInputs := c.operands.map fun index => params[index]!
  let inputs (last : String) := (clauseInputs ++ [last]).foldr (fun x tail => s!"(.cons {x} {tail})") ".nil"
  let values := (params ++ ["()"]).foldr (fun val tail => s!"(.cons {val} {tail})") ".nil"
  let calculations := match c.calculations with
    | .error _ => []
    | .ok (relation, extraction) => [
      "def relation {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : Statement G) (witness : F) : Option Bool := do", relation,
      "def extractor {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : Statement G) (commitment : Commitment G) (left right : Branch F) : Option F := do", extraction]
  return "\n".intercalate <| [
    c.storedRelation, c.storedExtractor,
    s!"def sourceLocations : List (String × String) := {provenance}",
    s!"abbrev Statement (G : Type) := {publicProduct (List.replicate c.publicCount "G")}",
    s!"abbrev Commitment (G : Type) := {c.view.history.leanType}",
    s!"abbrev historyTy : V.Ty := {historyType}"] ++ calculations ++ [
    "variable (M : Model V)",
    "def relationArguments (s : Statement (M.Val pointTy)) (w : M.Val scalarTy) : HList M.Val RelationHeader.ins :=",
    s!"  {inputs "w"}",
    "def extractorArguments (s : Statement (M.Val pointTy)) (a : M.Val historyTy) (l r : Branch (M.Val scalarTy)) : HList M.Val ExtractorHeader.ins :=",
    s!"  {inputs "((a,l.challenge,l.suffix,()),(a,r.challenge,r.suffix,()),())"}",
    "def coreRelationOf (p : Typed V) (root : Member p.headers.fns RelationHeader) (s : Statement (M.Val pointTy)) (w : M.Val scalarTy) : Option Bool :=",
    "  functionResult (t := .bool) (fnMeaning M p root (relationArguments M s w))",
    "def coreRelation := coreRelationOf M installedRelation Member.head",
    "def coreExtractorOf (p : Typed V) (root : Member p.headers.fns ExtractorHeader) (s : Statement (M.Val pointTy)) (a : M.Val historyTy) (l r : Branch (M.Val scalarTy)) : Option (M.Val scalarTy) :=",
    "  functionResult (t := scalarTy) (fnMeaning M p root (extractorArguments M s a l r))",
    "def coreExtractor := coreExtractorOf M installedExtractor Member.head",
    s!"def inputValues (s : Statement (M.Val pointTy)) : HList (RV M {v}) ports := {values}",
    s!"def observed (path : List Frame) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) := forkInputs M historyTy path {p} {keys} a b",
    "def acceptsOf (program : Typed V) (root : Member program.headers.protocols header) (s : Statement (M.Val pointTy)) (path : List Frame) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) : Prop :=",
    s!"  Returns (roleMeaning M program root {v} path (inputValues M s)) ((observed M path a b).map Input.entry)",
    "def accepts := acceptsOf M installed (Member.head : Member [header] header)",
    "theorem accepts_projected (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    s!"    accepts M s path a b ↔ Returns ((project {v} body).denote",
    s!"      (roleSem M {v} (hs := (⟨[],[]⟩ : Headers V)) (Defs.fnTable M .nil) (Defs.rTable M .nil))",
    "      path (Env.empty.extend inputNames (inputValues M s))) ((observed M path a b).map Input.entry) :=",
    s!"  singleton_role_returns M header inputNames body _ {v} path (inputValues M s) _",
    "def replayCheck (s : Statement (M.Val pointTy)) (path : List Frame) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) : Option Unit :=",
    s!"  replay (observed M path a b) (roleMeaning M installed Member.head {v} path (inputValues M s))",
    "theorem replay_returns (s : Statement (M.Val pointTy)) (path : List Frame) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ replayCheck M s path a b = some () := replay_iff ..",
    "def coreObligation (path : List Frame) : Prop := SpecialSoundness (fun s => accepts M s path)",
    "  (fun s w => coreRelation M s w = some true) (fun s a l r w => coreExtractor M s a l r = some w)",
    "def compiledObligation (protocol relation extractor : Admitted V) (path : List Frame) : Prop :=",
    "  ∃ root : Member protocol.program.headers.protocols header, ∃ rel : Member relation.program.headers.fns RelationHeader,",
    "  ∃ ext : Member extractor.program.headers.fns ExtractorHeader, SpecialSoundness (fun s => acceptsOf M protocol.program root s path)",
    "    (fun s w => coreRelationOf M relation.program rel s w = some true)",
    "    (fun s a l r w => coreExtractorOf M extractor.program ext s a l r = some w)",
    "theorem of_core_obligation {p r e : Admitted V} (hp : admit stored ⟨[],[],[],[],[]⟩ = .ok p)",
    "    (hr : admit storedRelation ⟨[],[],[],[],[]⟩ = .ok r) (he : admit storedExtractor ⟨[],[],[],[],[]⟩ = .ok e)",
    "    (path : List Frame) (proof : coreObligation M path) : compiledObligation M p r e path := by",
    "  unfold compiledObligation",
    "  rw [readback hp, RelationReadback r hr, ExtractorReadback e he]",
    "  exact ⟨.head, .head, .head, proof⟩",
    "variable (ops : Operations (M.Val scalarTy) (M.Val pointTy)) [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)]",
    "def verifierCheck (_ops : Operations (M.Val scalarTy) (M.Val pointTy)) (s : Statement (M.Val pointTy))",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) (path : List Frame := []) := replayCheck M s path a b",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_returns (_rows : GroupRows M ops) (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ verifierCheck M ops s a b path = some () := replay_returns M s path a b"
    ] ++ (if c.calculations.isOk then [
    "def obligation (path : List Frame) : Prop := SpecialSoundness (fun s => accepts M s path)",
    "  (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "def admittedObligation (a : Admitted V) (path : List Frame) : Prop :=",
    "  ∃ root : Member a.program.headers.protocols header, SpecialSoundness (fun s => acceptsOf M a.program root s path)",
    "    (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "theorem of_obligation {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (path : List Frame) (proved : obligation M ops path) : admittedObligation M ops a path := by",
    "  obtain ⟨pr, annotation, association, assured⟩ := a", "  have same := readback h", "  change pr = installed at same",
    "  subst pr", "  exact ⟨Member.head, proved⟩", ""] else [])

inductive TranscriptEvent (T : Type) where
  | message (key : Key) (type : T)
  | challenge (key : Key)

/-- Every verifier interaction must have a reply in the run view. Pure verifier computations
and guards are unrestricted here. A truncated trace would make every fork vacuous. -/
def checkPorts (p : SourcePackage) (evidence : p.Admission) (c : WrittenClause) : ExportM String := do
  let v := c.view
  let sp := c.source.where_
  let [.protocol root 2 ports [] (.mk _ steps _)] := p.named.definitions
    | refuse sp "WK-PORT" "expected a two-role protocol with an empty result"
  let some addresses := Emit.SiteAddresses.forProtocol evidence.admitted.program root
    | refuse sp "WK-VIEW" "admitted protocol is missing"
  for site in [v.commitment, v.challenge, v.response] do
    unless (addresses.resolve site).isSome do refuse site.place "WK-VIEW" "ambiguous or absent admitted event address"
  let point : p.bindings.vocabulary.Ty := .nominal (.inl (.group .g1))
  let scalar : p.bindings.vocabulary.Ty := .nominal (.inl (.field .bls12381Fr))
  let shared := [v.prover,v.verifier].mergeSort
  unless ports == List.replicate c.publicCount ⟨point, shared⟩ ++ [⟨scalar, [v.prover]⟩] do
    refuse sp "WK-PORT" "the admitted ports do not match the written statement and witness"
  let mut events : Array (TranscriptEvent p.bindings.vocabulary.Ty) := #[]
  for step in steps do
    match step with
    | .op k _ (.event (.flow .message giver peers) t) _ =>
      unless giver == v.prover && peers == [v.verifier] do refuse sp "WK-VIEW" "unexpected message direction"
      events := events.push (.message k t)
    | .op k _ (.event (.given (.coin law) who peers) t) [] =>
      if who == v.prover && peers.isEmpty then continue
      unless who == v.verifier && peers == [v.prover] && t == scalar &&
          law == .uniform (.nominal (.field .bls12381Fr)) do refuse sp "WK-VIEW" "unexpected verifier draw"
      events := events.push (.challenge k)
    | .op _ _ (.compute ..) _ | .guard .. => pure ()
    | _ => refuse sp "WK-VIEW" "unsupported verifier interaction"
  let #[.message comm historyTy, .challenge draw, .message reply replyTy] := events
    | refuse sp "WK-VIEW" "expected a message, a public challenge and a response"
  unless [some comm.number, some draw.number, some reply.number] ==
      [v.commitment.instruction, v.challenge.instruction, v.response.instruction] && replyTy == scalar do
    refuse sp "WK-VIEW" "incompatible transcript sites"
  ty (b := p.bindings) historyTy

/-- The certificate applies the same library proof to every exported root. The library
recovers the guard conditions and validates its instruction steps against the projection. -/
def certificate (c : WrittenClause) : String := Id.run do
  let v := c.view.verifier
  let origin := reprStr (location c.source.where_ ++ " using verifier at " ++ location c.verifierSpan)
  let clause := reprStr (location c.source.where_ ++ " using " ++ location c.extractorSpan ++ " and " ++ location c.relationSpan)
  return "\n".intercalate [
    "omit [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)] in",
    "def verifierConditions (s : Statement (M.Val pointTy)) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) : Prop := by",
    s!"  source_proof {origin} => written_guards stored {v} replies [a, b.challenge, b.suffix]",
    "omit [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)] in",
    "theorem model_equations (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ verifierConditions M s a b := by",
    s!"  source_proof {origin} =>",
    "    refine (accepts_projected M s path a b).trans ?_",
    s!"    let sem := roleSem M {v} (hs := (⟨[],[]⟩ : Headers V)) (Defs.fnTable M .nil) (Defs.rTable M .nil)",
    "    dsimp only [observed, forkInputs, List.map, Input.entry, InputPort.input, InputPort.operation, verifierConditions]",
    s!"    written_steps stored {v} replies [a, b.challenge, b.suffix]",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_equation (rows : GroupRows M ops) (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ interpreted_guards% (verifierConditions M s a b) with M rows := by",
    "  interpret_guards (model_equations M s path a b) with M rows",
    "theorem relation_agrees (rows : GroupRows M ops) (field : FunctionRows M ops)",
    "    (s : Statement (M.Val pointTy)) (w : M.Val scalarTy) : coreRelation M s w = relation ops s w := by",
    s!"  source_proof {clause} =>",
    "    change functionResult (RelationBody.denote (localSem M [] (Defs.fnTable M .nil)) [] (Env.empty.extend RelationNames (relationArguments M s w))) = _",
    "    check_function relation with rows field",
    "theorem extractor_agrees (rows : GroupRows M ops) (field : FunctionRows M ops) (s : Statement (M.Val pointTy))",
    "    (a : M.Val historyTy) (l r : Branch (M.Val scalarTy)) : coreExtractor M s a l r = extractor ops s a l r := by",
    s!"  source_proof {clause} =>",
    "    change functionResult (ExtractorBody.denote (localSem M [] (Defs.fnTable M .nil)) [] (Env.empty.extend ExtractorNames (extractorArguments M s a l r))) = _",
    "    check_function extractor with rows field",
    "theorem certified (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) : obligation M ops path := by",
    s!"  source_proof {clause} =>",
    "    certify_group_fork (fun s a b => verifier_equation M ops rows s path a b) with ops laws for extractor relation",
    "theorem certified_admitted {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) : admittedObligation M ops a path :=",
    "  of_obligation M ops h path (certified M ops rows laws path)", "#print axioms certified_admitted",
    "theorem certified_core (rows : GroupRows M ops) (field : FunctionRows M ops) (laws : ActionLaws ops)",
    "    (path : List Frame) : coreObligation M path := by",
    "  intro s a l r hl hr apart",
    "  obtain ⟨w, ext, rel⟩ := certified M ops rows laws path s a l r hl hr apart",
    "  exact ⟨w, (extractor_agrees M ops rows field s a l r).trans ext, (relation_agrees M ops rows field s w).trans rel⟩",
    "theorem certified_core_admitted {p r e : Admitted V} (hp : admit stored ⟨[],[],[],[],[]⟩ = .ok p)",
    "    (hr : admit storedRelation ⟨[],[],[],[],[]⟩ = .ok r) (he : admit storedExtractor ⟨[],[],[],[],[]⟩ = .ok e)",
    "    (rows : GroupRows M ops) (field : FunctionRows M ops) (laws : ActionLaws ops) (path : List Frame) :",
    "    compiledObligation M p r e path := of_core_obligation M hp hr he path (certified_core M ops rows field laws path)",
    "#print axioms certified_core_admitted", ""]

def exportSource (assembly : Assembly) (schemeName : String) (withProof : Bool) : ExportM String := do
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    let (report, s) := phase.runIn {vocabulary} state
    state := s
    if let some diag := s.log.entries.find? (fun d => d.isError || d.isIncomplete) then
      throw s!"{diag.span.file}:{diag.render s.env.renderer}"
    if let some skipped := report.interrupted then throw s!"WK-FRONTEND: {skipped}"
  let #[scheme] := state.results.schemes.filter (·.name == schemeName)
    | throw s!"WK-ROOT: expected exactly one scheme named {schemeName}"
  let (result, s) := (Typing.typeBody scheme.protocol scheme.span).run {vocabulary} state
  if let some diag := s.log.entries.find? (fun d => d.isError || d.isIncomplete) then
    throw s!"{diag.span.file}:{diag.render s.env.renderer}"
  let .ok _ := result | refuse scheme.span "WK-ROOT" "protocol did not typecheck"
  let c ← declarations s scheme
  let .ok emission := Typing.emitRoot s scheme.protocol | refuse scheme.span "WK-CORE" "protocol did not emit"
  let pkg := emission.package ⟨[],[],[],[],[]⟩
  let .ok evidence := pkg.checkEvidence | refuse scheme.span "WK-CORE" "admission refused the emitted program"
  let historyType ← checkPorts pkg evidence c
  let rendered ← program pkg evidence
  if withProof then
    if let .error why := c.calculations then refuse c.source.where_ "WK-PROOF" why
  let proof := if withProof then certificate c else ""
  return "\n".intercalate [preamble withProof, rendered, target c historyType, proof, "end WrittenKnowledge", ""]

end Zkc.Frontend.Written
