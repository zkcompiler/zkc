module

public import Zkc.Frontend.Written.Contract
public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Driver.SourcePhases

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

def preamble (withProof : Bool) : String :=
  let library := if withProof then "Zkc.Formal.Written.GroupReplay" else "Zkc.Formal.Written.Source"
  "module\n\npublic import " ++ library ++ "\n\n@[expose] public section\nopen Zkc.Core Zkc.Formal.Written Std.WP\nset_option experimental.vcgen true\nset_option maxRecDepth 4000\nset_option maxHeartbeats 1800000\nset_option linter.unusedVariables false\nnamespace WrittenKnowledge\n"

def target (c : WrittenClause) (historyType : String) : String := Id.run do
  let (v,p) := (c.view.verifier,c.view.prover)
  let sites := [c.view.commitment,c.view.challenge,c.view.response]
  let keys := " ".intercalate (sites.map fun site => s!"⟨{site.instruction.get!}⟩")
  let places := [("clause", c.source.where_), (c.relationName, c.relationSpan),
    (c.extractorName, c.extractorSpan)] ++ (sites.map fun site => (site.name.get!, site.place))
  let provenance := list (places.map fun (name,sp) => s!"({reprStr name}, {reprStr (location sp)})")
  let params := (List.range c.publicCount).map fun i => component "s" i (i + 1 == c.publicCount)
  let values := (params ++ ["()"]).foldr (fun val tail => s!"(.cons {val} {tail})") ".nil"
  return "\n".intercalate [
    s!"def sourceLocations : List (String × String) := {provenance}",
    s!"abbrev Statement (G : Type) := {publicProduct (List.replicate c.publicCount "G")}",
    s!"abbrev Commitment (G : Type) := {c.view.history.leanType}",
    s!"abbrev historyTy : V.Ty := {historyType}",
    "def relation {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : Statement G) (witness : F) : Option Bool := do", c.relation,
    "def extractor {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : Statement G) (commitment : Commitment G) (left right : Branch F) : Option F := do", c.extraction,
    "variable (M : Model V)",
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
    "variable (ops : Operations (M.Val scalarTy) (M.Val pointTy)) [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)]",
    "def verifierCheck (_ops : Operations (M.Val scalarTy) (M.Val pointTy)) (s : Statement (M.Val pointTy))",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) (path : List Frame := []) := replayCheck M s path a b",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_returns (_rows : GroupRows M ops) (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ verifierCheck M ops s a b path = some () := replay_returns M s path a b",
    "def obligation (path : List Frame) : Prop := SpecialSoundness (fun s => accepts M s path)",
    "  (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "def admittedObligation (a : Admitted V) (path : List Frame) : Prop :=",
    "  ∃ root : Member a.program.headers.protocols header, SpecialSoundness (fun s => acceptsOf M a.program root s path)",
    "    (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "theorem of_obligation {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (path : List Frame) (proved : obligation M ops path) : admittedObligation M ops a path := by",
    "  obtain ⟨pr, annotation, association, assured⟩ := a", "  have same := readback h", "  change pr = installed at same",
    "  subst pr", "  exact ⟨Member.head, proved⟩", ""]

inductive TranscriptEvent (T : Type) where
  | message (key : Key) (type : T)
  | challenge (key : Key)

/-- Every verifier interaction must have a reply in the run view. Pure verifier computations
and guards are unrestricted here. A truncated trace would make every fork vacuous. -/
def checkPorts (p : SourcePackage) (c : WrittenClause) : ExportM String := do
  let v := c.view
  let sp := c.source.where_
  let [.protocol _ 2 ports [] (.mk _ steps _)] := p.named.definitions
    | refuse sp "WK-PORT" "expected a two-role protocol with an empty result"
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
    "def verifierConditions {F G : Type} (ops : Operations F G) [DecidableEq G] (s : Statement G) (a : Commitment G) (b : Branch F) : Prop := by",
    s!"  source_proof {origin} => written_guards stored {v}",
    "omit [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)] in",
    "theorem accepts_congr {N : Model V} (same : M = N) (s : Statement (M.Val pointTy)) (s' : Statement (N.Val pointTy))",
    "    (a : M.Val historyTy) (a' : N.Val historyTy) (b : Branch (M.Val scalarTy)) (b' : Branch (N.Val scalarTy))",
    "    (hs : HEq s s') (ha : HEq a a') (hb : HEq b b') (path : List Frame) : accepts M s path a b ↔ accepts N s' path a' b' := by",
    "  subst N; cases hs; cases ha; cases hb; rfl",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_equations (rows : GroupRows M ops) (s : Statement (M.Val pointTy))",
    "    (path : List Frame) (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ verifierConditions ops s a b := by",
    s!"  source_proof {origin} =>",
    "    refine (accepts_congr M (groupModel_eq M ops rows).symm s s a a b b HEq.rfl HEq.rfl HEq.rfl path).trans ?_",
    "    let N := groupModel M ops rows",
    s!"    let sem := roleSem N {v} (hs := (⟨[],[]⟩ : Headers V)) (Defs.fnTable N .nil) (Defs.rTable N .nil)",
    "    refine (accepts_projected N s path a b).trans ?_",
    "    dsimp only [observed, forkInputs, List.map, Input.entry, InputPort.input, InputPort.operation, verifierConditions]",
    s!"    written_steps stored {v}",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_equation (rows : GroupRows M ops) (s : Statement (M.Val pointTy)) (path : List Frame)",
    "    (a : M.Val historyTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ guard_formula% (verifierConditions ops s a b) := by",
    "  simpa only [verifierConditions, decide_eq_true_eq, and_true] using verifier_equations M ops rows s path a b",
    "theorem certified (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) : obligation M ops path := by",
    s!"  source_proof {clause} =>",
    "    certify_group_fork (fun s a b => verifier_equation M ops rows s path a b) with ops laws for extractor relation",
    "theorem certified_admitted {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) : admittedObligation M ops a path :=",
    "  of_obligation M ops h path (certified M ops rows laws path)", "#print axioms certified_admitted", ""]

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
  let historyType ← checkPorts pkg c
  let rendered ← program pkg evidence
  let proof := if withProof then certificate c else ""
  return "\n".intercalate [preamble withProof, rendered, target c historyType, proof, "end WrittenKnowledge", ""]

end Zkc.Frontend.Written
