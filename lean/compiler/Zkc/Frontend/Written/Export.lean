module

public import Zkc.Frontend.Written.Proof
public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Driver.SourcePhases

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

def preamble := "module\n\npublic import Zkc.Formal.Written.Tactics\n\n@[expose] public section\nopen Zkc.Core Zkc.Formal.Written Std.WP\nset_option experimental.vcgen true\nset_option maxRecDepth 4000\nset_option maxHeartbeats 1800000\nset_option linter.unusedVariables false\nnamespace WrittenKnowledge\n"

def target (c : WrittenClause) : String := Id.run do
  let (v,p) := (c.view.verifier,c.view.prover)
  let sites := [c.view.commitment,c.view.challenge,c.view.response]
  let keys := " ".intercalate (sites.map fun site => s!"⟨{site.instruction.get!}⟩")
  let places := [("clause", c.source.where_), (c.relationName, c.relationSpan),
    (c.extractorName, c.extractorSpan)] ++ (sites.map fun site => (site.name.get!, site.place))
  let provenance := list (places.map fun (name,sp) => s!"({reprStr name}, {reprStr (location sp)})")
  return "\n".intercalate [
    s!"def sourceLocations : List (String × String) := {provenance}",
    "section Source",
    "def relation {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : G × G) (witness : F) : Option Bool := do", c.relation,
    "def extractor {F G : Type} (ops : Operations F G) [DecidableEq F] [DecidableEq G] (statement : G × G) (commitment : G) (left right : Branch F) : Option F := do", c.extraction,
    "end Source",
    "variable (M : Model V)",
    s!"def acceptsOf (program : Typed V) (root : Member program.headers.protocols header) (s : M.Val pointTy × M.Val pointTy) (path : List Frame) (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) : Prop :=",
    s!"  Returns (roleMeaning M program root {v} path (.cons s.1 (.cons s.2 (.cons () .nil)))) (forkTrace M path {p} {keys} a b)",
    "def accepts := acceptsOf M installed (Member.head : Member [header] header)",
    "variable (ops : Operations (M.Val scalarTy) (M.Val pointTy)) [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)]",
    "def obligation (path : List Frame) : Prop := SpecialSoundness (fun s => accepts M s path)",
    "  (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "def admittedObligation (a : Admitted V) (path : List Frame) : Prop :=",
    "  ∃ root : Member a.program.headers.protocols header, SpecialSoundness (fun s => acceptsOf M a.program root s path)",
    "    (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w)",
    "theorem of_obligation {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (path : List Frame) (proved : obligation M ops path) : admittedObligation M ops a path := by",
    "  have same := readback h", "  obtain ⟨pr, annotation, association, assured⟩ := a", "  change pr = installed at same",
    "  subst pr", "  exact ⟨Member.head, proved⟩", ""]

def verifierReplay (c : WrittenClause) (replay : VerifierProof) : String := Id.run do
  let v := c.view
  let keys := " ".intercalate ([v.commitment,v.challenge,v.response].map fun site => s!"⟨{site.instruction.get!}⟩")
  return "\n".intercalate [
    "omit [DecidableEq (M.Val scalarTy)] [DecidableEq (M.Val pointTy)] in",
    "theorem accepts_congr {N : Model V} (same : M = N) (s : M.Val pointTy × M.Val pointTy) (s' : N.Val pointTy × N.Val pointTy)",
    "    (a : M.Val pointTy) (a' : N.Val pointTy) (b : Branch (M.Val scalarTy)) (b' : Branch (N.Val scalarTy))",
    "    (hs : HEq s s') (ha : HEq a a') (hb : HEq b b') (path : List Frame) : accepts M s path a b ↔ accepts N s' path a' b' := by",
    "  subst N; cases hs; cases ha; cases hb; rfl",
    "def verifierCheck (s : M.Val pointTy × M.Val pointTy) (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) : Option Unit :=",
    s!"  require {replay.decision}",
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_returns (rows : GroupRows M ops) (s : M.Val pointTy × M.Val pointTy)",
    "    (path : List Frame) (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ verifierCheck M ops s a b = some () := by",
    "  refine (accepts_congr M (groupModel_eq M ops rows).symm s s a a b b HEq.rfl HEq.rfl HEq.rfl path).trans ?_",
    "  let N := groupModel M ops rows",
    s!"  let sem := roleSem N {v.verifier} (hs := (⟨[],[]⟩ : Headers V)) (Defs.fnTable N .nil) (Defs.rTable N .nil)",
    s!"  change Returns ((project {v.verifier} body).denote sem path (Env.empty.extend inputNames (.cons s.1 (.cons s.2 (.cons () .nil))))) (forkTrace N path {v.prover} {keys} a b) ↔ _",
    "  unfold forkTrace", "  expose_projection",
    s!"  source_proof {reprStr (location c.source.where_ ++ " using verifier at " ++ location c.verifierSpan)} =>",
    "\n".intercalate ((replay.steps.splitOn "\n").map ("  " ++ ·)), ""]

def schnorrProof (c : WrittenClause) : String :=
  "\n".intercalate [
    "omit [DecidableEq (M.Val scalarTy)] in",
    "theorem verifier_equation (rows : GroupRows M ops) (s : M.Val pointTy × M.Val pointTy)",
    "    (path : List Frame) (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) :",
    "    accepts M s path a b ↔ ops.scale s.1 b.suffix = ops.add a (ops.scale s.2 b.challenge) := by",
    s!"  source_proof {reprStr (location c.source.where_ ++ " using verifier at " ++ location c.verifierSpan)} =>",
    "    refine (verifier_returns M ops rows s path a b).trans (accepts_of_triple ?_)",
    "    unfold verifierCheck", "    vcgen [require_spec]", "    all_goals split <;> simp_all",
    "theorem certified (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) : obligation M ops path := by",
    s!"  source_proof {reprStr (location c.source.where_ ++ " using " ++ location c.extractorSpan ++ " and " ++ location c.relationSpan)} =>",
    "    intro s a l r hl hr apart",
    "    have one := (verifier_equation M ops rows s path a l).mp hl",
    "    have two := (verifier_equation M ops rows s path a r).mp hr",
    "    have gap : ops.sub l.challenge r.challenge ≠ ops.zero := fun h => apart ((laws.sub_zero ..).mp h)",
    "    have witness := extract_difference ops laws one two apart",
    "    apply returned_of_triple", "    unfold extractor", "    vcgen",
    "    all_goals simp (config := {zetaDelta := true}) [relation, gap, witness] <;> rfl",
    "theorem certified_admitted {a : Admitted V} (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a)",
    "    (rows : GroupRows M ops) (laws : ActionLaws ops) (path : List Frame) :",
    "    ∃ root : Member a.program.headers.protocols header, SpecialSoundness (fun s => acceptsOf M a.program root s path)",
    "      (fun s w => relation ops s w = some true) (fun s a l r w => extractor ops s a l r = some w) := by",
    "  exact of_obligation M ops h path (certified M ops rows laws path)", "#print axioms certified_admitted", ""]

def checkPorts (p : SourcePackage) (v : View) (where_ : Syntax.Span) : ExportM Unit := do
  let [.protocol _ 2 [a,b,x] [] _] := p.named.definitions
    | refuse where_ "WK-PORT" "expected two public inputs, a prover witness and an empty result"
  let point : p.bindings.vocabulary.Ty := .nominal (.inl (.group .g1))
  let scalar : p.bindings.vocabulary.Ty := .nominal (.inl (.field .bls12381Fr))
  let shared := [v.prover,v.verifier].mergeSort
  unless a.ty == point && b.ty == point && x.ty == scalar &&
      a.holders == shared && b.holders == shared && x.holders == [v.prover] do
    refuse where_ "WK-PORT" "the admitted ports do not match the written statement and witness"

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
  checkPorts pkg c.view c.source.where_
  let rendered ← program pkg evidence
  let replay ← (proofSteps pkg c.view).mapError (fun why => s!"{location c.source.where_}: WK-VIEW: {why}")
  let tail := verifierReplay c replay ++ (if withProof then schnorrProof c else "")
  return "\n".intercalate [preamble,rendered,target c,tail,"end WrittenKnowledge",""]

end Zkc.Frontend.Written
