module

public import Zkc.Source.Structured.ProtocolAdmission
public import Zkc.Source.Structured.ProtocolContext
public import Std.Data.TreeSet.Lemmas

@[expose] public section

namespace Zkc.Source.Structured

/-- Conservative original native expansion accounting, independent of execution. -/
structure ApplicationSummary where
  work : Nat := 0
  depth : Nat := 1
  indices : Nat := 0
  sites : Nat := 0
  siteBytes : Nat := 0
  longestSite : Nat := 0
  deriving DecidableEq, Repr

namespace ApplicationMetadata

def boundedAdd (limit left right : Nat) : Except String Nat :=
  if left > limit || right > limit - left then .error "structured-application-limit"
  else .ok (left + right)

def boundedMultiply (limit left right : Nat) : Except String Nat :=
  if left != 0 && right > limit / left then .error "structured-application-limit"
  else .ok (left * right)

/-- An accounting record is not executable syntax and contains no typed body. -/
structure SourceCost where
  descriptor : Option Descriptor
  slots : Nat
  selectors : Nat
  site : String
  deriving Repr

def terminatorCost : Terminator → SourceCost
  | .ret refs | .yield refs | .condition refs => ⟨none, refs.length, 0, ""⟩
  | .stop _ site => ⟨none, 0, 0, site⟩

def instructionCost (instruction : Instruction) : SourceCost :=
  let .instruction descriptor operands results _ site := instruction
  let selectors := match descriptor with
    | .protocolApply _ roles | .protocolRepeat _ _ roles _ | .restrict roles => roles.length
    | _ => 0
  ⟨some descriptor, operands.length + results.length, selectors, site⟩

theorem terminatorCost_return (operands : List Nat) :
    terminatorCost (.ret operands) = ⟨none, operands.length, 0, ""⟩ := rfl

theorem instructionCost_application (name site : String) (roles : List String)
    (operands : List Nat) (results : List Ty) :
    instructionCost (.instruction (.protocolApply name roles) operands results [] site) =
      ⟨some (.protocolApply name roles), operands.length + results.length, roles.length, site⟩ := rfl

theorem instructionCost_mathCall (name : String) (operands : List Nat) (results : List Ty) :
    instructionCost (.instruction (.call name) operands results [] "") =
      ⟨some (.call name), operands.length + results.length, 0, ""⟩ := rfl

/-- Original preorder includes each nested terminator and excludes synthesized marks. -/
def originalCosts : Nat → Block → Except String (List SourceCost)
  | 0, _ => .error "structured-region-depth"
  | depth + 1, .block instructions terminal => do
    let costs ← instructions.mapM fun instruction => do
      let .instruction _ _ _ regions _ := instruction
      let children ← regions.mapM fun (.region _ _ body) => originalCosts depth body
      return instructionCost instruction :: children.flatten
    return costs.flatten ++ [terminatorCost terminal]

def addOriginal (summary : ApplicationSummary) (cost : SourceCost) :
    Except String ApplicationSummary := do
  let work ← boundedAdd Limits.applicationVisits summary.work 1
  let indices ← boundedAdd Limits.applicationIndices summary.indices (cost.slots + cost.selectors)
  let siteBytes ← boundedAdd Limits.applicationSiteBytes summary.siteBytes cost.site.utf8ByteSize
  let longestSite := max summary.longestSite cost.site.utf8ByteSize
  if longestSite > Limits.siteBytes then throw "structured-application-limit"
  return { summary with
    work := work, indices := indices, siteBytes := siteBytes, longestSite := longestSite,
    sites := summary.sites + (if cost.site.isEmpty then 0 else 1) }

def addChild (summary child : ApplicationSummary) (boundary selectors sitePrefix : Nat)
    (application : Bool) : Except String ApplicationSummary := do
  let work ← boundedAdd Limits.applicationVisits summary.work child.work
  let work ← boundedAdd Limits.applicationVisits work boundary
  let indices ← boundedAdd Limits.applicationIndices summary.indices child.indices
  let indices ← boundedAdd Limits.applicationIndices indices (2 * boundary + selectors)
  let depth := max summary.depth (child.depth + 1)
  if depth > Limits.nesting then throw "structured-application-limit"
  if application then
    let extra ← boundedMultiply Limits.applicationSiteBytes child.sites sitePrefix
    let siteBytes ← boundedAdd Limits.applicationSiteBytes summary.siteBytes child.siteBytes
    let siteBytes ← boundedAdd Limits.applicationSiteBytes siteBytes extra
    let longestSite := if child.sites == 0 then summary.longestSite
      else max summary.longestSite (child.longestSite + sitePrefix)
    if longestSite > Limits.siteBytes then throw "structured-application-limit"
    return {
      work := work, depth := depth, indices := indices, sites := summary.sites + child.sites, siteBytes := siteBytes, longestSite := longestSite }
  else return { summary with work, indices, depth }

/-- Original Math expansion changes work/depth/slots while keeping its separate
site namespace out of the protocol summary. -/
theorem addChild_math_namespace {summary child result : ApplicationSummary}
    (accepted : addChild summary child 0 0 0 false = .ok result) :
    result.sites = summary.sites ∧ result.siteBytes = summary.siteBytes ∧
      result.longestSite = summary.longestSite := by
  unfold addChild at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    exact ⟨rfl, rfl, rfl⟩

abbrev SummaryTable := List (String × ApplicationSummary)
abbrev SummaryM := StateT SummaryTable (Except String)

/-- Cached suffix depth remains part of every occurrence's accounting.
An exhausted traversal depth refuses before cache lookup; this fixes the Lean
error category even when a cached summary would exceed the combined depth cap. -/
def summarizeFunction (snapshot : Snapshot) : Nat → Function → SummaryM ApplicationSummary
  | 0, _ => throw "structured-application-depth"
  | depth + 1, function => do
    if let some (_, cached) := (← get).find? (·.1 == function.name) then return cached
    let costs ← originalCosts Limits.nesting function.body
    let summary ← costs.foldlM (fun summary cost => do
      let summary ← addOriginal summary cost
      match cost.descriptor with
      | some (.protocolApply name _) =>
        let .function callee ← lookupDefinition snapshot name | throw "structured-call-kind"
        if !(.function callee : Definition).acceptsEdge .protocolApply then
          throw "structured-call-kind"
        let signature ← resolveProtocolSignature callee
        let child ← summarizeFunction snapshot depth callee
        let boundary := signature.inputs.length + signature.outputs.length
        let selectors := (signature.inputScopes ++ signature.outputScopes).foldl
          (fun count scope => count + scope.length) 0
        addChild summary child boundary selectors (12 + cost.site.utf8ByteSize) true
      | some (.call name) =>
        let .function callee ← lookupDefinition snapshot name | throw "structured-call-kind"
        if !(.function callee : Definition).acceptsEdge .call then throw "structured-call-kind"
        let child ← summarizeFunction snapshot depth callee
        addChild summary child 0 0 0 false
      | _ => pure summary) ({} : ApplicationSummary)
    modify ((function.name, summary) :: ·)
    return summary

/-- The ordinary lexicographic string order, exposed so concrete admission
proofs can reduce set membership across Lean module boundaries. -/
def compareSites (left right : String) : Ordering :=
  compareOfLessAndEq left right

instance : Std.TransCmp compareSites :=
  Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    String.le_antisymm String.le_trans String.le_total String.not_le

instance : Std.LawfulEqCmp compareSites where
  eq_of_compare h := compareOfLessAndEq_eq_eq String.le_refl String.not_le |>.mp h

/-- Balanced storage for exact effective-label membership. -/
abbrev SiteSet := Std.TreeSet String compareSites

structure SiteState where
  visits : Nat := 0
  bytes : Nat := 0
  seen : SiteSet := ∅

/-- Inserting one surviving label preserves the previous list-membership
criterion for duplicates. This is a collection invariant, not a second checker. -/
theorem siteSet_insert_agrees (seen : SiteSet) (previous : List String)
    (same : ∀ label, seen.contains label = previous.contains label)
    (site label : String) :
    (seen.insert site).contains label = (site :: previous).contains label := by
  simp only [Std.TreeSet.contains_insert, same, List.contains_cons,
    Std.LawfulBEqCmp.compare_beq_eq_beq]
  congr 1
  exact BEq.comm

/-- Each protocol root starts with the same empty collision namespace. -/
theorem siteSet_empty_agrees (label : String) :
    (∅ : SiteSet).contains label = ([] : List String).contains label := by
  simp

abbrev SiteM := StateT SiteState (Except String)

def chargeVisit : SiteM Unit := do
  let state ← get
  if state.visits >= Limits.applicationVisits then throw "structured-effective-site-limit"
  set { state with visits := state.visits + 1 }

/-- Check exact byte costs before constructing the shared process label.
The empty synthetic sentinel has zero cost; original traversal calls this only
for nonempty source sites. No generated-label concatenation precedes preflight. -/
def renderSite (sitePrefix : Option String) (site : String) : SiteM String := fun state =>
  let overhead := if site = "" then 0 else protocolSiteOverhead sitePrefix
  if overhead > Limits.siteBytes || site.utf8ByteSize > Limits.siteBytes - overhead then
    .error "structured-effective-site-limit"
  else
    let size := overhead + site.utf8ByteSize
    if size > Limits.applicationSiteBytes - state.bytes then .error "structured-effective-site-limit"
    else .ok (qualifyProtocolSite sitePrefix site, { state with bytes := state.bytes + size })

/-- Preflight checks precede construction of the shared label. -/
theorem renderSite_run (sitePrefix : Option String) (site : String) (before : SiteState) :
    (renderSite sitePrefix site).run before =
      let overhead := if site = "" then 0 else protocolSiteOverhead sitePrefix
      if overhead > Limits.siteBytes || site.utf8ByteSize > Limits.siteBytes - overhead then
        .error "structured-effective-site-limit"
      else if overhead + site.utf8ByteSize > Limits.applicationSiteBytes - before.bytes then
        .error "structured-effective-site-limit"
      else .ok (qualifyProtocolSite sitePrefix site,
        { before with bytes := before.bytes + (overhead + site.utf8ByteSize) }) := rfl

/-- Successful preflight returns the exact process label and changes only the
cumulative byte charge. Visits and the root collision set are preserved. -/
theorem renderSite_exact {sitePrefix : Option String} {site : String}
    {before after : SiteState} {rendered : String}
    (accepted : (renderSite sitePrefix site).run before = .ok (rendered, after)) :
    rendered = qualifyProtocolSite sitePrefix site ∧
      after = { before with bytes := before.bytes +
        (qualifyProtocolSite sitePrefix site).utf8ByteSize } := by
  rw [renderSite_run] at accepted
  dsimp only at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    constructor
    · rfl
    · rw [qualifyProtocolSite_utf8ByteSize]
      simp_all [protocolSiteSize]

/-- The checked charge is exactly the byte size of the emitted label. -/
theorem renderSite_accounting {sitePrefix : Option String} {site : String}
    {before after : SiteState} {rendered : String}
    (accepted : (renderSite sitePrefix site).run before = .ok (rendered, after)) :
    after.visits = before.visits ∧ after.seen = before.seen ∧
      after.bytes = before.bytes + rendered.utf8ByteSize := by
  rcases renderSite_exact accepted with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

/-- An overlong prefix refuses before the generated label is constructed. -/
theorem renderSite_overlong (sitePrefix : Option String) (site : String) (before : SiteState)
    (nonempty : site ≠ "") (overlong : Limits.siteBytes < protocolSiteOverhead sitePrefix) :
    (renderSite sitePrefix site).run before = .error "structured-effective-site-limit" := by
  rw [renderSite_run]
  simp [nonempty, overlong]

/-- Walk stored blocks, sharing visits and the collision namespace. Repeat
headers survive and do not introduce a prefix. Application headers are charged
but erased, and the callee is visited at its qualified prefix. -/
def visitBlock (application : Nat → Option String → Function → SiteM Unit)
    (snapshot : Snapshot) : Nat → Nat → Option String → Block → SiteM Unit
  | 0, _, _, _ => throw "structured-region-depth"
  | stored + 1, nesting, sitePrefix, .block instructions terminal => do
    for .instruction descriptor _ _ regions site in instructions do
      chargeVisit
      let rendered ← if site.isEmpty then pure "" else renderSite sitePrefix site
      match descriptor with
      | .protocolApply name _ =>
        let .function callee ← lookupDefinition snapshot name | throw "structured-call-kind"
        application nesting (some rendered) callee
      | _ =>
        if !site.isEmpty then
          let state ← get
          if state.seen.contains rendered then throw "structured-effective-site-collision"
          set { state with seen := state.seen.insert rendered }
      let nested ← match descriptor with
        | .protocolRepeat .. => do
          if nesting >= Limits.nesting then throw "structured-repeat-depth"
          pure (nesting + 1)
        | _ => pure nesting
      for .region _ _ body in regions do
        visitBlock application snapshot stored nested sitePrefix body
    chargeVisit
    match terminal with
    | .stop _ site =>
      if !site.isEmpty then
        let rendered ← renderSite sitePrefix site
        let state ← get
        if state.seen.contains rendered then throw "structured-effective-site-collision"
        set { state with seen := state.seen.insert rendered }
    | _ => pure ()

/-- Application frame capacity and expanded repeat nesting are independent.
Entering an application resets stored-block capacity, but preserves nesting. -/
def visitProtocolWith (snapshot : Snapshot) : Nat → Nat → Option String → Function → SiteM Unit
  | 0, _, _, _ => throw "structured-effective-site-depth"
  | frames + 1, nesting, sitePrefix, function =>
    visitBlock (visitProtocolWith snapshot frames) snapshot Limits.nesting nesting sitePrefix function.body

def visitProtocol (snapshot : Snapshot) (frames : Nat) (sitePrefix : Option String)
    (function : Function) : SiteM Unit :=
  visitProtocolWith snapshot frames 0 sitePrefix function

end ApplicationMetadata

/-- Native summary budgets are per function and cumulatively per original root. -/
def checkNativeApplicationBudgets (snapshot : Snapshot) :
    Except String (List (String × ApplicationSummary)) := do
  let computation : ApplicationMetadata.SummaryM Unit := do
    let mut work := 0
    let mut indices := 0
    let mut bytes := 0
    for function in snapshot.protocolFunctions do
      let summary ← ApplicationMetadata.summarizeFunction snapshot Limits.nesting function
      work ← ApplicationMetadata.boundedAdd Limits.applicationVisits work summary.work
      indices ← ApplicationMetadata.boundedAdd Limits.applicationIndices indices summary.indices
      bytes ← ApplicationMetadata.boundedAdd Limits.applicationSiteBytes bytes summary.siteBytes
  let (_, summaries) ← computation.run []
  return summaries

/-- Effective-site limits share counters across roots but reset the collision set. -/
def checkEffectiveProtocolSites (snapshot : Snapshot) : Except String Unit :=
  (do
    for function in snapshot.protocolFunctions do
      modify fun state : ApplicationMetadata.SiteState => { state with seen := ∅ }
      ApplicationMetadata.visitProtocol snapshot Limits.nesting none function).run' {}

end Zkc.Source.Structured
