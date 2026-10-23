module

public import ZkcTools.StructuredSource.Discovery.View

@[expose] public section

/-! Bounded library-guided proposals. Structural features select a mathematical
template; they establish no helper equation, degree, representation or endpoint.
No protocol names, mangled-name fragments, origin hints or hashes dispatch this
search. An unrecognized helper or more than one compatible state is unresolved.
-/

namespace ZkcTools.StructuredSource.Discovery
open Zkc.Source Zkc.Source.Structured

inductive Template where
  | table | factors
  deriving DecidableEq, Repr

structure Features where
  sums : Nat := 0
  splits : Nat := 0
  products : Nat := 0
  folds : Nat := 0
  maps : Nat := 0
  unknown : Bool := false
  deriving Repr

def Features.join (left right : Features) : Features :=
  ⟨left.sums + right.sums, left.splits + right.splits,
    left.products + right.products, left.folds + right.folds,
    left.maps + right.maps, left.unknown || right.unknown⟩

/-- This vocabulary classifies actual primitive constructors, never labels. -/
def opFeatures : Op → Features
  | .exec (.vectorSum _) => { sums := 1 }
  | .exec (.vectorSplit _) => { splits := 1 }
  | .fieldMultiply _ => { products := 1 }
  | .fold _ => { folds := 1 }
  | .map _ => { maps := 1 }
  | .invoke _ => {}
  | .exec _ | .indexConstant _ | .indexEqual | .fieldConstant .. | .fieldAdd _ |
    .fieldSubtract _ | .fieldEqual _ | .fieldEmbed .. | .booleanConstant _ |
    .booleanAnd | .booleanOr | .booleanXor | .booleanEqual | .booleanNotEqual |
    .select _ | .boundedAt _ | .branch .. | .loop .. | .loopCondition .. |
    .guard | .mark _ => {}
  | _ => { unknown := true }

def helperFeatures (view : View) : Nat → String → Features
  | 0, _ => { unknown := true }
  | fuel + 1, name =>
    match view.helperBodies.find? (·.name == name) with
    | none => { unknown := true }
    | some helper => helper.raw.operations.foldl (fun features op =>
        op.helpers.foldl (fun features dependency =>
          features.join (helperFeatures view fuel dependency.name))
          (features.join (opFeatures op))) {}

structure Candidate where
  template : Template
  occurrence : Address
  context : List Address
  state : List Address
  message : List Address
  updates : List Address
  helpers : List String
  degree : Nat
  obligations : List String
  deriving Repr

structure Outcome where
  status : String
  candidates : List Candidate := []
  reasons : List String := []
  steps : Nat := 0
  deriving Repr

def commonObligations : List String :=
  ["ReferenceLaws", "exact-helper-body-laws", "all-replies-whole-process-verifier-equation",
   "fixed-root-target-anchoring", "actual-producer-completeness-compiled_ideal",
   "honest-delivery", "closed-shape-under-future-restrictions", "private-residual-preservation"]

/-- Search a repeat's actual callback occurrence. Distinct loop occurrences are
kept separate. Multiple unexplained layouts within one loop are not guessed. -/
def proposeLoop (view : View) (loop : Node) : Outcome := Id.run do
  let inCallback := fun (node : Node) => node.address.definition == loop.address.definition &&
    node.context == loop.context && (loop.address.region ++ [2, 0]).isPrefixOf node.address.region
  let nodes := view.nodes.filter inCallback
  let receives := nodes.filter fun node => node.tag == "receive" &&
    node.roleMap[1]? == some node.selectedRole
  let messages := receives.filter fun node => node.results.any fun value =>
    match value.type with | .field _ => true | _ => false
  if messages.isEmpty then return ⟨"unresolved", [], ["no-message-cut-in-visible-callback"], 0⟩
  let helpers := nodes.filter fun node => node.tag == "local-helper" && node.helper.isSome
  let featured := helpers.map fun node => (node, helperFeatures view 32 (node.helper.getD ""))
  if featured.any (fun (_, features) => features.unknown) then
    return ⟨"unresolved", [], ["unknown-helper-summary"], 0⟩
  let messageSources := featured.filter fun (_, features) => features.sums > 0 || features.folds > 0
  let updateSources := featured.filter fun (_, features) => features.splits > 0 && features.maps > 0
  if messageSources.isEmpty || updateSources.isEmpty then
    return ⟨"unresolved", [], ["missing-observation-or-restriction-helper"], 0⟩
  let vectors := ((messageSources ++ updateSources).flatMap fun (node, _) => node.arguments).filter fun value =>
    match value.type with | .vector _ => true | _ => false
  let state := (vectors.map (·.address)).eraseDups
  -- The concrete table encoding carries two scalar shape cells in addition to
  -- its vector. Keep these in helper arguments and the representation obligation.
  let factorShape := messages.length == 3 && state.length > 1
  let pairShape := messages.length == 2 && state.length == 1
  if !factorShape && !pairShape then
    return ⟨"unresolved", [], ["ambiguous-state-or-message-layout"], 0⟩
  let candidate : Candidate := {     template := if factorShape then .factors else .table,     occurrence := loop.address, context := loop.context, state,     message := messages.flatMap fun node => node.results.map (·.address),     updates := updateSources.map fun (node, _) => node.address,     helpers := (helpers.filterMap (·.helper)).eraseDups,     degree := if factorShape then 2 else 1,     obligations := commonObligations ++ (if factorShape then       ["separate-factor-representation", "active-variable-independent-weight",        "off-cube-observation-preservation", "reference-degree-at-most-two"] else       ["table-representation", "affine-message-representation"]) }
  return ⟨"proposed-unchecked", [candidate], [], 0⟩

/-- Independent arm boundary: this signature has no Program or manual-answer
argument. A timeout leaves an unresolved result, never a partial success. -/
def discover (view : View) (budget : Nat := 20000) : Outcome := Id.run do
  if view.steps > budget || budget == 0 then
    return ⟨"unresolved", [], ["search-timeout"], 0⟩
  let loops := view.nodes.filter (·.tag == "repeat")
  if loops.isEmpty then return ⟨"unresolved", [], ["no-visible-repeat"], view.steps⟩
  let results := loops.map (proposeLoop view)
  let status := if results.all (·.status == "proposed-unchecked") then "proposed-unchecked" else "unresolved"
  return { status, candidates := results.flatMap (·.candidates),     reasons := (results.flatMap (·.reasons)).eraseDups, steps := view.steps }

/-- Explicit descriptors are a first-class, fully charged intervention. They
must still pass the same downstream equations. No fallback enters discover. -/
def manual (candidates : List Candidate) : Outcome :=
  { status := if candidates.isEmpty then "unresolved" else "manual-unchecked",     candidates, reasons := ["author-supplied-reference-and-alignment"] }

end ZkcTools.StructuredSource.Discovery
