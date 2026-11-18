module

public import Zkc.Core.Transform.FunctionChecking

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}

namespace FunctionReport

def invalidClause (key : Key) : HeaderClause V → ProgramRefusal V
  | .positional q => refuseWhole key .summary (.requirement q.lift)
  | .assertion c => refuseWhole key .summary (.contractAssertion c)

def catalog (headers : List (FnHeader V)) (current : Key) : HeaderError V → ProgramRefusal V
  | .invalidSummary key c => invalidClause key c
  | .duplicateKeys =>
    let rec repeated : List Key → Option Key
      | [] => none
      | k :: ks => if k ∈ ks then some k else repeated ks
    let key := (repeated (headers.map (·.key))).getD current
    refuseWhole key .key (.key key)

/-- Convert an obligation at the stored-body entry point. -/
def obligation (headers : List (FnHeader V)) (current : FnHeader V)
    (r : Refusal (LocalRaw V)) : ProgramRefusal V :=
  let q := diagnosticClause headers current.summary.ensures r.concern r.index
  match r.concern, q with
  | .requirement op, some (.inl requirement) => ⟨.domain, r.place, .unjustified op requirement r.ranges⟩
  | .requirement op, some (.inr c) => ⟨.domain, r.place, .unjustifiedAssertion op c⟩
  | .requirement op, none => ⟨.domain, r.place, .operation op⟩
  | .guarantee, some (.inl requirement) => ⟨.guarantee, r.place, .unestablished requirement r.ranges⟩
  | .guarantee, some (.inr c) => ⟨.guarantee, r.place, .contractAssertion c⟩
  | .guarantee, none => ⟨.guarantee, r.place, .nothing⟩
  | .premise site _, _ => ⟨.lemmaPremise, r.place, .premise site r.index⟩
  | .invariant site _ kept, _ => ⟨.loopInvariant, r.place, .invariant site r.index kept⟩

def atSite (key : Key) (site : AnnotationSite) (rule : Rule) : ProgramRefusal V :=
  ⟨rule, site.toPlace key none, .annotationSite site⟩

/-- Identify every ill-typed or unresolved note in written order when preflight fails. -/
def structural (contracts : FunctionContracts hs) (f : TypedFn V hs hdr)
    (lemmas : List (Lemma V.Ty (LocalRaw V))) : DefinitionCheckError → List (ProgramRefusal V)
  | .contract => [refuseWhole hdr.key .summary .nothing]
  | .registry => [refuseWhole hdr.key .annotation .nothing]
  | .annotations =>
    let types := localAssertionTypes hs contracts.assertable
    (f.notes.filter fun note => !checkAnnotations types lemmas f.body [note]).map
      fun note => atSite hdr.key note.1 .annotation

def body (contracts : FunctionContracts hs) (source candidate : TypedFn V hs hdr)
    (lemmas : List (Lemma V.Ty (LocalRaw V))) :
    FunctionCheckError V → List (ProgramRefusal V) × List Place
  | .header k c => ([invalidClause k c], [])
  | .facts (.refused rs) => (rs.map (obligation hs hdr), [])
  | .comparison (.body rs ds) => (rs.map (obligation hs hdr), ds)
  | .facts (.definition reason) | .comparison (.candidate reason) =>
    (structural contracts candidate lemmas reason, [])
  | .comparison (.source reason) => (structural contracts source lemmas reason, [])

end FunctionReport

/-- The plain executable entry point has no producer for external facts. -/
def checkFactEvidence (f : TypedFn V hs hdr) : Except (List (ProgramRefusal V)) Unit :=
  match f.notes.find? (fun e => e.2.isGiven) with
  | some entry => .error [FunctionReport.atSite hdr.key entry.1 .factEvidence]
  | none => .ok ()

/-- Check the stored notes of an elaborated function and preserve its structured diagnostics. -/
def checkStored (f : TypedFn V hs hdr) : Except (List (ProgramRefusal V)) (List (Place × Nat)) := do
  let catalog ← (FunctionContracts.check hs).mapError fun reason => [FunctionReport.catalog hs hdr.key reason]
  let bounds ← (catalog.checkFunction f [] f.notes).mapError fun reason => (FunctionReport.body catalog f f [] reason).1
  checkFactEvidence f
  return bounds

/-- Each side uses its own lexical annotations. The candidate must justify all its facts. -/
def compareStored (source candidate : TypedFn V hs hdr) :
    Except (List (ProgramRefusal V) × List Place) (List (Place × Nat)) := do
  let catalog ← (FunctionContracts.check hs).mapError fun reason => ([FunctionReport.catalog hs hdr.key reason], [])
  let bounds ← (catalog.compareFunctions source candidate [] source.notes candidate.notes).mapError
    (FunctionReport.body catalog source candidate [])
  (checkFactEvidence candidate).mapError fun refusals => (refusals, [])
  return bounds

end Zkc.Core.BodyAnalysis
