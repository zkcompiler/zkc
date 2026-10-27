module

public import Zkc.Construction.SourceOccurrences
public import Zkc.Construction.DomainExecution
public import Zkc.Source.Structured.Occurrence

@[expose] public section

/-! Checked nominal origins for actions of an original source occurrence view.
Candidate templates are proposals. The resolver checks the exact original
source path, source event, static enclosing repeat sites, and actual dynamic
indices before producing the key used by the nominal constructed evaluator.
An absent or ambiguous candidate refuses; equal host carrier types confer no
authority. The caller still proves that its stack comes from source execution.
-/
set_option autoImplicit false
namespace Zkc.Construction.OccurrenceResolution
open Zkc.Source

abbrev Frames := List Structured.Occurrence.Frame

/-- Both static repeat sites and dynamic coordinates are checked. Merely
matching the number of enclosing repeats does not identify the occurrence. -/
def matchesOccurrence (snapshot : Structured.Snapshot) (context : Context) (expected : Origin)
    (frames : Frames) (template : Template) : Bool :=
  SourceOccurrences.valid snapshot context template &&
    (SourceOccurrences.repeatSites template == frames.map (·.site)) &&
    (template.origin context == some expected) &&
    (Domain.templateOrigin context template (frames.map (·.index)) ==
      some (Domain.atCoordinates expected (frames.map (·.index))))

/-- Missing and duplicate associations stay unresolved; discovery is not trusted. -/
def resolve (snapshot : Structured.Snapshot) (context : Context) (expected : Origin)
    (frames : Frames) (candidates : List Template) : Option Origin :=
  match candidates.filter (matchesOccurrence snapshot context expected frames) with
  | [_] => some (Domain.atCoordinates expected (frames.map (·.index)))
  | _ => none

/-- Source admission can be checked once for a fixed proposal list. Dynamic
resolution still checks the complete static stack, nominal origin and indices. -/
theorem filter_validated (snapshot : Structured.Snapshot) (context : Context)
    (expected : Origin) (frames : Frames) (candidates : List Template)
    (valid : ∀ candidate ∈ candidates, SourceOccurrences.valid snapshot context candidate = true) :
    candidates.filter (matchesOccurrence snapshot context expected frames) =
      candidates.filter (fun template =>
        (SourceOccurrences.repeatSites template == frames.map (·.site)) &&
        (template.origin context == some expected) &&
        (Domain.templateOrigin context template (frames.map (·.index)) ==
          some (Domain.atCoordinates expected (frames.map (·.index))))) := by
  apply List.filter_congr
  intro candidate member
  simp only [matchesOccurrence, valid candidate member, Bool.true_and]

/-- Every resolved key has the exact expected nominal base and reached indices. -/
theorem resolved_origin {snapshot : Structured.Snapshot} {context : Context} {expected origin : Origin}
    {frames : Frames} {candidates : List Template}
    (resolved : resolve snapshot context expected frames candidates = some origin) :
    origin = Domain.atCoordinates expected (frames.map (·.index)) := by
  unfold resolve at resolved
  split at resolved
  · exact (Option.some.inj resolved).symm
  · cases resolved

/-- A successful resolution contains an exact source-owned candidate, not just
an origin whose spelling happens to agree. -/
theorem resolved_source {snapshot : Structured.Snapshot} {context : Context} {expected origin : Origin}
    {frames : Frames} {candidates : List Template}
    (resolved : resolve snapshot context expected frames candidates = some origin) :
    ∃ template ∈ candidates,
      SourceOccurrences.expected snapshot context template = some template.event ∧
      SourceOccurrences.repeatSites template = frames.map (·.site) ∧
      template.origin context = some expected ∧
      Domain.templateOrigin context template (frames.map (·.index)) = some origin := by
  have key := resolved_origin resolved
  unfold resolve at resolved
  split at resolved
  · rename_i template found
    have member : template ∈ candidates.filter (matchesOccurrence snapshot context expected frames) := by
      rw [found]
      exact List.mem_singleton_self _
    obtain ⟨member, valid⟩ := List.mem_filter.mp member
    simp only [matchesOccurrence, Bool.and_eq_true, beq_iff_eq] at valid
    refine ⟨template, member, (SourceOccurrences.valid_iff _ _ _).mp valid.1.1.1,
      valid.1.1.2, valid.1.2, ?_⟩
    simpa only [key] using valid.2
  · cases resolved

/-- Dynamic coordinates never change the request's nominal reply carrier. -/
theorem atCoordinates_request (origin : Origin) (coordinates : List Nat) :
    (Domain.atCoordinates origin coordinates).request = origin.request := by
  unfold Domain.atCoordinates
  split <;> rfl

/-- No admissibility restriction on an adversary's oracle queries is introduced
by source key resolution. This lemma concerns the one resolved source request. -/
theorem resolved_request {snapshot : Structured.Snapshot} {context : Context} {expected origin : Origin}
    {frames : Frames} {candidates : List Template}
    (resolved : resolve snapshot context expected frames candidates = some origin) :
    origin.request = expected.request := by
  rw [resolved_origin resolved, atCoordinates_request]

end Zkc.Construction.OccurrenceResolution
