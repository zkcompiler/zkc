module

public import Zkc.Core.Admission.Admit
public import Zkc.Frontend.Emit.Bindings
public import Zkc.Frontend.Basic.Log

@[expose] public section

set_option autoImplicit false

/-!
# Package admission reports

Each root carries the result of emitting and checking its source package.
A session records selected roots and their diagnostics. A completed selection
requires a checked package for each requested root and no errors or incomplete checks.
-/

namespace Zkc.Frontend

/-- Why an instance is a root of what a run emits. -/
inductive Emit.EntryKind where
  /-- A declaration without static parameters, or the protocol instance of a scheme. -/
  | root
  /-- An instance that a comment `// instantiate:` asks for. -/
  | directive
  /-- A default instance of a public declaration that no root reached (SP7). -/
  | defaultInstance
  deriving Inhabited, BEq, Repr

/-- The source compiler emits definitions under the project's linked vocabulary. The
same binding supplies the type of every occurrence of a primitive in the named program. -/
structure SourcePackage where
  bindings : Zkc.Vocabulary.Project.Bindings
  named : Core.NamedProgram bindings.vocabulary
  association : Core.Association

/-- Evidence indexed by the emitted source package. A consumer can transport a proof
about a typed program to this admission by checking the program's erasure. -/
structure SourcePackage.Admission (p : SourcePackage) where
  admitted : Core.Admitted p.bindings.vocabulary
  accepted : Core.admit p.named p.association = .ok admitted

/-- A report that can hold the result of any source root. -/
structure CheckedPackage extends SourcePackage where
  admitted : Core.Admitted bindings.vocabulary
  accepted : Core.admit named association = .ok admitted

def SourcePackage.checkEvidence (p : SourcePackage) :
    Except (List (Core.AdmissionRefusal p.bindings.vocabulary)) p.Admission :=
  match h : Core.admit p.named p.association with
  | .ok admitted => .ok ⟨admitted, h⟩
  | .error errors => .error errors

def SourcePackage.check (p : SourcePackage) :
    Except (List (Core.AdmissionRefusal p.bindings.vocabulary)) CheckedPackage :=
  p.checkEvidence.map fun evidence => ⟨p, evidence.admitted, evidence.accepted⟩

/-- What became of the package of a root. -/
inductive PackageOutcome where
  /-- Admitted by the core: elaborated, and every function and protocol passes the check of
  facts. -/
  | admitted (package : CheckedPackage)
  /-- Emitted and refused by the core. -/
  | refused (package : SourcePackage) (refusals : List (Core.AdmissionRefusal package.bindings.vocabulary))
  /-- Not emitted: a form that is not typed yet. -/
  | waiting (reason : String)
  /-- Typed, and not emitted: a specification item whose types or operations have no form in
  the core (`rational`, a `spec type`). -/
  | typedOnly (reason : String)
  /-- Not emitted: a defect of the frontend. -/
  | defect (message : String)
  /-- Not checked to the end: a budget of the compiler ran out (SP10). -/
  | exhausted (exhaustion : Exhaustion)

instance : Inhabited PackageOutcome := ⟨.waiting ""⟩

structure PackageReport where
  root : InstanceId
  /-- The root as source writes it. -/
  description : String
  outcome : PackageOutcome
  deriving Inhabited

/-- Why a root that was asked for is not in a result. -/
inductive Lack where
  /-- Refused: by the frontend, with an error logged, or by the core. -/
  | refused (reason : String)
  /-- Not computed: it needs a form of a later layer. -/
  | waiting (reason : String)
  /-- Not checked to the end: a budget of the compiler ran out. It is not refused (SP10). -/
  | exhausted (exhaustion : Exhaustion)
  /-- Without a package of its own: a specification item, typed and without a form in the
  core; a function bound to a row of the vocabulary. -/
  | noPackage (reason : String)
  /-- Not computed: a defect of the frontend. -/
  | defect (message : String)
  /-- The program has no root of the name asked for. -/
  | absent
  | ambiguous (places : Array String)
  deriving Inhabited

def Lack.describe : Lack → String
  | .refused reason => s!"refused: {reason}"
  | .waiting reason => s!"waiting for {reason}"
  | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"
  | .noPackage reason => s!"no package of its own: {reason}"
  | .defect message => s!"not computed, a defect of the frontend: {message}"
  | .absent => "no root of this name"
  | .ambiguous places => s!"ambiguous root: {", ".intercalate places.toList}"

/-- What a run made of the roots it was asked for: those it holds, each with what was made of it,
and those it lacks, each with why, beside the errors and incomplete checks from its log. -/
structure Admitted (α : Type) where
  private mk ::
  /-- The roots held, each named as source writes it, with what was made of it. -/
  held : Array (String × α)
  /-- The roots asked for that are not held, with why. -/
  lacking : Array (String × Lack)
  /-- The errors that the run reported, anywhere in the program. -/
  errors : Nat
  /-- The checks that the run left incomplete, anywhere in the program. -/
  incomplete : Nat

/-- Roots that are complete: each held, from a run that reported no error and left no check
incomplete. Only an admitted result makes one. -/
structure Completed (α : Type) where
  private mk ::
  held : Array (String × α)

end Zkc.Frontend

end

/- The bodies that make admitted and completed results are not exposed: they alone make them. -/
public section

namespace Zkc.Frontend

namespace Admitted

variable {α : Type}

/-- The result of the roots asked for, each held or lacking with why, with the errors and the
incomplete checks of the log of the run. -/
def ofLog (log : Log) (roots : Array (String × Except Lack α)) : Admitted α :=
  roots.foldl (init := ⟨#[], #[], log.errors, log.incomplete⟩) fun admitted (root, outcome) =>
    match outcome with
    | .ok value => { admitted with held := admitted.held.push (root, value) }
    | .error lack => { admitted with lacking := admitted.lacking.push (root, lack) }

/-- What the run reported that keeps every root from being complete, one line each. -/
def reported (admitted : Admitted α) : Array String :=
  (if admitted.errors == 0 then #[] else #[s!"{admitted.errors} errors are reported"]) ++
    (if admitted.incomplete == 0 then #[] else #[s!"{admitted.incomplete} checks are incomplete"])

/-- The roots that are not complete, one line each with why. -/
def lackingLines (admitted : Admitted α) : Array String :=
  admitted.lacking.map fun (root, lack) => s!"{root}: {lack.describe}"

/-- Every root asked for, complete: when the run reported no error, left no check incomplete,
and holds every root asked for. Otherwise what keeps it from that. This is what a request that
names its roots takes. -/
def complete (admitted : Admitted α) : Except (Array String) (Completed α) :=
  if admitted.errors == 0 && admitted.incomplete == 0 && admitted.lacking.isEmpty then
    .ok ⟨admitted.held⟩
  else .error (admitted.reported ++ admitted.lackingLines)

/-- The roots that are complete, each on its own: those held, when the run reported no error and
left no check incomplete, with those lacking and why. A root that waits keeps no other from
being complete; an error or an incomplete check anywhere keeps every one. -/
def completeRoots (admitted : Admitted α) :
    Except (Array String) (Completed α × Array (String × Lack)) :=
  if admitted.errors == 0 && admitted.incomplete == 0 then
    .ok (⟨admitted.held⟩, admitted.lacking)
  else .error admitted.reported

end Admitted

end Zkc.Frontend

end

@[expose] public section

namespace Zkc.Frontend

/-- Whether a name asked for names a root: the root as source writes it, or the declaration of
a default instance. -/
def namesRoot (name description : String) : Bool :=
  description == name || description == s!"default instance `{name}`"

/-- What a completed result holds for a root it was asked for. -/
def Completed.find? {α : Type} (completed : Completed α) (root : String) : Option α :=
  match completed.held.filter (fun (description, _) => namesRoot root description) with
  | #[(_, value)] => some value
  | _ => none

end Zkc.Frontend
