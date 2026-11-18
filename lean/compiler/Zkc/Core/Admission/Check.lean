module

public import Zkc.Core.Admission.Admission
public import Zkc.Core.Admission.Projections
public import Zkc.Core.Admission.Elaboration
public import Zkc.Core.Transform.Assured

@[expose] public section

/-!
Each definition elaborates against its preceding headers. A function checks its stored
contracts and annotations. A protocol checks its projections at the participant numbers in
its header. The bounds carry the definition key and optional role that produced them.
The incremental frontend entry and whole-program admission both use `checkDefinition`.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

open BodyAnalysis BodyAnalysis.RoleContracts

/-- A protocol contributes bounds from all of its declared projections. -/
def ProtocolAccepted {hs : Headers V} (hdr : ProtocolHeader V) {inputs : Names hdr.ins}
    (body : Prot V hs hdr inputs) (bounds : List (Place × Nat)) : Prop :=
  ∃ (catalog : FunctionContracts hs.fns)
    (evidence : CheckedProjections catalog hdr body (List.range hdr.roles)), evidence.bounds = bounds

def Elaborated.Checked {hs : Headers V} : Elaborated V hs → List (Place × Nat) → Prop
  | .fn _ inputs body ok _ notes, bounds => (TypedFn.mk inputs body ok notes).check = .ok bounds
  | .protocol hdr _ body _ _, bounds => ProtocolAccepted hdr body bounds

/-- Inspect an elaborated definition once and retain its check as erased evidence. -/
def Elaborated.checkBounds {hs : Headers V} (e : Elaborated V hs) :
    Except (List (AdmissionRefusal V)) {bs : List (Place × Nat) // e.Checked bs} :=
  match e with
  | .fn _ inputs body ok _ notes =>
    match checked : (TypedFn.mk inputs body ok notes).check with
    | .error errs => .error (errs.map fun f => .definition (.fn f))
    | .ok bs => .ok ⟨bs, checked⟩
  | .protocol hdr _ body _ _ =>
    match FunctionContracts.check hs.fns with
    | .error err => .error [.definition (.fn (FunctionReport.catalog hs.fns hdr.key err))]
    | .ok catalog =>
      match checkDeclared catalog hdr body with
      | .error errors => .error (errors.flatMap fun (r, err) => projectionRefusals catalog hdr.key r err)
      | .ok evidence => .ok ⟨evidence.bounds, catalog, evidence, rfl⟩

/-- Elaborate the named definition and check its function or every declared role projection. -/
def checkDefinition (hs : Headers V) (definition : Definition V) :
    Except (List (AdmissionRefusal V)) (Elaborated V hs × List (Place × Nat)) := do
  let e ← (elaborateDefinition hs definition).mapError (List.map AdmissionRefusal.definition)
  let bounds ← e.checkBounds
  return (e, bounds.val)

/-- The check of one definition against the headers of those before it: the headers with the
definition's. -/
def check (hs : Headers V) (definition : Definition V) :
    Except (List (AdmissionRefusal V)) (Headers V) :=
  (checkDefinition hs definition).map fun checked => checked.1.headers

/-- A check of definitions one at a time, each against the headers that the check of those
before it gave. -/
def checkAll (step : Headers V → Definition V → Except (List (AdmissionRefusal V)) (Headers V)) :
    Headers V → List (Definition V) → Except (List (AdmissionRefusal V)) (Headers V)
  | hs, [] => .ok hs
  | hs, definition :: rest => (step hs definition).bind fun hs' => checkAll step hs' rest

/-- Each definition passed its applicable checks and contributed exactly its bounds, in
reverse declaration order. Bounds of a protocol are ordered by participant number. -/
def Defs.Accepted : {hs : Headers V} → Defs V hs → List (Place × Nat) → Prop
  | _, .nil, bounds => bounds = []
  | _, .fn hdr inputs body ok rest notes, bounds => ∃ mine others,
      (TypedFn.mk inputs body ok notes).check = .ok mine ∧
        Defs.Accepted rest others ∧ bounds = mine ++ others
  | _, .protocol hdr _ body _ rest, bounds => ∃ mine others,
      ProtocolAccepted hdr body mine ∧ Defs.Accepted rest others ∧ bounds = mine ++ others

end

end Zkc.Core
