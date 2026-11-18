module

public import Zkc.Core.Facts.Body.Roles
public import Zkc.Core.Program.Typed
public import Zkc.Core.Program.Project
public import Zkc.Core.Program.Stepped

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts
variable {V : Vocabulary} {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
variable (header : ProtocolHeader V) {inputs : Names header.ins}

/-- Check the actual body of one role. The protocol header supplies its identity and ports.
The caller supplies any contract and annotations for this role. -/
def checkRole (body : RoleP V hs r header inputs)
    (summary : Contract (RoleRaw V) := ⟨[], []⟩) (lemmas : List (Lemma (LTy V) (RoleRaw V)) := [])
    (notes : Annotations (RoleRaw V) := []) : Except (FactCheckError (RoleRaw V)) (List (Place × Nat)) :=
  checkFacts (config catalog r header.key lemmas) notes summary inputs body

/-- Compare two role bodies using the ordered event identities of the role dialect. -/
def compareRoles {otherInputs : Names header.ins} (source : RoleP V hs r header inputs)
    (candidate : RoleP V hs r header otherInputs) (summary : Contract (RoleRaw V) := ⟨[], []⟩)
    (lemmas : List (Lemma (LTy V) (RoleRaw V)) := [])
    (sourceNotes candidateNotes : Annotations (RoleRaw V) := []) :
    Except (FollowError (RoleRaw V)) (List (Place × Nat)) :=
  followChecked (config catalog r header.key lemmas) (roleChecks r) header.key sourceNotes candidateNotes
    summary inputs otherInputs source candidate

end Zkc.Core.BodyAnalysis.RoleContracts
