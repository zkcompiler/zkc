import Zkc.Core.Statements

/-!
Each consumer's side, written against the core: what a frontend emits, what the
executor is called with, what a proof is about, and the erased program of a role.
-/

namespace Zkc.Core

/-! ## What a frontend emits -/

inductive SigmaType where
  | scalar
  | point
deriving DecidableEq

inductive SigmaRow where
  /-- The multiple of the generator. -/
  | base
  | add
  | mul
  /-- The multiple of a point. -/
  | scale
  | plus
  | same
deriving DecidableEq

abbrev scalar : Ty SigmaType := .nominal .scalar
abbrev point : Ty SigmaType := .nominal .point

/-- A vocabulary of a group and its scalars, with one law: a uniform scalar. -/
def sigmaVocabulary : Vocabulary where
  TypeKey := SigmaType
  RowKey := SigmaRow
  LawKey := Unit
  row r := some <| match r with
    | .base => ⟨[scalar], [point], .pure⟩
    | .add => ⟨[scalar, scalar], [scalar], .pure⟩
    | .mul => ⟨[scalar, scalar], [scalar], .pure⟩
    | .scale => ⟨[scalar, point], [point], .pure⟩
    | .plus => ⟨[point, point], [point], .pure⟩
    | .same => ⟨[point, point], [.bool], .pure⟩
  law _ := some ⟨[], scalar⟩
  literal _ _ := true
  decided key _ _ found kind := by cases key <;> cases found <;> cases kind

def proverRole : Role := 0
def verifierRole : Role := 1

/-- Knowledge of a discrete logarithm, by names. The prover holds the witness `0`; both hold
the statement `1`. Who computes, who sends and who checks is written; nothing else is. -/
def sigmaByNames : NamedProgram sigmaVocabulary where
  definitions := [
    .protocol ⟨0⟩ 2 [⟨scalar, [proverRole]⟩, ⟨point, [proverRole, verifierRole]⟩] []
      (.mk [0, 1] [
        .op ⟨10⟩ [2] (.event (.given (.coin ()) proverRole []) scalar) [],
        .op ⟨11⟩ [3] (.compute [proverRole] (.row .base)) [2],
        .op ⟨12⟩ [4] (.event (.flow .message proverRole [verifierRole]) point) [3],
        .op ⟨13⟩ [5] (.event (.given (.coin ()) verifierRole [proverRole]) scalar) [],
        .op ⟨14⟩ [6] (.compute [proverRole] (.row .mul)) [5, 0],
        .op ⟨15⟩ [7] (.compute [proverRole] (.row .add)) [2, 6],
        .op ⟨16⟩ [8] (.event (.flow .message proverRole [verifierRole]) scalar) [7],
        .op ⟨17⟩ [9] (.compute [verifierRole] (.row .base)) [8],
        .op ⟨18⟩ [10] (.compute [verifierRole] (.row .scale)) [5, 1],
        .op ⟨19⟩ [11] (.compute [verifierRole] (.row .plus)) [4, 10],
        .op ⟨20⟩ [12] (.compute [verifierRole] (.row .same)) [9, 11],
        .guard ⟨21⟩ [verifierRole] 12 .reject]
        [])]

/-- Nothing beyond the definitions. -/
def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- Its scheme: the entry, the role kinds, a derivation and a layout. Who proves follows from
the shape. -/
def sigmaScheme : Declaration where
  key := ⟨1⟩
  entry := ⟨0⟩
  kinds := [.online, .online]
  construction := .derived ⟨[], []⟩
  prover := none
  layout := some ⟨⟨[], []⟩, [], []⟩
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

/-! ## The members that a scheme generates -/

/-- What a scheme generates for its users besides `prove` and `verify`: the types of its
statement and of its witness. -/
structure Members (V : Vocabulary) where
  statement : List V.Ty
  witness : List V.Ty

/-- The generated members of a deployed scheme, from its prover and verifier. -/
def Deployed.members {V : Vocabulary} (d : Deployed V) : Option (Members V) :=
  d.roles.map fun roles => ⟨statementOf d.entry roles.1 roles.2, witnessOf d.entry roles.1 roles.2⟩

/-! ## What the executor is called with -/

section
variable {V : Vocabulary} (c : Functions V)

/-- A frontend calls `admit`, `deploy`, `prove` and `verify`, and nothing else of the core. -/
def compile (named : NamedProgram V) (assoc : Association) (scheme : Declaration) :
    Except (List (AdmissionRefusal V) ⊕ List (ProgramRefusal V)) (Deployed V) := do
  let admitted ← (c.admit named assoc).mapError Sum.inl
  (c.deploy admitted scheme).mapError Sum.inr

/-- A proof and its check, with the executor of the core. -/
def proveAndVerify (d : Deployed V) (M : Model V) (prover verifier : Role)
    (proverIns : HList (RV M prover) d.entry.ins) (verifierIns : HList (RV M verifier) d.entry.ins)
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (source : Source M) (limit : Nat) : Option (HList (RV M verifier) d.entry.outs) :=
  (prove c.execute d M prover proverIns first source limit).bind fun proof =>
    verify c.execute d M verifier verifierIns (cast (congrArg (HList M.Val) matched) proof)
      source limit

end

/-! ## What a proof is about -/

section
variable {V : Vocabulary}

/-- The completeness of a protocol, which its author proves: on inputs in its relation,
every run returns. It is about the protocol's process, found by key in the admitted
program. With `Statements.complete` it gives the completeness of every non-interactive
scheme of the protocol whose suite and layout satisfy their laws. -/
def protocolComplete (a : Admitted V) (M : Model V) (entry : Key)
    (related : ∀ hdr : ProtocolHeader V, HList (LVal M) hdr.ins → Prop) : Prop :=
  ∀ (hdr : ProtocolHeader V) (p : Member a.program.headers.protocols hdr),
    a.program.find entry = some (.protocol p) →
    ∀ (ins : HList (LVal M) hdr.ins) (source : Source M) (e : GEnd _), related hdr ins →
      GExec M source (protocolMeaning M a.program p [] ins) e → ∃ out, e = .returned out

/-- Two runs of a protocol, as their events in order, fork: an equal prefix, then the same
occurrence with different values. This is what an extractor reads. -/
def forkOf (M : Model V) (first second : List (Event M)) : Prop :=
  Fork M first second

end

/-! ## The worked example, as what a core must do with it -/

section
variable (c : Functions sigmaVocabulary)

/-- The worked program is admitted. -/
def sigmaAdmitted : Prop := ∃ a, c.admit sigmaByNames noAssociation = .ok a

/-- Its scheme is deployed, with the first role proving and the second verifying. -/
def sigmaDeployed : Prop :=
  ∀ a, c.admit sigmaByNames noAssociation = .ok a →
    ∃ d, c.deploy a sigmaScheme = .ok d ∧ d.roles = some (proverRole, verifierRole)

end

/-! ## The erased program of a role -/

section
variable {V : Vocabulary} (c : Functions V)

/-- The erased program of each role of each protocol: its projection, erased. -/
def Defs.erasedRole : {hs : Headers V} → Defs V hs → {hdr : ProtocolHeader V} →
    Member hs.protocols hdr → Role → Region (RoleRaw V) (List Role)
  | _, .fn _ _ _ _ rest _, _, x, r => rest.erasedRole x r
  | _, .protocol _ _ body _ _, _, .head, r => c.eraseRole r (project r body)
  | _, .protocol _ _ _ _ rest, _, .tail x, r => rest.erasedRole x r

end

end Zkc.Core
