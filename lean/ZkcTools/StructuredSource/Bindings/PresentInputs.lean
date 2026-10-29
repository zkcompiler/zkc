module

public import ZkcTools.StructuredSource.Bindings.Generate

@[expose] public section

/-! Present a root at its request's available inputs. This uses the same typed
normalizer and participant interpretation as the optional-input printer. The
emitted theorem retains the complete returned row and its visibility mask.
It covers the displayed input pattern; it does not assert availability for an
arbitrary adversarial input row. All source equations are kernel checked. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Bindings.PresentInputs
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcTools.StructuredSource.Presentation

def pattern (role : Nat) : (types : List Ty) → List (List Nat) → InputPattern types
  | [], _ => .nil
  | _ :: rest, scopes =>
      .cons (if (scopes.headD []).contains role then .present else .absent)
        (pattern role rest scopes.tail)

def inputValues (role : Nat) (types : List Ty) (scopes : List (List Nat))
    (names : List String) : String :=
  match types with
  | [] => ".nil"
  | _ :: rest =>
      if (scopes.headD []).contains role then
        app ".cons" [app "some" [names.headD "missingInput"], inputValues role rest scopes.tail names.tail]
      else app ".cons" ["none", inputValues role rest scopes.tail names]

/-- The selected role and all identities are data. No protocol name determines
normalization, presentation or the proof that links the result to the source. -/
def source (program : Program) (output : Output) (role : Nat) : Except String String := do
  unless role < program.payload.entry.roles.length do throw "input-view-role"
  let inputs := pattern role program.payload.entry.inputs program.payload.entry.inputScopes
  let signature : Signature := ⟨[], false, true, [], []⟩
  let .ok form := normalize signature program.payload.entry.body role
    program.payload.entry.roles.length inputs | throw "input-view-normalization"
  let naming : Naming signature.laws signature.callees inputs.scope := {
    carriers := .uniform "F" "G"
    context := "({} : ProtocolContext)"
    tables := "(helpers (F := F) (G := G) program.payload).toOn"
    results := "emptyResults (ringModel F G)"
    runs := "Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} " ++ toString role
    processes := "((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) [])" }
  let printed ← render naming .outputs form
  let names := printed.binders
  let parameters := " ".intercalate ((inputs.scope.zip names).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
  let arguments := " ".intercalate names
  let supplied := inputValues role program.payload.entry.inputs program.payload.entry.inputScopes names
  let binders := valuesText names
  let masked := "maskValues " ++ toString role ++ " program.payload.entry.outputScopes"
  return "module\n\npublic import " ++ output.sourceModule ++
    "\npublic import Zkc.Source.Structured.Bindings.Assembly\n" ++
    "public import Zkc.Source.Structured.NormalForm.Sites\n\n@[expose] public section\n\n" ++
    "/-! Generated present-input view of the admitted source. Regenerate. -/\n" ++
    "namespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured NormalForm Bindings\n" ++
    "set_option maxRecDepth 20000\nset_option maxHeartbeats 1500000\n" ++
    "noncomputable section\n\nabbrev program := " ++ output.programExpression ++ "\n" ++
    "def signature : Signature := ⟨[], false, true, [], []⟩\n" ++
    "def inputPattern : InputPattern program.payload.entry.inputs := " ++ patternText inputs ++ "\n\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n" ++
    declarations (out := program.payload.entry.outputs) naming .outputs printed { name := "root" } ++
    "\ntheorem normalized : normalize signature program.payload.entry.body " ++ toString role ++
    " program.payload.entry.roles.length inputPattern = .ok rootForm := by kernel_rfl\n\n" ++
    "def inputs " ++ parameters ++ " : Values (Component (assignment F G)) program.payload.entry.inputs :=\n  " ++ supplied ++ "\n\n" ++
    "noncomputable def view " ++ parameters ++ " :=\n  (rootProcess (F := F) (G := G) " ++ arguments ++
    ").bind fun out => PIR.Process.done (" ++ masked ++ " out)\n\n" ++
    "theorem source_equation " ++ parameters ++ " :\n" ++
    "    program.participant F G " ++ toString role ++ " (inputs (F := F) (G := G) " ++ arguments ++ ") = view (F := F) (G := G) " ++ arguments ++ " := by\n" ++
    "  have equation := invocation (F := F) (G := G) program.payload program.payload.entry\n" ++
    "    (List.get_mem _ _) signature " ++ toString role ++ " program.payload.entry.roles.length inputPattern\n" ++
    "    rootForm normalized root_calls (emptyResults (ringModel F G))\n" ++
    "    ((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) []) {} (RosterDistinct.root _ _)\n" ++
    "    (inputs (F := F) (G := G) " ++ arguments ++ ") (" ++ binders ++ ") (by kernel_rfl) (emptyLaws _ _) (fun entry => entry.elim0)\n" ++
    "  exact (program.payload.protocolTable_forgetSites (F := F) (G := G) program.payload.entry.signature {} " ++
    toString role ++ " (inputs (F := F) (G := G) " ++ arguments ++ ")).trans\n" ++
    "    (equation.trans (congrArg (fun p => p.bind fun out => PIR.Process.done (" ++ masked ++ " out))\n" ++
    "      (root_presentation (F := F) (G := G) " ++ arguments ++ ")))\n\nend\nend " ++ output.moduleName ++ "\n"

end ZkcTools.StructuredSource.Bindings.PresentInputs
