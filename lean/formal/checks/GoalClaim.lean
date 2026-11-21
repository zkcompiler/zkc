import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.PrintedPackageSupport

/-!
What written soundness goals of one scheme claim, as one package.

A goal names a protocol and, through its clause, a relation at the proof values that the goal
gives. `goalClaims` returns them in one package: the relations are instantiated one after
another in the state of the root, and the package is what the root reaches followed by what
each relation adds.

The check reads sources with the frontend and asserts, of what it returns:

- the definitions of the root's own package are the first of the claims', each with the stored
  text that it has alone, whatever the relation is and whichever goals are read;
- two goals of one scheme with two proof values give two relations with two keys, and a goal
  read twice gives one;
- a function that the verifier and the relation both call is one definition;
- a relation that the relation applies comes before it;
- the ports at the statement and at the witness, for a clause written short and one that gives
  the witness; an operand that is no port is refused.

Then Lean is run on three modules for the two goals of the reference case `N-GL2a`.

- The proof module has the root's package in a namespace of its own and the claims' package.
  The kernel accepts: the stored definitions of the claims are those of the deployed package
  followed by the two relations; the header of the root is the same; the process of each role
  of the root in the claims' package is its process in the deployed package, for every model,
  every start and all inputs; and in every program that admission gives for the claims'
  package the root is found by its key among the protocols and each relation by its key among
  the functions.
- The comparison module has the claims' package and the frontend: the program by names that
  Lean reads is the one that the frontend emits for the claims, and its first definitions are
  those of the root's own package.
- The control has, as the deployed package, the root of the same source with the guard of the
  verifier negated. Lean refuses it where it states that the deployed definitions come first.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace GoalClaimCheck

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- The stored text of each definition of a package, with its key. -/
def storedTexts (p : SourcePackage) : List (Nat × String) :=
  p.named.definitions.map fun d => (d.key.number, storedDefinition (b := p.bindings) d)

def packageOf (claims : GoalClaims) : SourcePackage := claims.emission.package noAssociation

/-- The claims of goals of a source: the deployed definitions are the first of their package,
what follows ends in the relation of the last goal, and no two definitions have one key. -/
def read (text : String) (goals : List String) : IO (AdmittedRoot × GoalClaims) := do
  let some first := goals.head? | throw (IO.userError "no goal")
  let root ← IO.ofExcept (goalRoot text first)
  let claims ← IO.ofExcept (goalClaims root goals)
  let deployed := storedTexts (root.emission.package noAssociation)
  let all := storedTexts (packageOf claims)
  unless all.take deployed.length == deployed do
    throw (IO.userError s!"{goals}: the deployed definitions are not the first of the claims' package")
  let added := (all.drop deployed.length).map (·.1)
  unless claims.goals.all (added.contains ·.relation) && added.getLast? == claims.goals.getLast?.map (·.relation) do
    throw (IO.userError s!"{goals}: the relations are not what follows the deployed definitions")
  unless (all.map (·.1)).eraseDups.length == all.length do
    throw (IO.userError s!"{goals}: two definitions of the claims' package have one key")
  return (root, claims)

/-- The claim of the one goal read. -/
def only (claims : GoalClaims) : IO ClaimedGoal :=
  match claims.goals with
  | [claimed] => pure claimed
  | _ => throw (IO.userError "expected the claim of one goal")

/-- The source with its one occurrence of `before` replaced. -/
def edit (text before after : String) : IO String := do
  unless (text.splitOn before).length == 2 do
    throw (IO.userError s!"expected one occurrence of {before}")
  return text.replace before after

def expect (title : String) (holds : Bool) : IO Unit :=
  unless holds do throw (IO.userError title)

def imports (others : List String) : String :=
  String.join ((Written.packageImports ++ others).map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The theorems of the proof module, whose axioms the check reads. -/
def theorems : List String :=
  ["deployed_first", "same_header", "prover_same", "verifier_same", "members"]

/-- The member of a list of headers that is `depth` places after its head. -/
def memberAt : Nat → String
  | 0 => "Member.head"
  | depth + 1 => s!"(Member.tail {memberAt depth})"

/-- The proof module: the deployed package in a namespace of its own, the claims' package, and
what relates them. `relations` are the keys of the relations in the order of the package; no
other function follows the deployed definitions. -/
def proofModule (name : String) (deployed claims : SourcePackage) (root : Nat)
    (relations : List Nat) : String :=
  let sameProcess (theorem_ : String) (role : Nat) :=
    s!"theorem {theorem_} (M : Model V) (path : List Frame)\n" ++
    s!"    (inputs : HList (RV M {role}) Deployed.header{root}.ins) :\n" ++
    s!"    roleMeaning M installed (Member.head : Member installed.headers.protocols Deployed.header{root})\n" ++
    s!"        {role} path inputs =\n" ++
    s!"      roleMeaning M Deployed.installed\n" ++
    s!"        (Member.head : Member Deployed.installed.headers.protocols Deployed.header{root}) {role} path inputs := by\n" ++
    "  kernel_rfl\n"
  let added := ", ".intercalate (relations.map (s!"stored{·}"))
  -- the functions of a program stand last first
  let found := relations.reverse.zipIdx.reverse.map fun (relation, depth) =>
    (s!"    ∧ (∃ relation : Member a.program.headers.fns header{relation},\n" ++
      s!"      a.program.find ⟨{relation}⟩ = some (.fn relation))", s!"⟨{memberAt depth}, by kernel_rfl⟩")
  imports [] ++ s!"namespace {name}\nnamespace Deployed\n" ++ (Written.package deployed).text ++
  "end Deployed\n" ++ (Written.package claims).text ++
  "noncomputable section\n" ++
  s!"theorem deployed_first : stored.definitions = Deployed.stored.definitions ++ [{added}] := rfl\n" ++
  s!"theorem same_header : header{root} = Deployed.header{root} := by kernel_rfl\n" ++
  sameProcess "prover_same" 0 ++ sameProcess "verifier_same" 1 ++
  "theorem members {a : Admitted V} (admitted : admit stored association = .ok a) :\n" ++
  s!"    (∃ root : Member a.program.headers.protocols header{root},\n" ++
  s!"      a.program.findProtocol ⟨{root}⟩ = some ⟨header{root}, root⟩)\n" ++
  "\n".intercalate (found.map (·.1)) ++ " := by\n" ++
  "  have same := readback admitted\n  generalize a.program = p at same\n  subst same\n" ++
  s!"  exact ⟨⟨Member.head, by kernel_rfl⟩, {", ".intercalate (found.map (·.2))}⟩\n" ++
  "end\n" ++ String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

def comparisonModule (name text : String) (goals : List String) (claims : SourcePackage) : String :=
  imports ["Zkc.Tests.Frontend.PrintedPackageSupport"] ++ s!"namespace {name}\n" ++
  (Written.package claims).text ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalClaims {literal text} {reprStr goals} " ++
  s!"({Written.associationTerm noAssociation}) stored association\nend {name}\n"

/-- Lean on a module, in the formal package, as a task. -/
def start (work : System.FilePath) (name text : String) :
    IO (Task (Except IO.Error (Bool × String))) := do
  let path := work / s!"{name}.lean"
  IO.FS.writeFile path text
  IO.asTask (runLakeLean path)

def run (corpus : System.FilePath) (work : System.FilePath) : IO Unit := do
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let fixture (id : String) : IO String := match (blocks.find? (·.id == id)).bind (·.files[0]?) with
    | some text => pure text
    | none => throw (IO.userError s!"missing the reference case {id}")
  let count ← fixture "N-GL2a"

  -- Two goals of one scheme: two relations with two keys, one deployed part, the table at the
  -- statement; a goal read twice claims one relation.
  let (root, both) ← read count ["loose", "strict"]
  let [loose, strict] := both.goals | throw (IO.userError "expected the claims of two goals")
  expect "the two goals of Count<8> claim one relation" (loose.relation != strict.relation)
  expect "a relation has the key of the root" (loose.relation != root.id && strict.relation != root.id)
  expect "the claims of two goals do not add two definitions"
    ((storedTexts (packageOf both)).length == (storedTexts (root.emission.package noAssociation)).length + 2)
  expect "the operands of NearZero(xs)" (loose.statement == #[0] && loose.witness == some #[])
  let (_, twice) ← read count ["loose", "loose"]
  expect "a goal read twice claims two relations"
    ((storedTexts (packageOf twice)).length == (storedTexts (root.emission.package noAssociation)).length + 1)

  -- Another relation changes no deployed definition, and changes the relation.
  let (_, looseAlone) ← read count ["loose"]
  let (_, stricter) ← read (← edit count "else 1) <= e\n" "else 1) < e\n") ["loose"]
  expect "a change of the relation changed a deployed definition"
    ((storedTexts (packageOf stricter)).dropLast == (storedTexts (packageOf looseAlone)).dropLast)
  expect "a change of the relation did not change the relation"
    ((storedTexts (packageOf stricter)).getLast? != (storedTexts (packageOf looseAlone)).getLast?)

  -- A function that the verifier and the relation both call is one definition.
  let helper ← edit count "section <n: nat, spec e: nat>:" "def zero(x: F) -> bool: x == 0\nsection <n: nat, spec e: nat>:"
  let helper ← edit helper "if xs[i] == 0 then 0 else 1" "if zero(xs[i]) then 0 else 1"
  let helper ← edit helper "guard @V xs[z] == 0" "guard @V zero(xs[z])"
  let (sharedRoot, shared) ← read helper ["loose"]
  expect "a function that the verifier and the relation call is not one definition"
    ((storedTexts (sharedRoot.emission.package noAssociation)).length == 2 &&
      (storedTexts (packageOf shared)).length == 3)

  -- A relation that the relation applies comes before it, after the deployed definitions.
  let (nestedRoot, nested) ← read (← fixture "N-GL2g") ["placed"]
  expect "a relation that the relation applies is not a definition before it"
    ((storedTexts (packageOf nested)).length == (storedTexts (nestedRoot.emission.package noAssociation)).length + 2)

  -- The witness: a relation with a witness parameter, the clause with the witness and short.
  let pair ← fixture "N-GL3b"
  let near ← only (← read pair ["sound"]).2
  expect s!"the operands of Near(x; w): {near.statement} {near.witness}"
    (near.statement == #[0] && near.witness == some #[1])
  let short ← only (← read (← edit pair "proves near: Near(x; w)" "proves @V near: Near(x)") ["sound"]).2
  expect "the operands of Near(x), written short" (short.statement == #[0] && short.witness == none)

  -- An operand that is no port.
  let computed ← edit count "proves @V NearZero(xs)" "proves @V NearZero(xs ++ [])"
  match (goalRoot computed "loose").bind (goalClaims · ["loose"]) with
  | .ok _ => throw (IO.userError "an operand that is no port was read as a port")
  | .error why => expect s!"an operand that is no port: {why}" (why.contains "WK-CLAUSE")

  -- Lean: the claims' package against the deployed package.
  let deployed := root.emission.package noAssociation
  let relations := [loose.relation, strict.relation]
  let negated ← IO.ofExcept (goalRoot (← edit count "guard @V xs[z] == 0" "guard @V xs[z] != 0") "loose")
  let proof ← start work "Claims" (proofModule "Claims" deployed (packageOf both) root.id relations)
  let comparison ← start work "ClaimsSource"
    (comparisonModule "ClaimsSource" count ["loose", "strict"] (packageOf both))
  let control ← start work "ClaimsControl"
    (proofModule "ClaimsControl" (negated.emission.package noAssociation) (packageOf both) root.id relations)
  let (ok, output) ← IO.ofExcept proof.get
  acceptedOutput "Claims" ok output theorems
  let (ok, output) ← IO.ofExcept comparison.get
  acceptedOutput "ClaimsSource" ok output []
  let (ok, output) ← IO.ofExcept control.get
  if ok then throw (IO.userError "Lean accepted another verifier as the deployed package of the claims")
  let unproved := theorems.filter fun theorem_ =>
    ((axiomsOf s!"ClaimsControl.{theorem_}" output).getD ["sorryAx"]).contains "sorryAx"
  unless unproved.contains "deployed_first" && !unproved.contains "members" do
    throw (IO.userError s!"the control: unproved are {unproved}\n{output}")
  IO.println ("The claims of the two goals of Count<8> are one package: the deployed definitions " ++
    "first and unchanged, then the relation at each goal's value; the kernel finds the root's " ++
    "processes to be the deployed ones; 1 of 1 control refused.")

end GoalClaimCheck

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    GoalClaimCheck.run "../../language/conformance/layer-b.txt" work
