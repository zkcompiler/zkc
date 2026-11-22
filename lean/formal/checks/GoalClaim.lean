import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
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
- the count of the relation, whose index is read as a position, is one loop, and a sum whose
  index is an operand of arithmetic is its terms in sequence (TY8);
- a function that the verifier and the relation both call is one definition;
- a relation that the relation applies comes before it;
- the ports at the statement and at the witness, for a clause written short and one that gives
  the witness; an operand that is no port is refused;
- the claim of a goal types the one clause that the goal reads;
- a relation applied in a relation, typed without a goal at default values, changes no key and
  no stored definition of the deployed protocol;
- the contract of a protocol generic over a module parameter is typed in both typings, and its
  claim is read with the resolutions that the instance keeps.

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

A fourth module has the claims of a goal whose relation has a witness, with the statements that
`Written.Statements` writes for it and no proof: its premise quantifies the witness, and Lean
elaborates it.
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

def imports (others : List String) : String := Statements.header (Written.packageImports ++ others)

/-- The theorems of the proof module, whose axioms the check reads. -/
def theorems : List String :=
  ["deployed_first", "same_header", "prover_same", "verifier_same", "members"]

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
  -- The count of the relation reads its index as a position, so it is one loop (TY8), with
  -- no block for each entry; a sum whose index is an operand of arithmetic stays its terms in
  -- sequence.
  let relationText (claims : GoalClaims) (claimed : ClaimedGoal) : String :=
    (((storedTexts (packageOf claims)).find? (·.1 == claimed.relation)).map (·.2)).getD ""
  let counted (text needle : String) : Nat := (text.splitOn needle).length - 1
  expect "the count of NearZero is not one loop"
    (counted (relationText both loose) ".loop " == 1 && counted (relationText both loose) ".block " == 0)
  let weighted ← edit count "if xs[i] == 0 then 0 else 1" "if xs[i] == 0 then 0 else i + 1"
  let (_, weightedClaims) ← read weighted ["loose"]
  let weightedRelation ← only weightedClaims
  expect "a sum whose index is an operand of arithmetic is not its eight terms in sequence"
    (counted (relationText weightedClaims weightedRelation) ".block " == 8)
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

  -- The claim of a goal types the clause that the goal reads and no other.
  let pairRoot ← IO.ofExcept (goalRoot pair "sound")
  for place in [0, 1] do
    let (typed, _) ← IO.ofExcept
      (evaluate pairRoot.state default (Typing.typedClauses pairRoot.id #[] (only := some place)))
    expect s!"the typing of the clause at {place} types {typed.map (·.1)}" (typed.map (·.1) == #[place])

  -- A specification item is typed without a goal at default values of its specification-only
  -- parameters, and a relation that it applies is then reached at those values. That changes
  -- no key and no stored definition of what is deployed.
  let applied ← fixture "N-GL2g"
  let plain ← edit applied "relation ZeroAt(xs: [F; n]): Reads(xs)" "relation ZeroAt(xs: [F; n]): xs[e] == 0"
  let appliedRoot ← IO.ofExcept (goalRoot applied "placed")
  let plainRoot ← IO.ofExcept (goalRoot plain "placed")
  expect "a relation applied in a relation changed the key or the stored text of the deployed protocol"
    (appliedRoot.id == plainRoot.id &&
      storedTexts (appliedRoot.emission.package noAssociation) ==
        storedTexts (plainRoot.emission.package noAssociation))

  -- A contract of a protocol generic over a module parameter is typed in both typings, and the
  -- goal reads the resolutions that the instance keeps: a relation over the type member, applied
  -- to a port of that type, is a definition of the claims' package after the module's member.
  let generic := "module client\nuse zkc::security::{soundness}\n" ++
    "pub struct Box:\n    pub n: nat\n" ++
    "interface Carrier:\n    type T\n    def digit(a: T) -> nat\n" ++
    "module First: Carrier:\n    type T = Box\n    def digit(a): a.n\n" ++
    "relation Holds<Y: Carrier>(a: Y::T): a.digit() == 9\n" ++
    "pub protocol Show<X: Carrier> roles(P, V)(x: X::T @(P, V)):\n" ++
    "    r <- draw index<8> from V to P\n    guard @V x.digit() == 9\n" ++
    "spec for Show:\n    proves @V Holds<X>(x)\n" ++
    "scheme S = Show<First>:\n    prover P\n    construction interactive\n" ++
    "goal sound = soundness(S)\n"
  let (genericRoot, genericClaims) ← read generic ["sound"]
  let held ← only genericClaims
  expect "the claim of a generic protocol"
    (held.statement == #[0] &&
      (storedTexts (packageOf genericClaims)).length ==
        (storedTexts (genericRoot.emission.package noAssociation)).length + 1)

  -- An operand that is no port.
  let computed ← edit count "proves @V NearZero(xs)" "proves @V NearZero(xs ++ [])"
  match (goalRoot computed "loose").bind (goalClaims · ["loose"]) with
  | .ok _ => throw (IO.userError "an operand that is no port was read as a port")
  | .error why => expect s!"an operand that is no port: {why}" (why.contains "WK-CLAUSE")

  -- Lean: the claims' package against the deployed package.
  let deployed := root.emission.package noAssociation
  let relations := [loose.relation, strict.relation]
  let negated ← IO.ofExcept (goalRoot (← edit count "guard @V xs[z] == 0" "guard @V xs[z] != 0") "loose")
  let proof ← startLakeLean work "Claims" (proofModule "Claims" deployed (packageOf both) root.id relations)
  let comparison ← startLakeLean work "ClaimsSource"
    (comparisonModule "ClaimsSource" count ["loose", "strict"] (Written.package (packageOf both)).text)
  let control ← startLakeLean work "ClaimsControl"
    (proofModule "ClaimsControl" (negated.emission.package noAssociation) (packageOf both) root.id relations)
  -- The statement of a goal whose relation has a witness: the premise is that the relation
  -- returns false at the statement for every valid witness. The promise pair has no charge, so
  -- the bound of its statement is zero; Lean elaborates the statement.
  let (_, pairClaims) ← read pair ["sound"]
  let pairStated : Statements := { claims := pairClaims }
  let pairText ← IO.ofExcept (pairStated.claimTexts standardModelText)
  -- The premise stands in the claim and in the statement that its hypotheses are met.
  expect "the statement of a relation with a witness does not quantify the witness"
    ((pairText.splitOn "∀ (witness0 : ").length == 3)
  let stated ← startLakeLean work "ClaimsWitness"
    (← IO.ofExcept (pairStated.claimsModule "ClaimsWitness"))
  let (ok, output) ← IO.ofExcept proof.get
  acceptedOutput "Claims" ok output theorems
  let (ok, output) ← IO.ofExcept stated.get
  acceptedOutput "ClaimsWitness" ok output []
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
