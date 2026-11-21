module

public import Zkc.Frontend.Written.Claim
public import Zkc.Frontend.Written.Charge
public import Zkc.Frontend.Written.Package

@[expose] public section

/-!
The statements of written soundness goals, as the text of a module.

A module about what goals claim holds the printed package of the claims (`goalClaims`). This
file writes what stands around a proof in such a module, from what the frontend read, from the
library and from the model that the check names:

- `facts`: the keys, headers and places of the root, of the functions before it that the text
  names and of each goal's relation, the verifier and the prover of the scheme, and each goal's
  proof arguments and charge, as terms;
- `coverage`: the theorem `covered`, that the model of the statement covers the stored program;
- `entries`: where the walks of the module start: for the deciding role, each named function
  and each goal's relation, the meaning in the installed program as the sealed denotation of
  the body;
- `transfers`: that what holds of the root and of a relation in the installed program holds of
  them in every program that admission gives, each found by its key;
- `claimTexts`: for each goal, the propositions that are stated before any proof. The claim
  about a program (`<goal>ClaimOf`, and `<goal>Claim` about the installed one): on valid inputs
  of the deciding role, where the relation of the goal's clause returns false at its operands
  (for every valid witness, when the relation has witness parameters), the simulation of the
  deciding role returns with probability at most the total of the goal's charge, against every
  service that is no more likely to answer a coin within a set of replies than the sampler of
  the coin's law is to draw one there (it may also not answer) and that answers only what is
  permitted. The goal for every admitted program (`<goal>Goal`), the result with the coverage
  (`<goal>Result`), and that the hypotheses of the claim are met together (`<goal>Witnessed`);
- `closings`: for each goal, the theorems `<goal>_sound : <goal>Goal`,
  `<goal>_result : <goal>Result` and `<goal>_met : <goal>Witnessed`, from the theorems
  `<goal>_installed : <goal>Claim` and `<goal>_witnessed : <goal>Witnessed` that the text
  between has to prove;
- `ceilings`: for each goal that states a ceiling, the theorem `<goal>_ceiling` that the total
  of its charge is within it. A goal whose ceiling is below that total is refused here (GL4),
  before any module is written.

So a proof module is: the package, `opens`, `facts`, `coverage`, `entries`, `transfers`,
`claimTexts`, the proofs written for the protocol, `closings`. Every statement that the module
publishes is a proposition defined before the text of the proofs; a name that the text defines
afterwards cannot change what it says. The subject, the premise, the experiment, the samplers
and the bound are written here.

What a statement says of its goal is read from the claims (`goalClaims`) and from nothing that
a caller gives beside them: the deciding role is the verifier of the claims' scheme, the
operands are the inputs of the deployed header at the places that the claims give, and the
proof arguments and the ceiling are the goal's. A caller gives the model, the labels of the
functions that the text names, and, until the budget of a goal is the table of its root, the
charge of one draw. A goal whose clause is a `reduces` gets no statement: the statement of a
reduction is about a return on which the reduced statement is true, and a bound on every return
is another claim.

The model is named by a `ModelText`: the binders of what it is built from, the model, its
samplers and its coverage as terms over them, and what the statement assumes of it. It is
chosen by the check that writes the module and is part of the claim, not of the proof. The
statement is for one charge on a draw of the root; a root with charges at several sites or
under applications waits for the table of caps by site.
-/

namespace Zkc.Frontend.Written
open Core

/-- How the module of a statement names the model that the statement is about. -/
structure ModelText where
  /-- The binders of what the model is built from. -/
  binders : String
  /-- The same, as the bound variables of an existential statement, an instance as an anonymous
  variable: what a witness of the statement's hypotheses gives. -/
  existential : String
  /-- What a use of a statement passes for the binders that are explicit. -/
  arguments : String
  /-- The model, as a term over the binders. -/
  model : String
  /-- The samplers of the laws of the model, as a term over the binders. -/
  samplers : String
  /-- Whether the model covers a stored program: the function that says that it interprets the
  rows that the program links and has a sampler for the laws that it draws. -/
  covers : String
  /-- What the statement assumes of what the model is built from: the name of each hypothesis
  and its proposition over the binders. A hypothesis is part of the claim; the proof gets it
  after the path. -/
  hypotheses : List (String × String) := []

/-- The standard model built from an algebra, with the samplers of its laws. -/
def standardModelText : ModelText where
  binders := "{F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]"
  existential := "(F G : Type) (D : StandardModel.Data F G) (_ : DecidableEq F) (_ : DecidableEq G)"
  arguments := "D"
  model := "(StandardModel.model D)"
  samplers := "(lawSamplers (StandardModel.model D) (StandardModel.draws D))"
  covers := "StandardModel.covers"

/-- The arithmetic model over a field that can be sampled, with the samplers of its laws: a
scalar and a sequence of scalars are drawn uniformly. -/
def arithmeticModelText : ModelText where
  binders := "{F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] " ++
    "[AddCommGroup G] [Module F G] [DecidableEq G]"
  existential := "(F G : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) " ++
    "(_ : SampleableType F) (_ : AddCommGroup G) (_ : Module F G) (_ : DecidableEq G)"
  arguments := ""
  model := "(ArithmeticModel.model F G)"
  samplers := "(lawSamplers (ArithmeticModel.model F G) (ArithmeticModel.draws F G))"
  covers := "ArithmeticModel.covers"

/-- The arithmetic model over a field with at least as many elements as the scalar field of the
source. A charge that the source writes with the order of its scalar field then bounds what a
uniform scalar of the model pays for; the scalar field itself is such a field. -/
def scalarFieldModelText : ModelText :=
  { arithmeticModelText with
    hypotheses := [("large", "Zkc.Vocabulary.Field.bls12381Fr.order ≤ Fintype.card F")] }

/-- The hypotheses of a model as the antecedents of a proposition. -/
def ModelText.assumed (model : ModelText) : String :=
  String.join (model.hypotheses.map fun (_, proposition) => s!"    {proposition} →\n")

/-- The hypotheses of a model as the binders of a theorem. -/
def ModelText.assumedBinders (model : ModelText) : String :=
  String.join (model.hypotheses.map fun (name, proposition) => s!"    ({name} : {proposition})\n")

/-- The hypotheses of a model as the conjuncts of a statement. -/
def ModelText.assumedConjuncts (model : ModelText) : String :=
  String.join (model.hypotheses.map fun (_, proposition) => s!"    {proposition} ∧\n")

/-- The names of the hypotheses of a model, as arguments. -/
def ModelText.assumedNames (model : ModelText) : String :=
  " ".intercalate (model.hypotheses.map (·.1))

/-- A goal of the claims with its charge on a draw of the root. -/
structure StatedGoal where
  claimed : ClaimedGoal
  charge : DrawCharge

/-- The claims of goals of one scheme, with what their statements need. The deciding role is
the verifier of the claims' scheme; the text names it `verifierRole` and the prover
`proverRole`. -/
structure Statements where
  claims : GoalClaims
  goals : List StatedGoal
  /-- The functions of the package before the root that the text names, each with the label of
  its name (`apply` gives `applyMember`): what the root may call. -/
  functions : List (String × Nat) := []

/-- A charge as a term. -/
def chargeTerm (charge : DrawCharge) : String :=
  let draw (blocks : List (Key × Nat)) (key : Key) :=
    let around := ", ".intercalate (blocks.map fun (block, number) => s!"(⟨{block.number}⟩, {number})")
    s!"([{around}], ⟨{key.number}⟩)"
  let draws := ", ".intercalate (charge.draws.map fun (blocks, key) => draw blocks key)
  s!"⟨⟨{charge.owner.number}⟩, {charge.numerator}, {charge.denominator}, [{draws}]⟩"

/-- The member of a list of headers that is `depth` places after its head. -/
def memberAt : Nat → String
  | 0 => "Member.head"
  | depth + 1 => s!"(Member.tail {memberAt depth})"

namespace Statements

/-- The package of the claims. -/
def package (s : Statements) : SourcePackage := s.claims.emission.package ⟨[], [], [], [], []⟩

/-- The keys of the definitions of the package in order, and whether each is a protocol. -/
def definitions (s : Statements) : List (Nat × Bool) :=
  (Written.package s.package).definitions.map fun (key, isProtocol) => (key.number, isProtocol)

/-- The name, in the package, of the program before the definition with a key. -/
def programBefore (s : Statements) (key : Nat) : String :=
  match (s.definitions.takeWhile (·.1 != key)).getLast? with
  | some (before, _) => s!"program{before}"
  | none => s!"program{baseSuffix}"

/-- The place of a definition among those of its kind in the installed program, which stand
last first: as many places after the head as definitions of its kind follow it. -/
def memberOf (s : Statements) (key : Nat) (isProtocol : Bool) : String :=
  memberAt (((s.definitions.dropWhile (·.1 != key)).drop 1).filter (·.2 == isProtocol)).length

/-- The functions of the package of claims that stand before the root, each under the name of
its declaration in the source: what the root may call. A name that two of them share, or that a
goal has, is followed by the key. -/
def _root_.Zkc.Frontend.Written.GoalClaims.functionsBeforeRoot (claims : GoalClaims) :
    List (String × Nat) :=
  let definitions := (Written.package (claims.emission.package ⟨[], [], [], [], []⟩)).definitions
  let before := (definitions.takeWhile (·.1.number != claims.root)).filter (!·.2)
  let named : List (String × Nat) := before.map fun (key, _) =>
    let name := match claims.state.table.entries[key.number]? with
      | some entry => claims.state.program.nameOf entry.key.declaration
      | none => ""
    (if name.isEmpty then "function" else name, key.number)
  let taken := claims.goals.map (·.goal) ++ ["root", "callee", "verifier", "prover"]
  named.map fun (name, key) =>
    if taken.contains name || (named.filter (·.1 == name)).length > 1 then (s!"{name}{key}", key)
    else (name, key)

/-- The place of a function among the functions of the program before the root, which stand
last first. -/
def calleeMember (s : Statements) (key : Nat) : String :=
  let before := s.definitions.takeWhile (·.1 != s.claims.root)
  memberAt (((before.dropWhile (·.1 != key)).drop 1).filter (!·.2)).length

/-- The ports of the root, each with its type as a term and whether the deciding role holds
it. -/
def ports (s : Statements) : Except String (List (String × Bool)) := do
  let deciding := s.claims.verifier
  let some root := s.package.named.definitions.find? (·.key.number == s.claims.root)
    | throw "the package of the claims does not have the root"
  let .protocol _ _ ins _ _ := root | throw "the root of the claims is no protocol"
  return ins.map fun port => (ty (b := s.package.bindings) port.ty, port.holders.contains deciding)

/-- The types of the parameters of a goal's relation, as terms. -/
def relationInputs (s : Statements) (goal : StatedGoal) : Except String (List String) := do
  let some relation := s.package.named.definitions.find? (·.key.number == goal.claimed.relation)
    | throw s!"the package of the claims does not have the relation of {goal.claimed.goal}"
  let .fn _ ins _ _ _ _ _ _ := relation | throw s!"the relation of {goal.claimed.goal} is no function"
  return ins.map (ty (b := s.package.bindings))

/-- The names that the text after this one may use. -/
def opens : String :=
  "open Zkc.Formal Zkc.Formal.ProbabilisticProcess Zkc.Formal.Written OracleComp ProbComp\n" ++
  "open Zkc.Frontend.Written (DrawCharge)\n" ++
  "open scoped NNRat ENNReal\n"

/-- What was read from the source, as terms: the root, the roles, the functions before the root
that the text names, and for each goal its proof arguments, its charge and its relation. -/
def facts (s : Statements) : String :=
  let root := s.claims.root
  s!"abbrev rootKey : Key := ⟨{root}⟩\n" ++
  s!"noncomputable abbrev rootHeader := header{root}\n" ++
  s!"noncomputable abbrev rootNames := names{root}\n" ++
  s!"noncomputable abbrev rootBody := body{root}\n" ++
  s!"noncomputable abbrev calleeProgram : Typed V := {s.programBefore root}\n" ++
  s!"noncomputable abbrev rootMember : Member installed.headers.protocols header{root} :=\n" ++
  s!"  {s.memberOf root true}\n" ++
  s!"abbrev verifierRole : Role := {s.claims.verifier}\n" ++
  s!"abbrev proverRole : Role := {s.claims.prover}\n" ++
  String.join (s.functions.map fun (label, key) =>
    s!"abbrev {label}Key : Key := ⟨{key}⟩\n" ++
    s!"noncomputable abbrev {label}Header := header{key}\n" ++
    s!"noncomputable abbrev {label}Names := names{key}\n" ++
    s!"noncomputable abbrev {label}Body := body{key}\n" ++
    s!"noncomputable abbrev {label}Before : Typed V := {s.programBefore key}\n" ++
    s!"noncomputable abbrev {label}Member : Member calleeProgram.headers.fns header{key} :=\n" ++
    s!"  {s.calleeMember key}\n") ++
  String.join (s.goals.map fun goal =>
    let name := goal.claimed.goal
    let relation := goal.claimed.relation
    s!"def {name}Charge : Zkc.Frontend.Written.DrawCharge := {chargeTerm goal.charge}\n" ++
    String.join (goal.claimed.specification.toList.zipIdx.map fun (value, index) =>
      s!"def {name}Argument{index} : Nat := {value}\n") ++
    s!"abbrev {name}Key : Key := ⟨{relation}⟩\n" ++
    s!"noncomputable abbrev {name}Header := header{relation}\n" ++
    s!"noncomputable abbrev {name}Names := names{relation}\n" ++
    s!"noncomputable abbrev {name}Body := body{relation}\n" ++
    s!"noncomputable abbrev {name}Before : Typed V := {s.programBefore relation}\n" ++
    s!"noncomputable abbrev {name}Member : Member installed.headers.fns header{relation} :=\n" ++
    s!"  {s.memberOf relation false}\n")

/-- Where the walks of a module start. The meanings of a program are closed to Lean's own
reduction, and a walk reads a term in an environment; so for the deciding role of the root, for
each function before the root that the text names and for each goal's relation, the meaning in
the installed program is stated to be the sealed denotation of the body, which the kernel
checks. The program of the role is `<role>Program`, in the kernel's normal form; the equations
are `<role>_meaning`, `<function>_meaning` and `<goal>_meaning`, for every model. A walk
starts by rewriting with one of them. -/
def entries (s : Statements) : String :=
  let function (label member program : String) :=
    s!"/-- The function of `{label}` in its program is the denotation of its body. -/\n" ++
    s!"theorem {label}_meaning (M : Model V) (inputs : HList M.Val {label}Header.ins) :\n" ++
    s!"    fnMeaning M {program} {member} inputs =\n" ++
    s!"      ({label}Body.denote (localSem M {label}Before.headers.fns (Defs.fnTable M {label}Before.defs)) []\n" ++
    s!"        (Env.empty.extend {label}Names inputs)).sealed := by\n  kernel_rfl\n\n"
  let label := "verifier"
  let role :=
      s!"-- The program of the {label}, in the kernel's normal form.\n" ++
      s!"kernel_normal {label}Program :\n" ++
      s!"    Term (roleDialect V calleeProgram.headers {label}Role) (Ctx.empty.extend rootNames) rootHeader.outs :=\n" ++
      s!"  project {label}Role rootBody\n\n" ++
      s!"/-- The process of the {label} in a run of the installed program is the denotation of its\n" ++
      "program. -/\n" ++
      s!"theorem {label}_meaning (M : Model V) (path : List Frame)\n" ++
      s!"    (inputs : HList (RV M {label}Role) rootHeader.ins) :\n" ++
      s!"    roleMeaning M installed rootMember {label}Role path inputs =\n" ++
      s!"      ({label}Program.denote (roleSem M {label}Role (Defs.fnTable M calleeProgram.defs)\n" ++
      s!"        (Defs.rTable M calleeProgram.defs)) path (Env.empty.extend rootNames inputs)).sealed := by\n" ++
      "  kernel_rfl\n\n"
  "noncomputable section\n\n" ++ role ++
  String.join (s.functions.map fun (label, _) => function label s!"{label}Member" "calleeProgram") ++
  String.join (s.goals.map fun goal =>
    function goal.claimed.goal s!"{goal.claimed.goal}Member" "installed") ++
  "end\n\n"

/-- The names of the theorems that `entries` writes. -/
def entryNames (s : Statements) : List String :=
  ["verifierProgram.eq", "verifier_meaning"] ++
  s.functions.map (s!"{·.1}_meaning") ++ s.goals.map (s!"{·.claimed.goal}_meaning")

/-- That what holds of the root, and of the root with a goal's relation, in the installed
program holds of them in every admitted program, each found by its key. -/
def transfers (s : Statements) : String :=
  let found (admitted : String) :=
    "    ∃ root : Member a.program.headers.protocols rootHeader,\n" ++
    "      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧ " ++ admitted
  "/-- What holds of the root of the installed program holds of the root of every admitted\n" ++
  "program. -/\n" ++
  "theorem at_root {a : Admitted V} (admitted : admit stored association = .ok a)\n" ++
  "    (P : (p : Typed V) → Member p.headers.protocols rootHeader → Prop)\n" ++
  "    (holds : P installed rootMember) :\n" ++
  found "P a.program root := by\n" ++
  "  have same := readback admitted\n  generalize a.program = p at same\n  subst same\n" ++
  "  exact ⟨rootMember, by kernel_rfl, holds⟩\n\n" ++
  String.join (s.goals.map fun goal =>
    let name := goal.claimed.goal
    s!"/-- What holds of the root and of the relation of `{name}` in the installed program holds of\n" ++
    "them in every admitted program, each found by its key. -/\n" ++
    s!"theorem at_{name} " ++ "{a : Admitted V} (admitted : admit stored association = .ok a)\n" ++
    s!"    (P : (p : Typed V) → Member p.headers.protocols rootHeader → Member p.headers.fns {name}Header → Prop)\n" ++
    s!"    (holds : P installed rootMember {name}Member) :\n" ++
    found "\n" ++
    s!"      ∃ relation : Member a.program.headers.fns {name}Header,\n" ++
    s!"        a.program.find {name}Key = some (.fn relation) ∧ P a.program root relation := by\n" ++
    "  have same := readback admitted\n  generalize a.program = p at same\n  subst same\n" ++
    s!"  exact ⟨rootMember, by kernel_rfl, {name}Member, by kernel_rfl, holds⟩\n\n")

/-- What a statement of a goal is made of, as text over a model: the binders of the deciding
role's inputs with their validity, the inputs, the premise about the relation for a program and
a member, and the names bound. -/
structure Parts where
  /-- As the binders of a theorem. -/
  binders : String
  /-- As the quantifiers of a proposition: each value, then its validity as a hypothesis. -/
  quantified : String
  /-- As the bound variables of an existential statement: each value, then its validity as a
  conjunct. -/
  existential : String
  names : String
  inputs : String
  premise : String → String → String

/-- The names of the inputs of the root in a statement: the name that the source gives the port,
after `input_`, so that a reader of a statement sees which inputs the relation is applied to and
which the deciding role is run on. An input whose name in the source is no plain identifier, or
is the name of another input, is named by its place. -/
def inputNames (s : Statements) : List String :=
  let plain (name : String) := !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') &&
    !(name.front.isDigit)
  let names := s.claims.inputs.toList
  names.zipIdx.map fun (name, index) =>
    if plain name && (names.filter (· == name)).length == 1 then s!"input_{name}" else s!"port{index}"

def parts (s : Statements) (model : ModelText) (goal : StatedGoal) : Except String Parts := do
  -- a goal of these statements is one of their claims, and not the claim of another package
  unless s.claims.goals.any (fun own => own.goal == goal.claimed.goal &&
      own.relation == goal.claimed.relation && own.statement == goal.claimed.statement &&
      own.witness == goal.claimed.witness && own.specification == goal.claimed.specification &&
      own.ceiling == goal.claimed.ceiling) do
    throw s!"{goal.claimed.goal}: the goal is not one of the claims that these statements are of"
  unless goal.claimed.clause.kind == .proves do
    throw (s!"{goal.claimed.goal}: the goal reads a `reduces` clause. The statement of a reduction " ++
      "is about a return on which the reduced statement is true, and is not issued yet")
  let ports ← s.ports
  let named := s.inputNames
  unless named.length == ports.length do
    throw s!"{goal.claimed.goal}: the inputs of the deployed header are not those that the claims name"
  let name (index : Nat) := named.getD index s!"port{index}"
  let held := ports.zipIdx.filter (·.1.2)
  let binders := String.join (held.map fun ((type, _), index) =>
    s!"    ({name index} : {model.model}.Val {type}) (valid_{name index} : {model.model}.Valid {type} {name index})\n")
  let quantified := String.join (held.map fun ((type, _), index) =>
    s!"    ∀ ({name index} : {model.model}.Val {type}), {model.model}.Valid {type} {name index} →\n")
  let existential := String.join (held.map fun ((type, _), index) =>
    s!"    ∃ ({name index} : {model.model}.Val {type}), {model.model}.Valid {type} {name index} ∧\n")
  let names := " ".intercalate (held.map fun (_, index) => s!"{name index} valid_{name index}")
  let cons (items : List String) := items.foldr (fun item rest => s!"(.cons {item} {rest})") ".nil"
  let inputs := cons (ports.zipIdx.map fun ((_, holds), index) => if holds then name index else "()")
  for position in goal.claimed.statement do
    unless (ports[position]?.map (·.2)) == some true do
      throw s!"{goal.claimed.goal}: the deciding role does not hold the input at {position} of the deployed header"
  let statement := goal.claimed.statement.toList.map name
  let types ← s.relationInputs goal
  let witnessTypes := types.drop statement.length
  let premise (program relation : String) : String :=
    let returns (operands : String) :=
      s!"functionResult (t := .bool) (fnMeaning {model.model} {program} {relation} {operands}) = some false"
    if witnessTypes.isEmpty then returns (cons statement)
    else
      let witnesses := witnessTypes.zipIdx.map fun (_, index) => s!"witness{index}"
      let bound := " ".intercalate (witnessTypes.zipIdx.map fun (type, index) =>
        s!"(witness{index} : {model.model}.Val {type})")
      let valid := String.join (witnessTypes.zipIdx.map fun (type, index) =>
        s!"{model.model}.Valid {type} witness{index} → ")
      s!"(∀ {bound}, {valid}{returns (cons (statement ++ witnesses))})"
  return { binders, quantified, existential, names, inputs, premise }

/-- The total of a goal's charge: the charge at each of its draws. -/
def _root_.Zkc.Frontend.Written.StatedGoal.total (goal : StatedGoal) : Rat :=
  goal.charge.draws.length * ((goal.charge.numerator : Rat) / goal.charge.denominator)

/-- The ceilings of the goals (GL4): a goal that states a ceiling is issued a statement only when
the total of its charge is within it. A source whose charges add up to more than its goal
promises gets no statement, and is told the two numbers. -/
def checkCeilings (s : Statements) : Except String Unit := do
  for goal in s.goals do
    let some ceiling := goal.claimed.ceiling | continue
    unless goal.total ≤ ceiling do
      throw (s!"GL4: the goal `{goal.claimed.goal}` states the ceiling {ceiling}, and the total of its " ++
        s!"charge is {goal.total}")

/-- For each goal with a ceiling, the theorem `<goal>_ceiling`: the total of the goal's charge
is within the ceiling, the comparison decided by the kernel. -/
def ceilings (s : Statements) : Except String String := do
  s.checkCeilings
  let mut text := ""
  for goal in s.goals do
    let some ceiling := goal.claimed.ceiling | continue
    let name := goal.claimed.goal
    text := text ++
      s!"/-- The total of the charge of `{name}` is within the ceiling that the goal states. -/\n" ++
      s!"theorem {name}_ceiling : total {name}Charge ≤ (({ceiling.num.toNat} : ℕ) : ℝ≥0∞) / ({ceiling.den} : ℕ) :=\n" ++
      s!"  total_le_div {name}Charge {ceiling.num.toNat} {ceiling.den} (by decide) (by decide) (by decide)\n\n"
  return text

/-- The probability that the simulation of the deciding role of a program returns, as text. -/
def returns (model : ModelText) (program root inputs : String) : String :=
  s!"Pr\{let out ← (simulateQ (handlerOf service) (embed\n" ++
  s!"          (roleMeaning {model.model} {program} {root} verifierRole path {inputs}))).run.run s}[\n" ++
  "        ∃ results, out.1 = some (.inl results)]"

/-- The same service as the quantifiers of a proposition. -/
def serviceQuantified (model : ModelText) : String :=
  s!"    ∀ \{σ : Type} (service : Service (RSig {model.model}) σ), service.Follows {model.samplers} →\n" ++
  s!"    (∀ op s reply t, (some reply, t) ∈ support (service op s) → Permitted {model.model} op reply) →\n" ++
  s!"    ∀ (s : σ),\n"

/-- The binders of a service that draws by the samplers of the model and answers what is
permitted, with a state. -/
def serviceBinders (model : ModelText) : String :=
  s!"    \{σ : Type} (service : Service (RSig {model.model}) σ)\n" ++
  s!"    (follows : service.Follows {model.samplers})\n" ++
  s!"    (permitted : ∀ op s reply t, (some reply, t) ∈ support (service op s) →\n" ++
  s!"      Permitted {model.model} op reply) (s : σ)"

/-- The theorem `covered`: the model covers the stored program of the package, decided by the
kernel. A statement over a model is issued with it, so that the statement is about this program
and not about one in which a row is a constant or a coin has no distribution. -/
def coverage (model : ModelText) : String :=
  "/-- **The model covers the package.** It interprets every row of the vocabulary that the\n" ++
  "package links and has a sampler for the law of every coin that the package draws. -/\n" ++
  s!"theorem covered : {model.covers} stored = true := by decide +kernel\n\n"

/-- What a goal claims of a program with its root and the relation of the goal's clause, as the
text of a proposition: on valid inputs of the deciding role on which the relation returns false,
the simulation of that role returns with probability at most the total of the goal's charge,
against every service that is no more likely to answer a coin within a set of replies than the
sampler of the coin's law is to draw one there, and that answers only what is permitted. -/
def claimAt (s : Statements) (model : ModelText) (goal : StatedGoal)
    (program root relation : String) : Except String String := do
  let parts ← s.parts model goal
  return s!"∀ {model.binders} (path : List Frame),\n" ++
    model.assumed ++ parts.quantified ++ serviceQuantified model ++
    s!"    {parts.premise program relation} →\n" ++
    s!"      {returns model program root parts.inputs} ≤ total {goal.claimed.goal}Charge"

/-- For each goal, what is stated before any proof is written, so that no name defined by the
text of a proof can change it:

- `<goal>ClaimOf p root relation`, the claim about a program with its root and the relation of
  the goal's clause, and `<goal>Claim`, the claim about the installed program, which the text
  proves;
- `<goal>Goal`: in every program that admission gives for the package, the root and the
  relation are found by their keys and the claim holds of them;
- `<goal>Result`: the model covers the package, and the goal holds;
- `<goal>Witnessed`: the hypotheses of the claim are met together by some model, valid inputs
  and a service with a state, with the relation returning false there. The text proves it, so
  that the claim is not about nothing. -/
def claimTexts (s : Statements) (model : ModelText) : Except String String := do
  let mut text := ""
  for goal in s.goals do
    let name := goal.claimed.goal
    let parts ← s.parts model goal
    text := text ++
      s!"/-- What the goal `{name}` claims of a program with its root and the relation of the goal's\n" ++
      "clause: on valid inputs of the deciding role on which the relation returns false, the\n" ++
      "simulation of that role returns with probability at most the total of the goal's charge,\n" ++
      "against every service that is no more likely to answer a coin within a set of replies than\n" ++
      "the sampler of the coin's law is to draw one there, and that answers only what is permitted. -/\n" ++
      s!"def {name}ClaimOf (p : Typed V) (root : Member p.headers.protocols rootHeader)\n" ++
      s!"    (relation : Member p.headers.fns {name}Header) : Prop :=\n  " ++
      (← s.claimAt model goal "p" "root" "relation") ++ "\n\n" ++
      s!"/-- The claim of the goal `{name}` about the installed program. -/\n" ++
      s!"def {name}Claim : Prop := {name}ClaimOf installed rootMember {name}Member\n\n" ++
      s!"/-- **The goal `{name}`.** In every program that admission gives for the package, the protocol\n" ++
      "and the relation of the goal's clause are found by their keys, and the claim holds of them. -/\n" ++
      s!"def {name}Goal : Prop :=\n" ++
      "  ∀ {a : Admitted V}, admit stored association = .ok a →\n" ++
      "    ∃ root : Member a.program.headers.protocols rootHeader,\n" ++
      "      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧\n" ++
      s!"      ∃ relation : Member a.program.headers.fns {name}Header,\n" ++
      s!"        a.program.find {name}Key = some (.fn relation) ∧ {name}ClaimOf a.program root relation\n\n" ++
      s!"/-- **The result of the goal `{name}`**: the model covers the package, and the goal holds. A\n" ++
      "result over a model is about the program only where the model covers it. -/\n" ++
      s!"def {name}Result : Prop := {model.covers} stored = true ∧ {name}Goal\n\n" ++
      s!"/-- The hypotheses of the claim of `{name}` are met together: some model with what the claim\n" ++
      "assumes of it, valid inputs on which the relation returns false, and a service with a state\n" ++
      "that draws within the samplers and answers only what is permitted. -/\n" ++
      s!"def {name}Witnessed : Prop :=\n  ∃ {model.existential},\n" ++
      model.assumedConjuncts ++ parts.existential ++
      s!"    ∃ (σ : Type) (service : Service (RSig {model.model}) σ), Nonempty σ ∧\n" ++
      s!"      service.Follows {model.samplers} ∧\n" ++
      s!"      (∀ op s reply t, (some reply, t) ∈ support (service op s) → Permitted {model.model} op reply) ∧\n" ++
      s!"      {parts.premise "installed" s!"{name}Member"}\n\n"
  return text

/-- For each goal, after the text of the proofs: the theorems `<goal>_sound : <goal>Goal`,
`<goal>_result : <goal>Result` and `<goal>_met : <goal>Witnessed`, from the theorems
`<goal>_installed : <goal>Claim` and `<goal>_witnessed : <goal>Witnessed` that the text has to
prove. The statements were fixed before the text; only their proofs are written here. -/
def closings (s : Statements) : String :=
  String.join (s.goals.map fun goal =>
    let name := goal.claimed.goal
    s!"/-- The goal `{name}`, for every admitted program. -/\n" ++
    s!"theorem {name}_sound : {name}Goal :=\n" ++
    s!"  fun admitted => at_{name} admitted {name}ClaimOf ({name}_installed : {name}Claim)\n\n" ++
    s!"/-- The result of the goal `{name}`. -/\n" ++
    s!"theorem {name}_result : {name}Result := ⟨covered, {name}_sound⟩\n\n" ++
    s!"/-- The hypotheses of the claim of `{name}` are met. -/\n" ++
    s!"theorem {name}_met : {name}Witnessed := {name}_witnessed\n\n")

/-- The names of the theorems that `closings` writes. -/
def closingNames (s : Statements) : List String :=
  s.goals.flatMap fun goal =>
    [s!"{goal.claimed.goal}_sound", s!"{goal.claimed.goal}_result", s!"{goal.claimed.goal}_met"]

end Statements

end Zkc.Frontend.Written
