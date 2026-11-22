module

public import Zkc.Frontend.Written.Claim
public import Zkc.Frontend.Written.Charge
public import Zkc.Frontend.Written.Package

@[expose] public section

/-!
The statements of written soundness goals, as the text of a module.

A module about what goals claim holds the printed package of the claims (`goalClaims`). This
file writes what stands around a proof in such a module, from what the frontend read and from
the library, about the class of models that it reads from the package (`chosenModel`):

- `facts`: the keys, headers and places of the root, of the functions before it that the text
  names and of each goal's relation, the verifier and the prover of the scheme, and each goal's
  proof arguments and table of caps, as terms;
- `counts`: for each goal, that the counts of its table are those of the stored program and
  that its budget is the number that the frontend computed, both decided by the kernel;
- `coverage`: the theorem `covered`, that the model of the statement covers the stored program;
- `sites`: the key of each named draw of the root under the name of its site in the source
  (`site_<name>`), and for each goal the cap that its table gives the draw
  (`<goal>_cap_<name>`), decided by the kernel;
- `entries`: where the walks of the module start: for the deciding role, each named function
  and each goal's relation, the meaning in the installed program as the sealed denotation of
  the body, each with the label at which a walk enters;
- `transfers`: that what holds of the root and of a relation in the installed program holds of
  them in every program that admission gives, each found by its key;
- `claimTexts`: for each goal, the propositions that are stated before any proof. The claim
  about a program (`<goal>ClaimOf`, and `<goal>Claim` about the installed one): on valid inputs
  of the deciding role, where the relation of the goal's clause returns false at its operands
  (for every valid witness, when the relation has witness parameters), the deciding role
  returns within the total of the goal's table of caps, in the experiment that the formal library
  defines (`ReturnsWithin`, `Zkc/Formal/ReturnExperiment.lean`): against every service that is
  no more likely to answer a coin within a set of replies than the sampler of the coin's law
  is to draw one there (it may also not answer) and that answers only what is permitted. The
  generator writes the process, the samplers and the bound, and not what the probability is of. The goal for every admitted program (`<goal>Goal`), the result with the coverage
  and the counts of the table (`<goal>Result`), and that the hypotheses of the claim are met together (`<goal>Witnessed`);
- `judgments`, for a text that establishes its claims by the judgment with fees
  (`Method.fees`): for each goal the proposition `<goal>Judged` that the text has to prove
  (`judgedAt`), the theorem `<goal>_claim_of_judged` that the claim follows from it, and the
  theorem `<goal>_witnessed_of` that the hypotheses of the claim are met at any valid inputs
  on which the relation returns false;
- `conclusions`, for such a text and after it: `<goal>_installed : <goal>Claim` from the
  theorem `<goal>_judged : <goal>Judged` of the text. A text of another method
  (`Method.direct`) proves `<goal>_installed` itself;
- `closings`: for each goal, the theorems `<goal>_sound : <goal>Goal`,
  `<goal>_result : <goal>Result` and `<goal>_met : <goal>Witnessed`, from the theorems
  `<goal>_installed : <goal>Claim` and `<goal>_witnessed : <goal>Witnessed`;
- `ceilings`: for each goal that states a ceiling, the theorem `<goal>_ceiling` that the total
  of its table of caps is within it, stated and proved before the text. A goal whose ceiling is
  below that total is refused here (GL4), before any module is written;
- `publications`: after everything else, the check that each theorem written after the text
  states exactly the proposition that was defined for it before the text.

So a proof module is: the package, `opens`, `facts`, `coverage`, `counts`, `sites`, `entries`,
`transfers`, `claimTexts`, `judgments`, `ceilings`, the proofs written for the protocol,
`conclusions`, `closings`, what a check adds, `publications`.
`Statements.module` assembles it, with its imports and with the names of the theorems whose
axioms it asks for; a caller gives the text of the proofs with what that text imports and the
names of its theorems, and what it adds after the closing theorems. Every
statement that the module publishes is a proposition defined before the text of the proofs; a
name that the text defines afterwards cannot change what it says. The subject, the premise, the experiment, the samplers
and the bound are written here.

What a statement says of its goal is read from the claims (`goalClaims`) and from nothing that
a caller gives beside them: the deciding role is the verifier of the claims' scheme, the
operands are the inputs of the deployed header at the places that the claims give, and the
proof arguments, the ceiling and the table of caps are the goal's. A caller gives the labels of
the functions that the text names. A goal whose clause is a `reduces` gets no
statement: the statement of a reduction is about a return on which the reduced statement is
true, and a bound on every return is another claim.

The model is named by a `ModelText`: the binders of what it is built from, the model, its
samplers and its coverage as terms over them, and what the statement assumes of it. It is part
of the claim, not of the proof, and no caller chooses it: `Statements.chosenModel` reads it
from the package (the laws of the coins that the stored program draws). The choice is not
trusted: every proof module states that its model covers the package (`covered`), and the
kernel decides that. A module of statements without proofs and the module of a ceiling state no
coverage. The
bound of a statement is the total of the goal's table of caps (`<goal>Caps.total`): every
charge that the root reaches at the goal's proof arguments, by use, read by `goalClaims`.
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
  /-- The modules of the model, of its samplers and of the instance at which a witness meets
  the hypotheses, beside those that every module of statements imports. -/
  imports : List String := []
  /-- What a witness gives for the bound variables of `existential`, as terms over the binders
  and separated by commas: an instance is found by Lean. -/
  witnesses : String
  /-- That the experiment of the model is not about nothing, as a term over the binders: a
  service of the laws with a state. -/
  served : String

/-- The standard model built from an algebra, with the samplers of its laws. -/
def standardModelText : ModelText where
  binders := "{F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]"
  existential := "(F G : Type) (D : StandardModel.Data F G) (_ : DecidableEq F) (_ : DecidableEq G)"
  arguments := "D"
  model := "(StandardModel.model D)"
  samplers := "(lawSamplers (StandardModel.model D) (StandardModel.draws D))"
  covers := "StandardModel.covers"
  imports := ["Zkc.Formal.Written.FiniteModel"]
  witnesses := "F, G, D, inferInstance, inferInstance"
  served := "(StandardModel.served D)"

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
  imports := ["Zkc.Formal.Written.ArithmeticDraws"]
  witnesses := "F, G, inferInstance, inferInstance, inferInstance, inferInstance, " ++
    "inferInstance, inferInstance, inferInstance"
  served := "(ArithmeticModel.served F G)"

/-- The arithmetic model over a field with at least as many elements as the scalar field of the
source. A charge that the source writes with the order of its scalar field then bounds what a
uniform scalar of the model pays for; the scalar field itself is such a field. -/
def scalarFieldModelText : ModelText :=
  { arithmeticModelText with
    hypotheses := [("large", "Zkc.Vocabulary.Field.bls12381Fr.order ≤ Fintype.card F")]
    imports := ["Zkc.Formal.Written.ArithmeticDraws", "Zkc.Formal.Written.ScalarField"] }

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

/-- The claims of goals of one scheme, with what their statements need beside them: the labels
of the functions that the text names. The deciding role is the verifier of the claims' scheme;
the text names it `verifierRole` and the prover `proverRole`. The goals of the statements are
those of the claims. -/
structure Statements where
  claims : GoalClaims
  /-- The functions of the package before the root that the text names, each with the label of
  its name (`apply` gives `applyMember`): what the root may call. -/
  functions : List (String × Nat) := []

/-- How the text of a module establishes the claim of a goal. -/
inductive Method where
  /-- By the judgment with fees: the text proves `<goal>_judged : <goal>Judged`, and the claim
  is concluded from it by a theorem that is generated. -/
  | fees
  /-- The text proves `<goal>_installed : <goal>Claim` itself. -/
  | direct
  deriving DecidableEq

/-- The proofs that an author writes for a protocol: their text, the modules that they use
beside those of the generator and of the model, and the names of their theorems, whose axioms
the module asks Lean to report. -/
structure ProofText where
  text : String := ""
  imports : List String := []
  theorems : List String := []
  /-- How the text establishes the claim of each goal. -/
  method : Method := .fees

/-- A module as Lean reads it, and the theorems whose axioms it asks for, in the order in which
the module states them. -/
structure Module where
  text : String
  theorems : List String
  /-- The module without the text of the proofs and without anything that is proved: the
  package, the facts, the transfers and the propositions of the goals, under the imports that
  the generator's statements need. The imports that a text asks for are not among them, so no
  word and no choice of an author is in it. The check outside the file compares the published
  theorems of `text` with the propositions that this module defines. A module that publishes
  nothing has none. -/
  reference : String := ""
  /-- The published theorems of `text`, each with its proposition, under their full names. -/
  published : List (String × String) := []

/-- A table of caps as a term. -/
def capsTerm (table : CapTable) : String :=
  let draw (d : DrawCap) := s!"⟨⟨{d.key.number}⟩, {d.numerator}, {d.denominator}, {d.count}⟩"
  let call (c : CallCap) := s!"⟨⟨{c.key.number}⟩, {c.count}, {c.callee}⟩"
  -- what adds up along a run: an item then the rest, or a choice of two arms then the rest
  let rec tally : Core.Tally Cap → String
    | .nil => ".nil"
    | .item (.draw d) rest => s!"(.item (.draw {draw d}) {tally rest})"
    | .item (.call c) rest => s!"(.item (.call {call c}) {tally rest})"
    | .choice left right rest => s!"(.choice {tally left} {tally right} {tally rest})"
  let use (u : UseCaps) := s!"⟨⟨{u.definition.number}⟩, {tally u.caps}⟩"
  s!"⟨[{", ".intercalate (table.uses.map use)}]⟩"

/-- The member of a list of headers that is `depth` places after its head. -/
def memberAt : Nat → String
  | 0 => "Member.head"
  | depth + 1 => s!"(Member.tail {memberAt depth})"

namespace Statements

/-- The package of the claims. -/
def package (s : Statements) : SourcePackage := s.claims.emission.package ⟨[], [], [], [], []⟩

/-- **The class of models that the statements are about**, read from the package: the least of
the descriptions whose samplers the package needs.

- A package whose coins are all positions (`index<n>`) is about the standard model over any
  data: nothing is assumed of a field.
- A package that draws anything else is about the arithmetic model over a field with at least
  as many elements as the scalar field of the source: a uniform scalar of the source is one of
  that many, and a charge that the source writes with that order bounds what a uniform scalar
  of the model pays for only in such a field. That model has samplers for a position, a scalar
  of that field and a sequence of such scalars. A package that draws something else again (a
  truth value, a group element, a scalar of another field) gets this class too, and its module
  is refused where the coverage is stated: no class has a sampler for it yet.

No caller chooses the class. A class that covers too little is refused by the kernel where the
module states the coverage; one that assumes more than a subject needs shows as a hypothesis of
the statement. -/
def chosenModel (s : Statements) : ModelText :=
  let positions := s.package.named.laws.all fun (law, _) =>
    match law with
    | .uniform (.fin _) => true
    | _ => false
  if positions then standardModelText else scalarFieldModelText

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
  let taken := claims.goals.map (·.goal) ++ ["root", "callee", "verifier", "prover", "site"]
  named.map fun (name, key) =>
    if taken.contains name || (named.filter (·.1 == name)).length > 1 then (s!"{name}{key}", key)
    else (name, key)

/-- The place of a function among the functions of the program before the root, which stand
last first. -/
def calleeMember (s : Statements) (key : Nat) : String :=
  let before := s.definitions.takeWhile (·.1 != s.claims.root)
  memberAt (((before.dropWhile (·.1 != key)).drop 1).filter (!·.2)).length

/-- A role of a protocol that the deciding role plays through applications: the protocol, the
role in it, and the definition whose body applies it. The application finds the protocol in the
table of the program before that definition. -/
structure AppliedRole where
  protocol : Nat
  role : Nat
  caller : Nat
  deriving BEq

/-- The applications in the stored body of a protocol of the package: each callee with the
roles of the caller that play the callee's, in the callee's order. -/
def applications (s : Statements) (key : Nat) : List (Nat × List Nat) :=
  match s.package.named.definitions.find? (·.key.number == key) with
  | some (.protocol _ _ _ _ body) =>
    (body.counted (some 1)).filterMap fun (_, operation, _) =>
      match operation with
      | .apply callee roles => some (callee.number, roles)
      | _ => none
  | _ => []

/-- The roles that a role of a definition plays in the protocols that the definition applies,
and through them: `depth` bounds how many applications are entered, and no chain of
applications is longer than the list of definitions. -/
def appliedFrom (s : Statements) : Nat → Nat → Nat → List AppliedRole → List AppliedRole
  | 0, _, _, found => found
  | depth + 1, caller, role, found =>
    (s.applications caller).foldl (init := found) fun found (callee, roles) =>
      match roles.idxOf? role with
      | none => found
      | some played =>
        let entry : AppliedRole := ⟨callee, played, caller⟩
        if found.contains entry then found
        else s.appliedFrom depth callee played (found ++ [entry])

/-- The roles that the deciding role of the root plays through applications, read from the
stored program: where a walk of the deciding role can go beside the root. -/
def appliedRoles (s : Statements) : List AppliedRole :=
  s.appliedFrom s.definitions.length s.claims.root s.claims.verifier []

/-- The place of a protocol among the protocols of the program before a definition, which
stand last first. -/
def protocolMember (s : Statements) (key caller : Nat) : String :=
  let before := s.definitions.takeWhile (·.1 != caller)
  memberAt (((before.dropWhile (·.1 != key)).drop 1).filter (·.2)).length

/-- The ports of the root, each with its type as a term and whether the deciding role holds
it. -/
def ports (s : Statements) : Except String (List (String × Bool)) := do
  let deciding := s.claims.verifier
  let some root := s.package.named.definitions.find? (·.key.number == s.claims.root)
    | throw "the package of the claims does not have the root"
  let .protocol _ _ ins _ _ := root | throw "the root of the claims is no protocol"
  return ins.map fun port => (ty (b := s.package.bindings) port.ty, port.holders.contains deciding)

/-- The types of the parameters of a goal's relation, as terms. -/
def relationInputs (s : Statements) (goal : ClaimedGoal) : Except String (List String) := do
  let some relation := s.package.named.definitions.find? (·.key.number == goal.relation)
    | throw s!"the package of the claims does not have the relation of {goal.goal}"
  let .fn _ ins _ _ _ _ _ _ := relation | throw s!"the relation of {goal.goal} is no function"
  return ins.map (ty (b := s.package.bindings))

/-- The names that the text after this one may use. -/
def opens : String :=
  "open Zkc.Formal Zkc.Formal.ProbabilisticProcess Zkc.Formal.Written OracleComp ProbComp\n" ++
  "open Zkc.Frontend.Written (CapTable UseCaps DrawCap CallCap)\n" ++
  "open scoped NNRat ENNReal\n"

/-- What was read from the source, as terms: the root, the roles, the functions before the root
that the text names, and for each goal its proof arguments, its table of caps and its
relation. -/
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
  String.join (s.claims.goals.map fun goal =>
    let name := goal.goal
    let relation := goal.relation
    s!"def {name}Caps : Zkc.Frontend.Written.CapTable := {capsTerm goal.caps}\n" ++
    String.join (goal.specification.toList.zipIdx.map fun (value, index) =>
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
each role that it plays in a protocol that is applied (`appliedRoles`), for each function
before the root that the text names and for each goal's relation, the meaning in its program
is stated to be the sealed denotation of the body. The equation is the one that the core
carries with the entry of the definition in its table (`roleMeaning_entry`,
`fnMeaning_entry`, from `Defs.protocolEntry` and `Defs.functionEntry`), so that the kernel compares a body with a body and does not run a lookup
against the interpreter: that comparison took 14 seconds for a function three entries deep in
a table and takes none now. For a role the body is the projection of the protocol to the role,
which the module names in the kernel's normal form: `verifierProgram` for the root, and
`Applied.role<protocol>_<role>Program` for a role of an applied protocol, by the keys (in a
name space of their own, which no name made from a name of the source is in). The equations
are `verifier_meaning`, `Applied.role<protocol>_<role>in<caller>_meaning` (the meaning in the
table that the applications of the definition `<caller>` read), `<function>_meaning` and
`<goal>_meaning`, for every model. Each has the label `walk_entry`: a walk on a goal that
judges such a meaning passes along the equation that fits, and a text names none of them. -/
def entries (s : Statements) : String :=
  let function (label member program : String) :=
    s!"/-- The function of `{label}` in its program is the denotation of its body. -/\n" ++
    s!"@[walk_entry]\ntheorem {label}_meaning (M : Model V) (inputs : HList M.Val {label}Header.ins) :\n" ++
    s!"    fnMeaning M {program} {member} inputs =\n" ++
    s!"      ({label}Body.denote (localSem M {label}Before.headers.fns (Defs.fnTable M {label}Before.defs)) []\n" ++
    s!"        (Env.empty.extend {label}Names inputs)).sealed := by\n" ++
    s!"  rw [Process.sealed_eq]\n  exact fnMeaning_entry M {program} {member} inputs\n\n"
  let label := "verifier"
  let role :=
      s!"-- The program of the {label}, in the kernel's normal form.\n" ++
      s!"kernel_normal {label}Program :\n" ++
      s!"    Term (roleDialect V calleeProgram.headers {label}Role) (Ctx.empty.extend rootNames) rootHeader.outs :=\n" ++
      s!"  project {label}Role rootBody\n\n" ++
      s!"/-- The process of the {label} in a run of the installed program is the denotation of its\n" ++
      "program. -/\n" ++
      s!"@[walk_entry]\ntheorem {label}_meaning (M : Model V) (path : List Frame)\n" ++
      s!"    (inputs : HList (RV M {label}Role) rootHeader.ins) :\n" ++
      s!"    roleMeaning M installed rootMember {label}Role path inputs =\n" ++
      s!"      ({label}Program.denote (roleSem M {label}Role (Defs.fnTable M calleeProgram.defs)\n" ++
      s!"        (Defs.rTable M calleeProgram.defs)) path (Env.empty.extend rootNames inputs)).sealed := by\n" ++
      s!"  rw [Process.sealed_eq, {label}Program.eq]\n" ++
      s!"  exact roleMeaning_entry M installed rootMember {label}Role path inputs\n\n"
  let applied := s.appliedRoles
  let programs := (applied.map fun a => (a.protocol, a.role)).eraseDups
  let appliedPrograms := String.join (programs.map fun (key, played) =>
    s!"-- The program of role {played} of the protocol with key {key}, in the kernel's normal form.\n" ++
    s!"kernel_normal Applied.role{key}_{played}Program :\n" ++
    s!"    Term (roleDialect V {s.programBefore key}.headers {played}) (Ctx.empty.extend names{key}) header{key}.outs :=\n" ++
    s!"  project {played} body{key}\n\n")
  let appliedEntries := String.join (applied.map fun a =>
    let (key, played, caller) := (a.protocol, a.role, a.caller)
    let table := s.programBefore caller
    let before := s.programBefore key
    let name := s!"Applied.role{key}_{played}in{caller}"
    let program := s!"Applied.role{key}_{played}Program"
    s!"noncomputable abbrev {name}Member : Member {table}.headers.protocols header{key} :=\n" ++
    s!"  {s.protocolMember key caller}\n\n" ++
    s!"/-- The process of role {played} of the protocol with key {key}, where the definition with key\n" ++
    s!"{caller} applies it, is the denotation of its program. -/\n" ++
    s!"@[walk_entry]\ntheorem {name}_meaning (M : Model V) (path : List Frame)\n" ++
    s!"    (inputs : HList (RV M {played}) header{key}.ins) :\n" ++
    s!"    roleMeaning M {table} {name}Member {played} path inputs =\n" ++
    s!"      ({program}.denote (roleSem M {played} (Defs.fnTable M {before}.defs)\n" ++
    s!"        (Defs.rTable M {before}.defs)) path (Env.empty.extend names{key} inputs)).sealed := by\n" ++
    s!"  rw [Process.sealed_eq, {program}.eq]\n" ++
    s!"  exact roleMeaning_entry M {table} {name}Member {played} path inputs\n\n")
  "noncomputable section\n\n" ++ role ++ appliedPrograms ++ appliedEntries ++
  String.join (s.functions.map fun (label, _) => function label s!"{label}Member" "calleeProgram") ++
  String.join (s.claims.goals.map fun goal =>
    function goal.goal s!"{goal.goal}Member" "installed") ++
  "end\n\n"

/-- The names of the theorems that `entries` writes. -/
def entryNames (s : Statements) : List String :=
  ["verifierProgram.eq", "verifier_meaning"] ++
  ((s.appliedRoles.map fun a => (a.protocol, a.role)).eraseDups.map fun (key, played) =>
    s!"Applied.role{key}_{played}Program.eq") ++
  (s.appliedRoles.map fun a => s!"Applied.role{a.protocol}_{a.role}in{a.caller}_meaning") ++
  s.functions.map (s!"{·.1}_meaning") ++ s.claims.goals.map (s!"{·.goal}_meaning")

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
  String.join (s.claims.goals.map fun goal =>
    let name := goal.goal
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

/-- Whether a name of the source can stand in a generated name as it is: letters of the basic
alphabet, digits and underscores, not beginning with a digit. A name of the source may be any
identifier of Unicode, of which Lean reads some as other tokens. -/
def plainName (name : String) : Bool :=
  !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') && !name.front.isDigit

/-- The names of the inputs of the root in a statement: the name that the source gives the port,
after `input_`, so that a reader of a statement sees which inputs the relation is applied to and
which the deciding role is run on. An input whose name in the source is no plain identifier, or
is the name of another input, is named by its place. -/
def inputNames (s : Statements) : List String :=
  let names := s.claims.inputs.toList
  names.zipIdx.map fun (name, index) =>
    if plainName name && (names.filter (· == name)).length == 1 then s!"input_{name}" else s!"port{index}"

def parts (s : Statements) (model : ModelText) (goal : ClaimedGoal) : Except String Parts := do
  unless goal.clause.kind == .proves do
    throw (s!"{goal.goal}: the goal reads a `reduces` clause. The statement of a reduction " ++
      "is about a return on which the reduced statement is true, and is not issued yet")
  let ports ← s.ports
  let named := s.inputNames
  unless named.length == ports.length do
    throw s!"{goal.goal}: the inputs of the deployed header are not those that the claims name"
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
  for position in goal.statement do
    unless (ports[position]?.map (·.2)) == some true do
      throw s!"{goal.goal}: the deciding role does not hold the input at {position} of the deployed header"
  let statement := goal.statement.toList.map name
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

/-- The total of a goal's table of caps, as the frontend computes it. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.total (goal : ClaimedGoal) : Rat := goal.caps.ratio

/-- The ceilings of the goals (GL4): a goal that states a ceiling is issued a statement only when
the total of its table of caps is within it. A source whose charges add up to more than its goal
promises gets no statement, and is told the two numbers. -/
def checkCeilings (s : Statements) : Except String Unit := do
  for goal in s.claims.goals do
    let some ceiling := goal.ceiling | continue
    unless goal.total ≤ ceiling do
      throw (s!"GL4: the goal `{goal.goal}` states the ceiling {ceiling}, and the total of its " ++
        s!"charges is {goal.total}")

/-- For each goal, what the module states of its table before any proof: the counts of the table
are those of the stored program (`<goal>_counted`), and its budget is the number that the
frontend computed (`<goal>_budget`), both decided by the kernel. The second ties the total of a
statement to the number that GL4 compares with a ceiling and that a reader can write down. -/
def counts (s : Statements) : String :=
  String.join (s.claims.goals.map fun goal =>
    let name := goal.goal
    let total := goal.total
    s!"/-- The table of caps of `{name}` adds up as the stored program does: its counts and its arms are the program's. -/\n" ++
    s!"theorem {name}_counted : {name}Caps.counted stored rootKey = true := by decide +kernel\n\n" ++
    s!"/-- The budget of the table of caps of `{name}`: the number that the frontend computed. -/\n" ++
    s!"theorem {name}_budget : {name}Caps.budget = (({total.num.toNat} : ℕ) : ℚ≥0) / ({total.den} : ℕ) := by\n" ++
    "  decide +kernel\n\n")

/-- The names of the theorems that `counts` writes. -/
def countNames (s : Statements) : List String :=
  s.claims.goals.flatMap fun goal => [s!"{goal.goal}_counted", s!"{goal.goal}_budget"]

/-- For each goal with a ceiling, the theorem `<goal>_ceiling`: the total of the goal's table is
within the ceiling, the comparison decided by the kernel. -/
def ceilings (s : Statements) : Except String String := do
  s.checkCeilings
  let mut text := ""
  for goal in s.claims.goals do
    let some ceiling := goal.ceiling | continue
    let name := goal.goal
    text := text ++
      s!"/-- The total of the charges of `{name}` is within the ceiling that the goal states. -/\n" ++
      s!"theorem {name}_ceiling : {name}Caps.total ≤ (({ceiling.num.toNat} : ℕ) : ℝ≥0∞) / ({ceiling.den} : ℕ) :=\n" ++
      s!"  {name}Caps.total_le_div {ceiling.num.toNat} {ceiling.den} (by decide) (by decide +kernel)\n\n"
  return text

/-- The experiment of a goal, as text: the deciding role of a program on its inputs returns with
probability at most a bound, against the services that the formal library's experiment is
about (`ReturnsWithin`: they draw within the samplers of the model and answer only what is
permitted). The generator names the process, the samplers and the bound; what the probability
is of is the library's definition. The event of a deciding protocol is that the role returns. -/
def returnsWithin (model : ModelText) (program root inputs bound : String) : String :=
  s!"ReturnsWithin (roleMeaning {model.model} {program} {root} verifierRole path {inputs})\n" ++
  s!"        {model.samplers} (Permitted {model.model}) (fun _ => True) ({bound})"

/-- That the experiment of a model is not about nothing, as text: some service with a state
draws within the samplers and answers only what is permitted (`Served`). -/
def served (model : ModelText) : String :=
  s!"Served {model.samplers} (Permitted {model.model})"

/-- The theorem `covered`: the model covers the stored program of the package, decided by the
kernel. A statement over a model is issued with it, so that the statement is about this program
and not about one in which a row is a constant or a coin has no distribution. -/
def coverage (model : ModelText) : String :=
  "/-- **The model covers the package.** It interprets every row of the vocabulary that the\n" ++
  "package links and has a sampler for the law of every coin that the package draws. -/\n" ++
  s!"theorem covered : {model.covers} stored = true := by decide +kernel\n\n"

/-- What a goal claims of a program with its root and the relation of the goal's clause, as the
text of a proposition: on valid inputs of the deciding role on which the relation returns false,
that role returns within the total of the goal's table of caps, in the experiment of the formal
library (`ReturnsWithin`). -/
def claimAt (s : Statements) (model : ModelText) (goal : ClaimedGoal)
    (program root relation : String) : Except String String := do
  let parts ← s.parts model goal
  return s!"∀ {model.binders} (path : List Frame),\n" ++
    model.assumed ++ parts.quantified ++
    s!"    {parts.premise program relation} →\n" ++
    s!"      {returnsWithin model program root parts.inputs s!"{goal.goal}Caps.total"}"

/-- For each goal, what is stated before any proof is written, so that no name defined by the
text of a proof can change it:

- `<goal>ClaimOf p root relation`, the claim about a program with its root and the relation of
  the goal's clause, and `<goal>Claim`, the claim about the installed program, which the text
  proves;
- `<goal>Goal`: in every program that admission gives for the package, the root and the
  relation are found by their keys and the claim holds of them;
- `<goal>Result`: the model covers the package, the counts of the goal's table of caps are those
  of the stored program, and the goal holds;
- `<goal>Witnessed`: the hypotheses of the claim are met together by some model, valid inputs
  and a service with a state, with the relation returning false there. The text proves it, so
  that the claim is not about nothing. -/
def claimTexts (s : Statements) (model : ModelText) : Except String String := do
  let mut text := ""
  for goal in s.claims.goals do
    let name := goal.goal
    let parts ← s.parts model goal
    text := text ++
      s!"/-- What the goal `{name}` claims of a program with its root and the relation of the goal's\n" ++
      "clause: on valid inputs of the deciding role on which the relation returns false, that role\n" ++
      "returns with probability at most the total of the goal's table of caps, against every service that\n" ++
      "draws within the samplers of the model and answers only what is permitted (`ReturnsWithin`). -/\n" ++
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
      s!"/-- **The result of the goal `{name}`**: the model covers the package, the counts of the goal's\n" ++
      "table of caps are those of the stored program, and the goal holds. A result over a model is\n" ++
      "about the program only where the model covers it, and a bound by a table is about the program\n" ++
      "only where the table has its counts. -/\n" ++
      s!"def {name}Result : Prop :=\n" ++
      s!"  {model.covers} stored = true ∧ {name}Caps.counted stored rootKey = true ∧ {name}Goal\n\n" ++
      s!"/-- The hypotheses of the claim of `{name}` are met together: some model with what the claim\n" ++
      "assumes of it, valid inputs on which the relation returns false, and a service with a state\n" ++
      "that draws within the samplers and answers only what is permitted (`Served`). -/\n" ++
      s!"def {name}Witnessed : Prop :=\n  ∃ {model.existential},\n" ++
      model.assumedConjuncts ++ parts.existential ++
      s!"    {served model} ∧\n" ++
      s!"      {parts.premise "installed" s!"{name}Member"}\n\n"
  return text

/-- The name of a draw of the root in a module: the name of its site in the source, with
its place among the draws that realize the site where a stepped loop gives several. -/
def siteLabel (site : String) (index count : Nat) : String :=
  if count == 1 then site else s!"{site}_{index}"

/-- The named draws of a goal's root, each with the name of its site in the source, its name
in a module and its key. The name in a module is the site's (`siteLabel`) where that is a plain
name, and `key<number>` of the draw where it is not. A name that two charged draws would share
(a site `r_0` beside the first draw of a stepped loop over `r`) is followed by the key of each.
The name of a charged draw does not depend on the draws that the contract does not charge: a
draw without a charge whose name another draw has is the one that is followed by its key. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.siteLabels (goal : ClaimedGoal) :
    List (String × String × Core.Key) :=
  let capped := (goal.caps.uses.getLast?.map (·.draws)).getD []
  let charged (key : Core.Key) : Bool := capped.any (·.key == key)
  let draws := goal.sites.flatMap fun (site, keys) =>
    keys.zipIdx.map fun (key, index) =>
      (site, if plainName site then siteLabel site index keys.length else s!"key{key.number}", key)
  draws.map fun (site, label, key) =>
    let sharing := draws.filter fun other => other.2.1 == label && other.2.2 != key
    let shared :=
      if charged key then sharing.any fun other => charged other.2.2 else !sharing.isEmpty
    if shared then (site, s!"{label}_key{key.number}", key) else (site, label, key)

/-- The draws of a goal's root that its table of caps gives a cap, each with its name
in a module and that cap. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.siteCaps (goal : ClaimedGoal) :
    List (String × DrawCap) :=
  let capped := (goal.caps.uses.getLast?.map (·.draws)).getD []
  goal.siteLabels.filterMap fun (_, label, key) =>
    (capped.find? (·.key == key)).map fun cap => (label, cap)

/-- The name, in a module, of a draw below applications of the root: `site_`, then the keys of
the applications in their order, then the key of the draw. A number follows `site_`, where the
name of a draw of the root has the name of a site of the source or `key`, so the two never
meet. -/
def appliedSite (site : Core.Site) : String :=
  "site_" ++ "_".intercalate ((site.through ++ [site.key]).map fun key => toString key.number)

/-- The draws of the root under the names of their sites: the key of each
(`site_<name>`, and `site_<name>_<index>` for each block of a stepped loop), once for the
package, and for each goal the cap that its table gives the draw (`<goal>_cap_<name>`), decided
by the kernel. A text can name a draw as the source does, and where it pays a fee at such a
draw the fee is compared with the cap stated here (the label `walk_cap`), so that a fee that is
not within it is refused with the name of the site. -/
def sites (s : Statements) : String :=
  let named := (s.claims.goals.flatMap (·.siteLabels)).eraseDups
  String.join (named.map fun (site, label, key) =>
    s!"/-- A draw of the root: `sites.{site}` of the source. -/\n" ++
    s!"abbrev site_{label} : Key := ⟨{key.number}⟩\n\n") ++
  String.join (s.claims.goals.map fun goal =>
    String.join (goal.siteCaps.map fun (label, cap) =>
      s!"/-- The cap that the table of `{goal.goal}` gives the draw `{label}`. -/\n" ++
      s!"@[walk_cap]\ntheorem {goal.goal}_cap_{label} :\n" ++
      s!"    {goal.goal}Caps.capFrom {goal.goal}Caps.root [] site_{label} = " ++
      s!"{cap.numerator} / {cap.denominator} := by\n  decide +kernel\n\n")) ++
  -- the draws below applications: a draw is charged in the contract of the protocol that has
  -- it, and the table gives the root its cap through the applications that reach it
  let applied := (s.claims.goals.flatMap fun goal =>
    (goal.caps.sites.filter (!·.1.through.isEmpty)).map (·.1)).eraseDups
  String.join (applied.map fun site =>
    s!"/-- A draw below the applications {site.through.map (·.number)} of the root: the draw with\n" ++
    s!"key {site.key.number} of the protocol that the last of them applies. -/\n" ++
    s!"abbrev {appliedSite site} : Key := ⟨{site.key.number}⟩\n\n") ++
  String.join (s.claims.goals.map fun goal =>
    String.join ((goal.caps.sites.filter (!·.1.through.isEmpty)).map
      fun (site, numerator, denominator, _) =>
        let through := ", ".intercalate (site.through.map fun key => s!"⟨{key.number}⟩")
        s!"/-- The cap that the table of `{goal.goal}` gives the draw `{appliedSite site}`. -/\n" ++
        s!"@[walk_cap]\ntheorem {goal.goal}_cap_{appliedSite site} :\n" ++
        s!"    {goal.goal}Caps.capFrom {goal.goal}Caps.root [{through}] {appliedSite site} = " ++
        s!"{numerator} / {denominator} := by\n  decide +kernel\n\n"))

/-- The names of the theorems that `sites` writes. -/
def siteNames (s : Statements) : List String :=
  s.claims.goals.flatMap fun goal =>
    (goal.siteCaps.map fun (label, _) => s!"{goal.goal}_cap_{label}") ++
    ((goal.caps.sites.filter (!·.1.through.isEmpty)).map fun (site, _) =>
      s!"{goal.goal}_cap_{appliedSite site}")

/-- What the method of fees has to establish for a goal, as the text of a proposition: on valid
inputs of the deciding role on which the relation returns false, the role's process in the
installed program is judged never to return within the budget of the goal's table of caps, each
fee within what the table allows the effect that pays it. The binders are named: what the model
is built from, `path`, the hypotheses of the model, each input with its validity, `rejected`. -/
def judgedAt (s : Statements) (model : ModelText) (goal : ClaimedGoal) : Except String String := do
  let name := goal.goal
  let parts ← s.parts model goal
  let premise := parts.premise "installed" s!"{name}Member"
  return s!"∀ {model.binders} (path : List Frame)\n" ++
    model.assumedBinders ++ parts.binders ++
    s!"    (rejected : {premise}),\n" ++
    s!"    (roleMeaning {model.model} installed rootMember verifierRole path {parts.inputs}).interpret\n" ++
    s!"      (.charged (Permitted {model.model})\n" ++
    s!"        (paysWithin {model.samplers} ({name}Caps.allowance {model.model} path)))\n" ++
    s!"      (fun _ _ => False) (fun _ _ => True) {name}Caps.budget"

/-- For each goal, what the method of fees has to establish, stated before any proof, and what
follows from it:

- `<goal>Judged`: on valid inputs of the deciding role on which the relation returns false, the
  role's process in the installed program is judged never to return within the budget of the
  goal's table of caps, each fee within what the table allows the effect that pays it. Its
  binders are named (what the model is built from, `path`, each input with its validity,
  `rejected`), and `claim_intro` introduces them under those names;
- `<goal>_claim_of_judged : <goal>Judged → <goal>Claim`, by the library's bridge from the
  judgment to the experiment;
- `<goal>_witnessed_of`: the hypotheses of the claim are met at any valid inputs on which the
  relation returns false, with the service of the model's laws. -/
def judgments (s : Statements) (model : ModelText) : Except String String := do
  let mut text := ""
  for goal in s.claims.goals do
    let name := goal.goal
    let parts ← s.parts model goal
    let premise := parts.premise "installed" s!"{name}Member"
    let given := model.hypotheses.map (·.1) ++ (parts.names.splitOn " ").filter (!·.isEmpty)
    text := text ++
      "set_option linter.unusedVariables false in\n" ++
      s!"/-- **What the judgment with fees establishes for `{name}`**: on valid inputs of the deciding\n" ++
      "role on which the relation returns false, the role is judged never to return within the\n" ++
      "budget of the goal's table of caps, each fee within what the table allows the effect that\n" ++
      "pays it. -/\n" ++
      s!"def {name}Judged : Prop :=\n  " ++ (← s.judgedAt model goal) ++ "\n\n" ++
      s!"/-- The claim of `{name}` follows from the judgment. -/\n" ++
      s!"theorem {name}_claim_of_judged (judged : {name}Judged) : {name}Claim := by\n" ++
      "  claim_intro\n" ++
      "  exact returnsWithin_of_never _ _ _ _ _ (by apply judged <;> assumption)\n\n" ++
      s!"/-- The hypotheses of the claim of `{name}` are met at valid inputs on which the relation\n" ++
      "returns false, with the service of the model's laws. -/\n" ++
      s!"theorem {name}_witnessed_of {model.binders}\n" ++
      model.assumedBinders ++ parts.binders ++
      s!"    (rejected : {premise}) :\n    {name}Witnessed :=\n" ++
      s!"  ⟨{", ".intercalate ([model.witnesses] ++ given ++ [model.served, "rejected"])}⟩\n\n"
  return text

/-- The names of the theorems that `judgments` writes. -/
def judgmentNames (s : Statements) : List String :=
  s.claims.goals.flatMap fun goal =>
    [s!"{goal.goal}_claim_of_judged", s!"{goal.goal}_witnessed_of"]

/-- For each goal whose claim the text established by the judgment with fees, the claim about
the installed program, from the theorem `<goal>_judged` of the text. -/
def conclusions (s : Statements) : String :=
  String.join (s.claims.goals.map fun goal =>
    s!"/-- The claim of `{goal.goal}`, from the judgment that the text established. -/\n" ++
    s!"theorem {goal.goal}_installed : {goal.goal}Claim :=\n" ++
    s!"  {goal.goal}_claim_of_judged {goal.goal}_judged\n\n")

/-- The names of the theorems that `conclusions` writes. -/
def conclusionNames (s : Statements) : List String :=
  s.claims.goals.map fun goal => s!"{goal.goal}_installed"

/-- For each goal, after the text of the proofs: the theorems `<goal>_sound : <goal>Goal`,
`<goal>_result : <goal>Result` and `<goal>_met : <goal>Witnessed`, from the theorems
`<goal>_installed : <goal>Claim` (the text's, or the one that `conclusions` writes from the
text's judgment) and `<goal>_witnessed : <goal>Witnessed` of the text. The statements were
fixed before the text; only their proofs are written here. -/
def closings (s : Statements) : String :=
  String.join (s.claims.goals.map fun goal =>
    let name := goal.goal
    s!"/-- The goal `{name}`, for every admitted program. -/\n" ++
    s!"theorem {name}_sound : {name}Goal :=\n" ++
    s!"  fun admitted => at_{name} admitted {name}ClaimOf ({name}_installed : {name}Claim)\n\n" ++
    s!"/-- The result of the goal `{name}`. -/\n" ++
    s!"theorem {name}_result : {name}Result := ⟨covered, {name}_counted, {name}_sound⟩\n\n" ++
    s!"/-- The hypotheses of the claim of `{name}` are met. -/\n" ++
    s!"theorem {name}_met : {name}Witnessed := {name}_witnessed\n\n")

/-- The names of the theorems that `closings` writes. -/
def closingNames (s : Statements) : List String :=
  s.claims.goals.flatMap fun goal =>
    [s!"{goal.goal}_sound", s!"{goal.goal}_result", s!"{goal.goal}_met"]

/-- The names of the theorems that `ceilings` writes. -/
def ceilingNames (s : Statements) : List String :=
  s.claims.goals.filterMap fun goal => goal.ceiling.map fun _ => s!"{goal.goal}_ceiling"

/-- The modules that a module of statements imports: those of the printed package, those of
the library that the generated statements name, and the model's. A text that walks the program
has the walk and the equations where it starts; `walks` says whether the module is for one. -/
def imports (model : ModelText) (walks : Bool) : List String :=
  packageImports ++
    (if walks then ["Zkc.Core.Evidence.FunctionEntry", "Zkc.Core.Evidence.ProtocolReadback",
      "Zkc.Formal.Walk",
      "Zkc.Formal.Written.WalkFees"] else []) ++
    ["Zkc.Formal.OracleProcess", "Zkc.Formal.ReturnExperiment", "Zkc.Formal.Written.LawSamplers",
      "Zkc.Formal.Written.SiteCaps", "Zkc.Formal.Written.FunctionMeaning",
      "Zkc.Formal.Written.ClaimIntro", "Zkc.Formal.Written.Published"] ++ model.imports

/-- The lines that open a module: its imports, and the namespace of the core. -/
def header (modules : List String) : String :=
  String.join (modules.map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The published theorems of the goals, each with the proposition that it states, under their
full names in the module `name`: for a goal, `<goal>_installed : <goal>Claim`,
`<goal>_sound : <goal>Goal`, `<goal>_result : <goal>Result`, `<goal>_met : <goal>Witnessed`.
The check inside a module (`publications`) and the check outside it
(`Zkc/Tools/Formal/VerifyPublication.lean`) are both given this one list. The theorems
themselves are written by `closings`, which spells the same endings: if the two came apart, the
check outside would find no theorem under the listed name. -/
def publicationPairs (s : Statements) (name : String) : List (String × String) :=
  s.claims.goals.flatMap fun goal =>
    [("_installed", "Claim"), ("_sound", "Goal"), ("_result", "Result"), ("_met", "Witnessed")].map
      fun (theorem_, proposition) =>
        (s!"{name}.{goal.goal}{theorem_}", s!"{name}.{goal.goal}{proposition}")

/-- For each goal, the check that the theorems written after the text of the proofs state
exactly the propositions that were defined before it (`published`,
`Zkc/Formal/Written/Published.lean`). Those theorems are elaborated in the scope that the text
leaves: a variable that the text declared there is a hypothesis of each of them that can use
it, and then the theorem is not of its proposition, though Lean accepts it and reports no axiom
for it. The check reads the type that Lean stored for the theorem, under its full name. -/
def publications (s : Statements) (name : String) : String :=
  String.join ((s.publicationPairs name).map fun (theorem_, proposition) =>
    s!"published {theorem_} : {proposition}\n")

/-- The requests for the axioms of theorems, and the end of the module's namespace. -/
def footer (name : String) (theorems : List String) : String :=
  String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

/-- **The module of the goals of one scheme**: the package of the claims; what is generated
before any proof (the facts, the coverage, the counts, the names of the draws, where
the walks start, the transfers, the propositions of each goal and, for a text of the method of
fees, the judgment of each goal with what follows from it, and the comparisons with the
ceilings); the author's text; the claim of each goal from the text's judgment, for that method;
the closing theorems; what a check writes after them (`after`: a consumer of the published
theorems); the check that each theorem written after the text states exactly its proposition
(`publications`); and a request for the axioms of every theorem. The order of the parts, the
imports, the names of the generated theorems and the class of models (`chosenModel`) are
decided here and by no caller; a control that states a claim about another class gives its
own description (`model`).

What the generator states of a goal stands before the text, so that nothing which the text
declares takes part in it; what it proves after the text is checked to be of those statements.
A text that sets an option for debugging is refused before Lean reads it: one of those options
has the kernel not check a declaration. That guards against an accident, and it is a search for
a string: a text can spell the option otherwise, or set it by a command of its own, and Lean
then accepts a false theorem and reports no axiom for it. So Lean's acceptance of this module
is not what a check of a subject rests on. The check compiles the module to an object and has
it read outside the file (`Zkc/Tools/Formal/VerifyPublication.lean`): the kernel replays the
declarations of the object on the imports (all that it checks: not code marked `unsafe`, which
no theorem can use), the published theorems are read from the result of
that replay, each is of its proposition as a module generated without the text and without
the text's imports defines it (`Module.reference`, with the definitions that the proposition
uses), and the axioms are read from the replayed proofs. Every module of a check, a proof module as a control with the same
text, is elaborated in a sandbox (the file system read-only but for the module's own folder, no
network, no socket, no process that outlives it), so a text cannot change the program, the reference or
the imports before they are read. What is trusted is then
the toolchain, the imports, this generator, that program and the sandbox. The object that is
read is whatever the run of Lean on the text left in the module's folder, which a text can
write itself: the program replays every declaration that it finds there and compares the
published theorems with the reference, so what it accepts is a proof of the reference's
propositions whoever wrote the file; but it maps the file into memory without checking its
format, so that the reader of objects behaves on such a file as on an object is trusted too
(the program runs in the sandbox, where a malformed object can change no file). A statement
that a check itself writes after the text (a consumer, with its numerals and notations) is
still read in the scope that the text leaves. -/
def module (s : Statements) (name : String) (proof : ProofText)
    (walks := true) (after : ProofText := {}) (model : ModelText := s.chosenModel) :
    Except String Module := do
  if (proof.text ++ after.text).contains "debug." then
    throw s!"{name}: the text sets an option for debugging"
  let claims ← s.claimTexts model
  let ceilings ← s.ceilings
  let fees := proof.method == .fees
  let judgments ← if fees then s.judgments model else pure ""
  let theorems := ["admitted_exists", "covered"] ++ s.countNames ++ s.siteNames ++
    (if walks then s.entryNames else []) ++ (if fees then s.judgmentNames else []) ++
    s.ceilingNames ++ proof.theorems ++ (if fees then s.conclusionNames else []) ++
    s.closingNames ++ after.theorems
  let stated := s!"namespace {name}\n" ++ (Written.package s.package).text ++ opens ++ s.facts ++ "\n"
  -- what the reference has stands first and in the reference's order, so that the two modules
  -- elaborate the same commands up to the end of the claims
  let text := header (imports model walks ++ proof.imports ++ after.imports) ++ stated ++
    s.transfers ++ claims ++
    coverage model ++ s.counts ++ s.sites ++ (if walks then s.entries else "") ++
    judgments ++ ceilings ++ proof.text ++ "\n" ++
    (if fees then s.conclusions else "") ++ s.closings ++ after.text ++ s.publications name ++
    footer name theorems
  -- the reference imports what the generator's statements need and nothing that a text or a
  -- check asked for: an import of the text that changed how a statement is read would make the
  -- two modules differ
  let reference := header (imports model walks) ++ stated ++ s.transfers ++ claims ++ s!"end {name}\n"
  return { text, theorems, reference, published := s.publicationPairs name }

/-- A module with the package of the claims and the statements of the goals, with no proof: the
facts, the transfers and the propositions. Lean elaborates the statements. -/
def statementsModule (s : Statements) (name : String) (model : ModelText := s.chosenModel) :
    Except String String := do
  return header (imports model false) ++ s!"namespace {name}\n" ++
    (Written.package s.package).text ++ opens ++ s.facts ++ "\n" ++ s.transfers ++
    (← s.claimTexts model) ++ s!"end {name}\n"

/-- A module with the package of the claims and the one theorem that a model covers it. -/
def coverageModule (s : Statements) (name : String) (model : ModelText := s.chosenModel) : Module :=
  let text := header (packageImports ++ ["Zkc.Formal.Written.LawSamplers"] ++ model.imports) ++
    s!"namespace {name}\n" ++ (Written.package s.package).text ++ "open Zkc.Formal.Written\n" ++
    coverage model ++ footer name ["covered"]
  { text, theorems := ["covered"] }

/-- A module with the package of the claims, its facts, and the comparison of each goal's total
with the ceiling that it states. A goal whose ceiling is below its total gives no module. -/
def ceilingModule (s : Statements) (name : String) : Except String Module := do
  let ceilings ← s.ceilings
  let text := header (packageImports ++ ["Zkc.Formal.Written.SiteCaps"]) ++
    s!"namespace {name}\n" ++ (Written.package s.package).text ++ opens ++ s.facts ++ "\n" ++
    ceilings ++ footer name s.ceilingNames
  return { text, theorems := s.ceilingNames }

end Statements

end Zkc.Frontend.Written
