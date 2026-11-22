# Writing a subject of a written soundness goal

A subject is a source with a soundness goal, the text of its proofs, and a check that runs Lean on the two. This page says what each of the three is, what is generated around a text, and what a text writes. The five subjects of the repository are the examples: `lean/formal/checks/GuessCharge.lean`, `CountCharge.lean`, `FreivaldsCharge.lean`, `EitherCharge.lean` and `TwiceCharge.lean`, each with its text in the file of the same name ending in `.lean.in`. [Status](status.md) says what the path supports and what it does not.

## The three parts

**The source** declares a protocol, the relation that its verifier decides, a contract with a `proves` clause and the charges of its draws, a scheme and a goal:

```
module t
use zkc::security::{soundness}
relation Holds(claim: bool): claim
protocol Either roles(P, V)(claim: bool @(P, V), first: index<8> @P, second: index<4> @P):
    if claim:
        a <- send first from P to V
        x <- draw index<8> from V to P
        guard @V x == a
    else:
        b <- send second from P to V
        guard @V b != 3
        y <- draw index<4> from V to P
        guard @V y == b
spec for Either:
    proves @V Holds(claim)
    charge sites.x <= 1 / 8
    charge sites.y <= 1 / 4
scheme Checked = Either:
    prover P
    construction interactive
goal either = soundness(Checked, stage = written)
```

The claim of the goal: on inputs on which the relation returns false, the verifier returns with probability at most the total of the charges that the root reaches (here three eighths), against every service that draws each coin no more favourably than its law.

**The text** is a Lean file without a header, between `noncomputable section` and `end`. It proves, for each goal, the judgment that the generator states (`<goal>_judged : <goal>Judged`) and that the hypotheses of the claim are met at some input (`<goal>_witnessed : <goal>Witnessed`). The propositions that a module publishes are all generated before the text, and the text states none of them. What it states is its own: what the relation computes, and any law or lemma that its proofs use. The first is needed by every text, since the judgment assumes that the relation returns false and the text has to say what that means of the inputs:

```lean
theorem either_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]
    [DecidableEq G] (claim : Bool) :
    functionResult (t := .bool)
      (fnMeaning (StandardModel.model D) installed eitherMember (.cons claim .nil)) =
        some claim := by
  kernel_rfl
```

A relation that the kernel does not compute on variables (one with a loop) is walked as any function is (`Count<8>`, Freivalds).

**The check** is a Lean file that reads the source with the frontend, asserts what it read, and runs Lean on the generated module. With the library of `lean/compiler/Zkc/Tests/Frontend/WrittenSubject.lean` it is data:

```lean
def reading : Reading where
  goals := ["either"]
  ports := #["claim", "first", "second"]
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

def run (template work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read source reading
  let _ ← check work "Either" written
    { text := template, theorems := ["either_relation", "either_judged", "either_witnessed"] }
    [/- controls -/]
```

The rest of a check file is frame that the five checks share word for word: the imports, the `open`s, and at the end `#eval show IO Unit from IO.FS.withTempDir fun work => run "checks/EitherCharge.lean.in" work`. The path of the text is relative to `lean/formal`, where a check is run: `lake lean checks/EitherCharge.lean`. A text that uses a lemma of a library module that the generated module does not import names the module in `imports` of its proof (Freivalds: `Zkc.Formal.Written.FixedSequences`, `Mathlib.Data.Matrix.Mul`).

A subject is accepted when Lean accepts the proof module; the module is accepted outside the file, where the kernel replays it and its published theorems are compared with the generator's (below, "A check does not rest on Lean's acceptance"); every theorem of it, generated or of the text, rests on `propext`, `Classical.choice` and `Quot.sound` at most; Lean accepts the module in which the package is compared with what the frontend gives to admission (`<Name>Source`); and every control is refused as it says.

A `Reading` asserts the ports of the root, the clause that each goal reads, the inputs of the deployed header that the relation is applied to, the number of proof arguments, the roles of the scheme, and the class of models (`model`, the standard model unless said). A reading that is not what the check asserts is an error: the text is written against it. A relation with witness parameters is not a subject yet. What else a check asserts of the reading is its own; the five checks assert the table of caps and the names of the draws:

```lean
  let goal ← written.goal
  unless goal.total == 3 / 8 && (goal.caps.uses.map fun use => use.draws.map fun draw =>
      (draw.numerator, draw.denominator, draw.count)) == [[(1, 8, 1), (1, 4, 1)]] do
    throw (IO.userError "the table of caps is not the two draws at 1/8 and 1/4")
  unless goal.siteLabels.map (·.2.1) == ["x", "y"] do
    throw (IO.userError "the draws are not named `x` and `y`")
```

## What stands before the text

The generator (`lean/compiler/Zkc/Frontend/Written/Statement.lean`) writes the printed package and, from what the frontend read, the names that a text uses. For a goal `either` of a root with the ports above:

| Name | What it is |
| --- | --- |
| `installed`, `rootMember`, `verifierRole`, `proverRole` | the program that the module installs from the package, the root in it, the two roles |
| `eitherMember` | the function of the relation at the goal's value; a function that the root calls has `<function>Member` |
| `eitherCaps`, `either_budget` | the table of caps of the goal, and its budget as a number |
| `site_x`, `site_y` | each named draw of the root, under its name in the source, charged or not |
| `either_cap_x`, `either_cap_y` | the cap that the table gives each charged draw |
| `eitherJudged` | the judgment that the text proves |
| `either_witnessed_of` | the theorem that gives `eitherWitnessed` from an input on which the relation returns false |
| `eitherClaim`, `eitherGoal`, `eitherResult`, `eitherWitnessed` | the published propositions: the claim about the installed program, the goal for every admitted program, the result with the coverage, and that the hypotheses are met |
| `either_installed`, `either_sound`, `either_result`, `either_met` | their theorems, written after the text from `either_judged` and `either_witnessed` |

The class of models is read from the package: the standard model over any data (`D : StandardModel.Data F G`) where every coin is a position, and otherwise the arithmetic model over a field `F` with at least the order of the source's scalar field (a hypothesis `large`), which has samplers for a position, a scalar and a sequence of scalars. A package that draws anything else is refused where its module states the coverage.

To see a generated module, keep the working directory of a check: replace `IO.FS.withTempDir fun work =>` by a function that passes a directory of yours, and read `<Name>.lean` there.

## What a text writes

The judgment is about the verifier's process: on inputs on which the relation returns false it is judged never to return, within the budget of the table, each fee within what the table allows the effect that pays it. A text walks the program to the places where it has something to say.

```lean
theorem either_judged : eitherJudged := by
  claim_intro
  obtain rfl : input_claim = false :=
    Option.some.inj ((either_relation D input_claim).symm.trans rejected)
  walk_free as sent
  walk as allowed
  walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = sent) as drawn differs
  case weight => simpa using prEvent_drawPosition_eq_le 3 sent
  walk as hit
  exact differs (Nat.eq_of_beq_eq_true hit)
```

**`claim_intro`** introduces the binders of the judgment under the names that the generator gave them: what the model is built from (`D`, or `F` and `G`), `path`, each input that the verifier holds as `input_<port>` with `valid_input_<port>` (`input_claim` here; the two positions are the prover's and have no binder), a hypothesis of the model by its name, and `rejected`, that the relation returns false.

**`walk`** goes to the next effect, loop, call of a function by a role, or the end of the program. It goes into the arm of a choice and into a block as into a program. At the end, what is left is what the judgment asks there, stated in the inputs, the replies and the names of the text. `walk … at h` walks a hypothesis that judges a process. The two tactics of an effect walk to the effect themselves, so a text writes `walk` where it names a fork, before a loop or a call, and to reach the end.

A condition of the source shows in a goal as the values that it computes: `or` as `||`, `==` on positions as `Nat.beq`, `!=` as its negation, and an operand that the kernel computes is gone (`false || c` is `c`). The hypothesis of the last guard above is `hit : drawn.beq sent = true`, and `Nat.eq_of_beq_eq_true` reads it. To see a goal, write `trace_state` after a tactic and run the check.

**Nothing that an instruction binds has a name.** A value of a step shows in a goal under a name that a text cannot write (`value✝`). A text names what it speaks of:

- a reply, at its effect (`as sent`, `as drawn`);
- a fork, where a step waits on a value: `walk as h` names the hypothesis that says which form the value is, `walk as ⟨x, h⟩` also the parts of that form (the entry that a read found), and `walk as ⟨x, h⟩, g` the forks on the way in order. A side that holds as it stands (a guard that stops the run, where the judgment asks nothing of a stop) is closed; the walk goes on in every other. A name for which no fork is met is an error;
- the arguments of an invariant (below).

**At an effect** under the judgment with fees:

- `walk_free as v`: nothing is excluded and no fee is paid. The reply is `v`, and `permitted_v` says that it is permitted. A reply has its computed type: a scalar is a value of the field of the model, and so is a part of a tuple and an item of a sequence, so that a theorem about the field or about a list over it applies to `v.1` or to `v` as it stands. The inputs that `claim_intro` introduces are read the same way. A message got has no sampler and is met this way.
- `walk_pay fee excluding set as v kept`: a coin pays `fee` for the replies in `set`. It leaves, in this order: `weight`, that the sampler draws a reply of the set with probability at most the fee, which is the mathematics of the step; `within`, that the fee is at most what is left of the budget (the budget less the fees paid before), unless a hypothesis of the goal is exactly that or the kernel decides it on closed numbers (a fee over what is left is then refused); `cap`, that the fee is within the cap of the draw, unless the kernel decides it; and then the rest after a reply `v` with `kept : ¬ set v`, judged within the budget less the fee. The cap is compared first: a fee over the cap that the module states is refused with the name of the site, also where it is over what is left of the budget.

**An application.** Where the root applies a protocol in which the deciding role plays a role, `walk` goes into it (an application in which it plays none is passed like any other instruction): the next effect that the text meets is the callee's, at the path of the application, and after the callee's last instruction the walk is in the root again, with the results that the application gave as values. A text writes nothing at the application itself (the check of `Twice` has the case, a root that applies a protocol that applies another, and a root that applies one in the body of a loop). A fork inside the callee is named by the text as a fork of the root is: `walk as kept` at a guard of the callee, and `walk as chosen` at its choice, with a goal for each arm (the root `Forked` of that check). Four things follow from where a callee stands in a program:

- a draw of the callee is charged in the callee's contract, and the table gives the root its cap through the application. `walk_pay` compares the fee with that cap, and the module names the draw `site_<application>_<draw>` by the keys of the applications and of the draw;
- a function that the callee calls is read in the table of the definitions before the callee. A text states a law of a function once, of `fnMeaning M calleeProgram <function>Member`, and `walk_law` takes a call in any table by it;
- a value that the deciding role does not hold in the callee (a port of the callee that only the other role holds) has no form to read, and no hypothesis is about it.
- a theorem about every judgment with fees (a converse, which walks a hypothesis with `walk … at h`) states that the judgment reads no peer of an effect, `(blind : ∀ ρ : Role → Role, Blind ρ (.charged allowed pays))`; the walk takes it from the hypotheses. For the judgment of a goal, and for the judgments on every and on some permitted reply (`.every (Permitted M)`, `.possible (Permitted M)`), the library proves it, and a text writes nothing. Under a judgment for which nothing says so, the walk stops at the application and says which judgment it is.

For a draw of a position in the standard model, `prEvent_drawPosition_eq_le n v` bounds the probability that a position of `index<n + 1>` is `v` by one in `n + 1` (so `7` for `index<8>`), stated with `toProbability`; `simpa using` puts it in the form of `weight`.

**A loop** is taken by an invariant, a function of the iteration number, of each carried value, of what was collected so far and of what the judgment carries (the budget):

```lean
walk_loop fun i (hit : Bool) budget => hit = false ∧ ((3 - i : ℕ) : ℚ≥0) * (1 / 8) ≤ budget
case first => …   -- the invariant before the first iteration
case step => …    -- the body at any iteration: `i`, `hit`, `budget`, `early_i : i < 3`, `invariant_i`
case after => …   -- the rest, from `invariant_i` after the last
```

**A call of a function** by a role is taken by a theorem of what the function computes: `walk_law apply_law G b r B w hb hw`. The value is what the law says; a hole (`_`) for an operand is the operand of the call. The law of a function is itself proved by walking the function (`refine done_of_judged ?_` or `functionResult_of_judged ?_`, then `walk` and `walk_loop`).

**A read of a sequence** is no case where the context decides it: a hypothesis that states the read, the entry of the list of a function at a position below its size (`List.getElem?_ofFn_of_lt`; a theorem of the text's own with the label `@[walk_read]`, as `rows_at` of Freivalds' check), or the length of the list and a bound of the position (`length : xs.length = 8` with `early_i : i < 8`). A read that nothing decides is a fork (`walk as ⟨entry, found⟩`).

**At the end** the operations of a model are read as its library says: over the arithmetic model a goal is stated with `+`, `*`, `List.sum` and numerals, and `ring` proves an equation of the field. A text that ends a step with the mathematics and `ring` is accepted unchanged when the source computes the same value another way.

**The witness** gives an input on which the relation returns false, over a model at which the hypotheses hold:

```lean
theorem either_witnessed : eitherWitnessed :=
  either_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial (either_relation _ false)
```

## Controls

A control is a module that Lean must refuse: the subject with its source or its text altered. It names the theorems that are then left unproved and the texts of the places at which the module is refused; with `only`, it is refused at those places and at no other.

```lean
{ title := "the charges exchanged", name := "CapControl", subject := exchanged, text := template,
  unproved := ["either_judged", "either_installed", "either_sound", "either_result"],
  places := ["the fee is not within the cap that the table gives the draw `site_y`\n  1 / 4 ≤ 1 / 8"],
  only := true }
```

A check does not rest on Lean's acceptance of the proof module. Every module of a check is elaborated in a sandbox (`bwrap`, which the host must have: the module can write only its own folder and can make no socket, so that it cannot ask a process outside to act for it; the filter of system calls knows x86-64 and 64-bit ARM). `check` and `startModule` compile each accepted module to an object there and have it read outside the file: the kernel replays its declarations, and its published theorems are compared with the module that the generator writes without the text and without the text's imports (`Module.reference`). A text that turns the kernel's check off is accepted by Lean and refused there; `refusedOutside` states such a control (the check of `Either` has one). The object that is read is what the run of Lean on the text left in the module's folder, and the program that reads it runs in the sandbox too. A module that a check starts itself goes through `startModule`, not `startLakeLean`, which is for controls and for modules that publish nothing.

A control of a charge is a source: no caller gives a statement its table. A text is altered with `replaceOnce`, which fails when the place that it alters is gone. Where two proofs of one module meet the same refusal, `occurrences` says how often its text occurs, since a text twice among the places says only that it occurs. A control is worth what it would catch: run the check once with the control given the unaltered subject, and see that the check fails ("Lean accepted a control that must be refused").

## What a text cannot do yet

A case analysis on a variant and an attempt are computed as one instruction: a walk does not go into them, and a walk that has to wait on the value that a case analysis on a variant takes apart (a `match` on a reply) is refused there. A protocol that is applied is walked, and nothing is yet stated of it: a text walks the body of the callee at each application, and a theorem of the callee that a caller could use once is not generated. A step that begins an instruction and fails says the number of the instruction's key in the stored program and what the instruction is; a step on what is left of an instruction after an effect or a fork names none. A goal whose clause is a `reduces`, and a knowledge goal, get no statement from this generator.
