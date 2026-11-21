# Writing a subject of a written soundness goal

A subject is a source with a soundness goal, the text of its proofs, and a check that runs Lean on the two. This page says what each of the three is, what is generated around a text, and what a text writes. The four subjects of the repository are the examples: `lean/formal/checks/GuessCharge.lean`, `CountCharge.lean`, `FreivaldsCharge.lean` and `EitherCharge.lean`, each with its text in the file of the same name ending in `.lean.in`. [Status](status.md) says what the path supports and what it does not.

## The three parts

**The source** declares a protocol, the relation that its verifier decides, a contract with a `proves` clause and the charges of its draws, a scheme and a goal:

```
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

**The text** is a Lean file without a header. It proves, for each goal, the judgment that the generator states (`<goal>_judged : <goal>Judged`) and that the hypotheses of the claim are met at some input (`<goal>_witnessed : <goal>Witnessed`). It states nothing: every proposition is generated before the text.

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

Run it from `lean/formal` with `lake lean checks/EitherCharge.lean`. It is accepted when Lean accepts the module, every listed theorem rests on `propext`, `Classical.choice` and `Quot.sound` at most, and every control is refused as it says.

A `Reading` asserts the ports of the root, the clause that each goal reads, the inputs of the deployed header that the relation is applied to, the number of proof arguments, the roles of the scheme, and the class of models (`model`, the standard model unless said). A reading that is not what the check asserts is an error: the text is written against it.

## What stands before the text

The generator (`lean/compiler/Zkc/Frontend/Written/Statement.lean`) writes the printed package and, from what the frontend read, the names that a text uses. For a goal `either` of a root with the ports above:

| Name | What it is |
| --- | --- |
| `installed`, `rootMember`, `verifierRole`, `proverRole` | the admitted program, the root in it, the two roles |
| `eitherMember` | the function of the relation at the goal's value; a function that the root calls has `<function>Member` |
| `eitherCaps`, `either_budget` | the table of caps of the goal, and its budget as a number |
| `site_x`, `site_y` | each named draw of the root, under its name in the source, charged or not |
| `either_cap_x`, `either_cap_y` | the cap that the table gives each charged draw |
| `eitherJudged` | the judgment that the text proves |
| `either_witnessed_of` | the theorem that gives `eitherWitnessed` from an input on which the relation returns false |
| `eitherClaim`, `eitherGoal`, `eitherResult`, `eitherWitnessed` | the published propositions; their theorems are written after the text |

The class of models is read from the package: the standard model over any data (`D : StandardModel.Data F G`) where every coin is a position, and the arithmetic model over a field `F` with at least the order of the source's scalar field (a hypothesis `large`) where the package draws a scalar.

To see a generated module, keep the working directory of a check: replace `IO.FS.withTempDir fun work =>` by a function that passes a directory of yours, and read `<Name>.lean` there.

## What a text writes

The judgment is about the verifier's process: on inputs on which the relation returns false it is judged never to return, within the budget of the table, each fee within what the table allows the effect that pays it. A text walks the program to the places where it has something to say.

```lean
theorem either_judged : eitherJudged := by
  claim_intro
  obtain rfl : input_claim = false :=
    Option.some.inj ((either_relation D input_claim).symm.trans rejected)
  walk
  walk_free as sent
  walk as allowed
  walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = sent) as drawn differs
  case weight => simpa using prEvent_drawPosition_eq_le 3 sent
  case within => decide +kernel
  walk as hit
  exact differs (Nat.eq_of_beq_eq_true hit)
```

**`claim_intro`** introduces the binders of the judgment under the names that the generator gave them: what the model is built from (`D`, or `F` and `G`), `path`, each input as `input_<port>` with `valid_input_<port>`, a hypothesis of the model by its name, and `rejected`, that the relation returns false.

**`walk`** goes to the next effect, loop, call of a function by a role, or the end of the program. It goes into the arm of a choice and into a block as into a program. At the end, what is left is what the judgment asks there, stated in the inputs, the replies and the names of the text. `walk … at h` walks a hypothesis that judges a process.

**Nothing that an instruction binds has a name.** A value of a step shows in a goal under a name that a text cannot write (`value✝`). A text names what it speaks of:

- a reply, at its effect (`as sent`, `as drawn`);
- a fork, where a step waits on a value: `walk as h` names the hypothesis that says which form the value is, `walk as ⟨x, h⟩` also the parts of that form (the entry that a read found), and `walk as ⟨x, h⟩, g` the forks on the way in order. A side that holds as it stands (a guard that stops the run, where the judgment asks nothing of a stop) is closed; the walk goes on in every other. A name for which no fork is met is an error;
- the arguments of an invariant (below).

**At an effect** under the judgment with fees:

- `walk_free as v`: nothing is excluded and no fee is paid. The reply is `v`, and `permitted_v` says that it is permitted. A message got has no sampler and is met this way.
- `walk_pay fee excluding set as v kept`: a coin pays `fee` for the replies in `set`. It leaves `weight` (the sampler draws a reply of the set with probability at most the fee: the mathematics of the step), `within` (the fee is within the budget, unless a hypothesis says so as it stands) and `cap` (the fee is within the cap of the draw, unless the kernel decides it), and then the rest after a reply `v` with `kept : ¬ set v`. A fee over the cap that the module states is refused with the name of the site.

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

A control of a charge is a source: no caller gives a statement its table. A text is altered with `replaceOnce`, which fails when the place that it alters is gone. A control is worth what it would catch: state the place, and run the check once with the thing that the control guards switched off.

## What a text cannot do yet

A case analysis on a variant and an attempt are computed as one instruction: a walk does not go into them. A call of a protocol (an application) has no rule: a root that applies another protocol has a table of caps and no text. A goal whose clause is a `reduces`, and a knowledge goal, get no statement from this generator.
