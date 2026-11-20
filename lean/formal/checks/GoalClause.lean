import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Tests.Frontend.SyntaxHarness

/-!
The clause that a written soundness goal reads.

What the selector returns is compared with what the source of each fixture says, read here by
name: the kind of the clause, its label, its deciding role, the relation it applies and the
ports at the statement and at the witness, in the order of the relation's parameters. A
selector that returned the right label with the wrong relation, or the operands in the order
written, is refused by these expectations.
-/

open Zkc.Frontend Zkc.Frontend.Written

private def assemblyOf (src : String) : Assembly :=
  Id.run <| assemble #[⟨"claim.zkc", Syntax.parseString "claim.zkc" src⟩] fun _ => pure none

/-- The source with its one occurrence of `before` replaced. -/
private def edit (src before after : String) : IO String := do
  unless (src.splitOn before).length == 2 do
    throw (IO.userError s!"expected one occurrence of {before}")
  return src.replace before after

/-- What a reader of a selected clause sees, by the names of the source. -/
private structure Seen where
  kind : String
  label : Option String
  role : String
  relation : String
  statement : List String
  witness : List String
  deriving BEq, Repr

private def seen (c : AdmittedRoot) (goal : String) : Except String Seen := do
  let clause ← goalClause c goal
  let some key := c.state.results.key? c.id | throw "missing the root"
  let some {content := .protocol head .., ..} := c.state.env.modules.lowered? key.declaration
    | throw "missing the protocol"
  let some application := clause.application | throw "the clause applies no relation"
  let port (operand : Lowered.Expr) : Except String String := match operand with
    | .local _ id => match head.ports.find? (·.binder.id == id) with
      | some found => pure found.binder.name
      | none => throw "an operand is no port"
    | _ => throw "an operand is no name"
  return {
    kind := if clause.kind == .proves then "proves" else "reduces"
    label := clause.label
    role := (clause.role.bind (head.roster[·]?)).getD "?"
    relation := c.state.program.nameOf application.relation
    statement := (← application.statement.mapM port).toList
    witness := (← application.witness.mapM port).toList }

private def expect (title : String) (c : AdmittedRoot) (goal : String) (wanted : Seen) : IO Unit := do
  let found ← IO.ofExcept (seen c goal)
  unless found == wanted do
    throw (IO.userError s!"{title}: the goal reads {repr found}, the source says {repr wanted}")

private def refused {α} (title : String) (attempt : Except String α) (rule why : String) : IO Unit := do
  let .error message := attempt | throw (IO.userError s!"{title}: expected a refusal by {rule}")
  unless message.contains rule && message.contains why do
    throw (IO.userError s!"{title}: expected {rule} ({why}), got {message}")

#eval show IO Unit from do
  let blocks := Zkc.Tests.Frontend.readBlocks (← IO.FS.readFile "../../language/conformance/layer-b.txt")
  let fixture (id : String) : IO String := match (blocks.find? (·.id == id)).bind (·.files[0]?) with
    | some text => pure text
    | none => throw (IO.userError s!"missing the reference case {id}")
  let admit (text goal : String) := admitSoundnessGoal (assemblyOf text) goal

  -- A promise pair: each goal reads the clause it names, whatever the order of the clauses.
  let pair ← fixture "N-GL3b"
  let near : Seen := ⟨"proves", some "near", "V", "Near", ["x"], ["w"]⟩
  let exact : Seen := ⟨"proves", some "exact", "V", "Exact", ["x"], ["w"]⟩
  let reversed ← edit pair "    proves exact: Exact(x; w)\n    proves near: Near(x; w)\n"
    "    proves near: Near(x; w)\n    proves exact: Exact(x; w)\n"
  for (title, text) in [("promise pair", pair), ("promise pair, clauses reversed", reversed)] do
    expect title (← IO.ofExcept (admit text "sound")) "sound" near
    let other ← edit text "soundness(S, clause = near)" "soundness(S, clause = exact)"
    expect title (← IO.ofExcept (admit other "sound")) "sound" exact

  -- The operands are in the order of the relation's parameters, not in the order written.
  let wide ← edit pair "relation Near(x: F; w: F):" "relation Near(x: F, y: F; w: F):"
  let wide ← edit wide "roles(P, V)(x: F @(P, V)," "roles(P, V)(y: F @(P, V), x: F @(P, V),"
  for (written, statement) in [("Near(y = y, x = x; w)", ["x", "y"]), ("Near(y = x, x = y; w)", ["y", "x"])] do
    let text ← edit wide "proves near: Near(x; w)" s!"proves near: {written}"
    expect s!"named operands {written}" (← IO.ofExcept (admit text "sound")) "sound"
      ⟨"proves", some "near", "V", "Near", statement, ["w"]⟩

  -- One deciding clause: the goal reads it, named or not.
  let count ← fixture "N-GL2a"
  let single : Seen := ⟨"proves", none, "V", "NearZero", ["xs"], []⟩
  expect "one clause" (← IO.ofExcept (admit count "loose")) "loose" single
  let labelled ← edit count "proves @V NearZero(xs)" "proves @V within: NearZero(xs)"
  expect "one clause, labelled, not named" (← IO.ofExcept (admit labelled "loose")) "loose"
    { single with label := some "within" }
  let named ← edit labelled "soundness(Checked, spec e = 4)" "soundness(Checked, spec e = 4, clause = within)"
  expect "one clause, named" (← IO.ofExcept (admit named "loose")) "loose" { single with label := some "within" }

  -- A `reduces` clause: the goal reads its source.
  let reducing ← edit count "roles(P, V)(xs: [F; n] @(P, V)):" "roles(P, V)(xs: [F; n] @(P, V)) -> ys: [F; n] @(P, V):"
  let reducing ← edit reducing "        guard @V xs[z] == 0\n" "        guard @V xs[z] == 0\n        return xs\n"
  let reducing ← edit reducing "proves @V NearZero(xs)" "reduces @V NearZero(xs) to NearZero(ys)"
  expect "a reduces clause" (← IO.ofExcept (admit reducing "loose")) "loose" { single with kind := "reduces" }

  -- Two deciding clauses and no name: the claim has no clause, and the charge at the site is
  -- read as before, since reading a charge states no claim.
  let relation := "    relation NearZero(xs: [F; n]): (∑ i ∈ 0..n, if xs[i] == 0 then 0 else 1) <= e\n"
  let both ← edit count relation (relation ++ "    relation Below(xs: [F; n]): (∑ i ∈ 0..n, if xs[i] == 0 then 0 else 1) < e\n")
  let both ← edit both "        proves @V NearZero(xs)\n" "        proves @V within: NearZero(xs)\n        proves @V below: Below(xs)\n"
  let ambiguous ← IO.ofExcept (admit both "loose")
  refused "two clauses, none named" (goalClause ambiguous "loose") "GL3" "several deciding clauses"
  let charge ← IO.ofExcept (goalDrawCharge ambiguous "loose" [] "z")
  unless (charge.numerator, charge.denominator) == (3, 8) do throw (IO.userError "the charge at the site changed")
  for (label, relationName) in [("within", "NearZero"), ("below", "Below")] do
    let text ← edit both "soundness(Checked, spec e = 4)" s!"soundness(Checked, spec e = 4, clause = {label})"
    expect s!"two clauses, {label} named" (← IO.ofExcept (admit text "loose")) "loose"
      ⟨"proves", some label, "V", relationName, ["xs"], []⟩

  -- A name that no clause has, and the name of a clause of another kind, are refused where
  -- the goal is read.
  let absent ← edit both "soundness(Checked, spec e = 4)" "soundness(Checked, spec e = 4, clause = absent)"
  refused "a name that no clause has" (admit absent "loose") "GL3" "no clause labelled `absent`"
  let other ← edit labelled "        charge sites.z" "        ensures after: true\n        charge sites.z"
  let other ← edit other "soundness(Checked, spec e = 4)" "soundness(Checked, spec e = 4, clause = after)"
  refused "the name of a clause of another kind" (admit other "loose") "GL3" "`after` is a `ensures` clause"

  -- The deciding role of the clause is the verifier of the scheme.
  let prover ← edit count "proves @V NearZero(xs)" "proves @P NearZero(xs)"
  refused "decided by the prover" (goalClause (← IO.ofExcept (admit prover "loose")) "loose") "GL3"
    "the deciding role of the clause is the verifier"

  -- A caller without a contract has no clause to read, and reads the charges of its callees.
  let wrapper := "protocol Caller<spec tolerance: nat> roles(P, V)(xs: [F; 8] @(P, V)):\n" ++
    "    first <- Count<8, spec e = tolerance>(xs)\n" ++
    "    second <- Count<8, spec e = 1>(xs)\n"
  let wrapped ← edit count "scheme Checked = Count<8>:" (wrapper ++ "scheme Checked = Caller:")
  let wrapped := wrapped.replace "Checked, spec e" "Checked, spec tolerance"
  let caller ← IO.ofExcept (admit wrapped "loose")
  refused "a caller without a contract" (goalClause caller "loose") "GL3" "has no `proves` or `reduces` clause"
  let #[origin] := caller.emission.origins.filter (·.definition.number == caller.id)
    | throw (IO.userError "missing the caller's origin")
  let #[first, second] := origin.specification | throw (IO.userError "expected two applications")
  for (site, wanted) in [(first.instruction, (3, 8)), (second.instruction, (3, 4))] do
    let charge ← IO.ofExcept (goalDrawCharge caller "loose" [site] "z")
    unless (charge.numerator, charge.denominator) == wanted do
      throw (IO.userError "the charge of a callee under the caller's proof arguments changed")
  IO.println "A soundness goal reads the clause it names or the only one, with its relation and its operands in order."
