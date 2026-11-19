import Zkc.Tools.Formal.DrawCharge
import Zkc.Tools.Formal.Policy
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tests.Formal.Reuse.Automatic

open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Written.RoundCharge

-- Retaining the original emission equality rules out a mixed public certificate.
example (source _other : Written.AdmittedRoot) : Written.AdmittedRoot := by
  fail_if_success exact {source with emission := _other.emission, evidence := _other.evidence}
  exact source

private def sum (root : System.FilePath) (rounds : Nat) (edit : Option (String × String) := none) :
    IO Written.AdmittedRoot := do
  let file := root / "examples/sumcheck_example.zkc"
  let entry ← SourceProtocolRoots.replaceOnce file "Proof = Sumcheck<10>" s!"Proof = Sumcheck<{rounds}>"
  SourceProtocolRoots.admitRoot entry fun parts => do
    if let some (from_, to_) := edit then
      if parts.back? == some "sumcheck" then
        return some (← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck.zkc") from_ to_)
    SourcePairReadback.loadModule root .original parts

#eval show IO Unit from do
  let root := (← IO.currentDir) / "../.."
  for n in [0,1,10] do
    let c ← sum root n
    let approved ← IO.ofExcept (chargeSumcheck c n "challenge")
    unless c.emission.bindings.rows.isEmpty do throw (IO.userError "standard arithmetic model does not cover these rows")
    let charge := approved.issued.charge
    unless charge.draws.length == n do throw (IO.userError "incomplete collection of charged draws")
    if let a :: b :: rest := charge.draws then
      for wrong in [{charge with draws := a :: a :: rest}, {charge with draws := b :: a :: rest},
          {charge with owner := ⟨c.id⟩}] do
        if decide (Matches wrong approved.verifier.linked 1 charge.denominator) then
          throw (IO.userError "accepted a different callee, reused draw or permuted draw")
    IO.println s!"Sumcheck accepted the written charge at {n} positions, degree {charge.numerator}, order {charge.denominator}"
  let original := "charge sites.challenge <= R::Degree / F::Order"
  for loose in ["2 / F::Order", "1 / 5", "2 / (2 * F::Order)"] do
    let c ← sum root 1 (some (original, "charge sites.challenge <= " ++ loose))
    let _ ← IO.ofExcept (chargeSumcheck c 1 "challenge")
  for (after,expected) in [
      ("charge sites.challenge <= 0 / F::Order","too small"),
      ("charge sites.challenge <= 1 / (2 * F::Order)","too small"),
      ("charge sites.challenge <= R::Degree / 0","too small"),
      ("charge sites.round <= R::Degree / F::Order","expected one charge")] do
    let c ← sum root 1 (some (original,after))
    let .error why := chargeSumcheck c 1 "challenge" | throw (IO.userError s!"accepted {after}")
    unless why.contains expected do throw (IO.userError why)
  let empty ← sum root 0 (some (original, "charge sites.challenge <= 0"))
  let emptyCharge ← IO.ofExcept (chargeSumcheck empty 0 "challenge")
  unless emptyCharge.issued.charge.draws.isEmpty do throw (IO.userError "zero-trip bound includes a draw")
  for expr in ["(R::Degree / F::Order) + 0", "1 / (2 * F::Order) + 1 / (2 * F::Order)",
      "(1 - 1 / 2)^2", "2^-3", "1 + (3 / 0)"] do
    let c ← sum root 1 (some (original, "charge sites.challenge <= " ++ expr))
    let _ ← IO.ofExcept (chargeSumcheck c 1 "challenge")
  for (expr,expected) in [("2^(1 - 3)", (1 / 4 : Rat)), ("(-2)^(-3) + 1", 7 / 8), ("3 / 0 + 1", 1)] do
    let c ← sum root 1 (some (original, "charge sites.challenge <= " ++ expr))
    let approved ← IO.ofExcept (chargeSumcheck c 1 "challenge")
    let fee := approved.issued.charge
    unless Rat.divInt fee.numerator fee.denominator == expected do throw (IO.userError s!"wrong exact amount for {expr}")
  for (expr,reason) in [("-1", "nonnegative"), ("2^(1/2)", "integer"), ("3 % 2", "remainder")] do
    let c ← sum root 1 (some (original, "charge sites.challenge <= " ++ expr))
    let .error why := chargeSumcheck c 1 "challenge" | throw (IO.userError s!"accepted {expr}")
    unless why.contains reason do throw (IO.userError why)
  for (old, replacement) in [("proves @V Sum(values, claim)", "proves @V Sum(values, 0)"),
      ("proves @V Sum(values, claim)", "proves @P Sum(values, claim)"),
      ("claim == ∑ v ∈ values, v", "claim == ∑ v ∈ values, 0")] do
    let c ← sum root 2 (some (old,replacement))
    let .error why := chargeSumcheck c 2 "challenge" | throw (IO.userError "issued a different source property")
    unless why.contains "written sum relation" do throw (IO.userError why)
  let two ← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck_example.zkc") "Proof = Sumcheck<10>" "Proof = Sumcheck<2>"
  let changed (edit : String → String) := SourceProtocolRoots.admitRoot two fun parts => do
    if parts.back? != some "sumcheck" then return ← SourcePairReadback.loadModule root .original parts
    let path := root / "examples/sumcheck.zkc"
    return some ⟨path.toString, Syntax.parseString path.toString (edit (← IO.FS.readFile path))⟩
  let renamed ← changed fun source => (source.replace "relation Sum<" "relation PublicTotal<").replace
    "proves @V Sum(" "proves @V PublicTotal("
  let _ ← IO.ofExcept (chargeSumcheck renamed 2 "challenge")
  for (variant, expected) in [(SourcePairReadback.Variant.affine,true),(.reversed,false)] do
    let c ← SourceProtocolRoots.admitRoot two (SourcePairReadback.loadModule root variant)
    unless (chargeSumcheck c 2 "challenge").isOk == expected do throw (IO.userError "incorrect interpolation certificate")
  let mixed ← changed fun src =>
    ((((src.replace "def evaluate(m: Message" "def evaluate<depth: nat>(m: Message").replace
      "law at_point(m:" "law at_point<depth: nat>(m:").replace
      "evaluate(m, r) == value" "evaluate<depth = depth>(m, r) == value").replace
      "R::evaluate(round, challenge)" "R::evaluate<depth = rounds - i>(round, challenge)").replace
      "def evaluate(m, r): (1 - r) * m.0 + r * m.1"
      "def evaluate(m, r): if depth == 1 then m.0 + r * (m.1 - m.0) else (1 - r) * m.0 + r * m.1"
  let mixedCharge ← IO.ofExcept (chargeSumcheck mixed 2 "challenge")
  let rows := Zkc.Formal.Written.SumcheckRows.sourceRows mixed.emission.bindings
  let rounds := mixedCharge.verifier.linked
  for single in [rows.evaluationReadback, rows.affineReadback] do
    if (Zkc.Formal.Interactive.Sumcheck.ReductionRound.checkPairSequence rows rounds.entry.definitions
        (List.nodup_append.mp rounds.entry.distinct).1 single rounds.rounds).isSome then
      throw (IO.userError "one interpolation rule unexpectedly certified the mixed sequence")
  let actualKeys := mixedCharge.verifier.linked.rounds.instances.filterMap fun r =>
    match r.checked.members.evaluate.print with | .call key => some key | _ => none
  unless actualKeys.length == 2 && actualKeys.eraseDups.length == 2 do throw (IO.userError "expected two distinct round callees")
  let wrongExtension ← SourceProtocolRoots.admitRoot two fun parts => do
    if parts.back? == some "polynomial" then return some (← SourceProtocolRoots.replaceOnce
      (root / "libraries/zkc/polynomial.zkc") "Zkc.Polynomial.extension" "Example.otherExtension")
    SourcePairReadback.loadModule root .original parts
  if (chargeSumcheck wrongExtension 2 "challenge").isOk then throw (IO.userError "issued the wrong table extension")
  let reused ← changed fun src =>
    (src.replace "mut running = claim" "mut running = claim\n    mut last = claim").replace
      "running := R::evaluate(round, challenge)" "running := R::evaluate(round, last)\n        last := challenge"
  let .error "uncertified Sumcheck verifier" := chargeSumcheck reused 2 "challenge"
    | throw (IO.userError "accepted a verifier that ignores the current draw")
  -- A separate declaration with exactly the same executable body has no written charge.
  let other ← changed fun src =>
    let body := ((src.splitOn "pub protocol Reduce")[1]!).splitOn "spec for Reduce:"
    (src.replace "pub protocol Reduce" ("pub protocol AnotherReduce" ++ body[0]! ++ "pub protocol Reduce")).replace
      "reduced <- Reduce<Pairs" "reduced <- AnotherReduce<Pairs"
  let .error why := chargeSumcheck other 2 "challenge" | throw (IO.userError "issued another callee's charge")
  unless why.contains "expected one charge" do throw (IO.userError s!"callee switch failed before source binding: {why}")
  let entry ← SourcePairReadback.source .original (root / "examples/gkr_example.zkc")
  let c ← SourceProtocolRoots.admitRoot entry (SourcePairReadback.loadModule root .original)
  let some component := Reuse.Automatic.gkr c ⟨17⟩ ⟨11⟩ [15,16,9] ⟨28⟩
    | throw (IO.userError "missing GKR layer reduction")
  let summand : Emit.LocalApplication := ⟨34,[.binder 0,.binder 1,.bounded 4 6,.binder 4]⟩
  let actual := (← IO.ofExcept (chargeLayer (c := c) component.atCall summand "challenge")).issued
  if (chargeLayer (c := c) component.atCall {summand with operands := [.binder 1,.binder 0,.bounded 4 6,.binder 4]}
      "challenge").isOk then throw (IO.userError "accepted swapped source summand operands")
  unless actual.charge.draws.length == 4 do throw (IO.userError "wrong GKR reduction charge count")
  if (issueCharge c.state "challenge" component.atCall.linked 3 actual.charge.denominator).isOk then
    throw (IO.userError "the written degree-two charge covered degree three")
  let altered ← SourceProtocolRoots.admitRoot entry fun parts => do
    if parts.back? == some "layered" then
      return some (← SourceProtocolRoots.replaceOnce (root / "examples/support/circuits/layered.zkc")
        "circuit.gate_evaluate" "circuit.other_evaluate")
    SourcePairReadback.loadModule root .original parts
  let some (.error why) := Reuse.Automatic.withLayerCall altered ⟨17⟩ ⟨11⟩ [15,16,9] ⟨28⟩
      (fun {_} _ _ {_ _} call => some ((chargeLayer (c := altered) call summand "challenge").map fun _ => ()))
    | throw (IO.userError "expected the same located call to refuse the replacement gate")
  unless why.contains "uncertified gate member" do throw (IO.userError why)
  IO.println "GKR issued four degree-two charges at the verified layer call"


namespace RepeatedCoin
open Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess Zkc.Formal.Interactive OracleComp
open scoped ENNReal

private abbrev Coin : Sig := ⟨Unit, fun _ => Bool⟩

private def slots (reuse : Bool) : Slots Coin (Option Bool) where
  width _ _ := 1
  answer _ saved i :=
    let sampled := i.val == 0
    let reply := if reuse then saved.getD sampled else sampled
    (some reply, some reply)

private def agree : Process Coin Unit Bool :=
  .call () fun first => .call () fun second => .done (first == second)

private def yes (b : Bool) (_ : Option Bool) := b

example : prEvent (observed yes <$> run (service (slots true)) agree none) = 1 := by
  rw [finite_slots_probability, show (finite (slots true)).probability agree none yes = 1 by decide, embed_one]

example : prEvent (observed yes <$> run (service (slots false)) agree none) = (1/2 : ℝ≥0∞) := by
  rw [finite_slots_probability, show (finite (slots false)).probability agree none yes = slotWeight 1 by decide,
    embed_weight]
  norm_num

end RepeatedCoin

open Lean Zkc.Tools.Audit in
#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let artifacts ← zkcArtifacts (← searchPathRef.get)
  let env ← importModules #[{module := `Zkc.Tools.Formal.DrawCharge}, {module := `Zkc.Tools.Audit.Controls.Axiom}]
    {} (level := .private) (loadExts := false) (arts := artifacts)
  let authorized (names : Array Lean.Name) := do
    for name in names do
      unless (env.find? name).any (· matches .thmInfo _) do throw (IO.userError s!"missing theorem {name}")
    let (axioms,_,_) := dependencies env names
    IO.println s!"{names}: axioms {axioms}"
    return axioms.all Zkc.Tools.Formal.policy.axioms.contains
  unless ← authorized #[`Zkc.Tools.Formal.ChargedSumcheck.primeBound, `Zkc.Tools.Formal.ChargedLayer.bound] do
    throw (IO.userError "published charge theorem exceeds the formal axiom policy")
  let some control := env.constants.toList.findSome? (fun (n,info) =>
    if (privateToUserName n) == `Zkc.Tools.Audit.Controls.fromAxiom && info matches .thmInfo _ then some n else none)
    | throw (IO.userError "missing extra-axiom control")
  if ← authorized #[control] then throw (IO.userError "failed to reject an extra axiom")
