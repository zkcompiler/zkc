import Zkc.Tools.Formal.DrawCharge
import Zkc.Tests.Formal.Reuse.Automatic

open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Written.RoundCharge

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
  let two ← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck_example.zkc") "Proof = Sumcheck<10>" "Proof = Sumcheck<2>"
  let changed (edit : String → String) := SourceProtocolRoots.admitRoot two fun parts => do
    if parts.back? != some "sumcheck" then return ← SourcePairReadback.loadModule root .original parts
    let path := root / "examples/sumcheck.zkc"
    return some ⟨path.toString, Syntax.parseString path.toString (edit (← IO.FS.readFile path))⟩
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

#print axioms Zkc.Formal.Written.RoundCharge.sumcheck
#print axioms Zkc.Formal.Written.RoundCharge.gate
#print axioms ChargedSumcheck.primeBound
