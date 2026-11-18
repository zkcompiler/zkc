import Zkc.Tests.Formal.Reuse.Controls
import Zkc.Tests.Formal.SourceHonestSumcheck

open Zkc.Core Zkc.Frontend Zkc.Tests.Formal

#eval show IO Unit from do
  let root := (← IO.currentDir) / ".." / ".."
  Zkc.Tests.Formal.SourceProtocolRoots.checkAll root
  Zkc.Tests.Formal.Reuse.run root 0
  let cases : List (Nat × SourcePairReadback.Variant × Option (String × String) × String) := [
    (0,.original,none,"empty reduction and terminal guard"),
    (1,.original,none,"one message and restriction"),
    (10,.original,none,"approved Pairs"),
    (10,.affine,none,"affine evaluation"),
    (10,.original,some ("(sum(table[0..2^v]), sum(table[2^v..2^(v + 1)]))",
      "(sum(table[2^v..2^(v + 1)]), sum(table[0..2^v]))"),"swapped honest endpoints"),
    (10,.original,some ("def bind(state, r): fix_first(state, r)",
      "def bind(state, r): fix_first(state, r + r)"),"wrong private restriction"),
    (10,.original,some ("guard @V reduced.value == evaluate(values, reduced.point)",
      "guard @V claim == evaluate(values, reduced.point)"),"stale terminal claim")]
  for (n,variant,edit,label) in cases do
    let path := root / "examples/sumcheck_example.zkc"
    let entry ← if n == 10 then SourcePairReadback.source .original path
      else SourceProtocolRoots.replaceOnce path "Proof = Sumcheck<10>" s!"Proof = Sumcheck<{n}>"
    let load (parts : Array String) : IO (Option SourceInput) := do
      if let some (before,after) := edit then
        if parts.back? == some "sumcheck" then
          return some (← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck.zkc") before after)
      SourcePairReadback.loadModule root variant parts
    let c ← SourceProtocolRoots.admitRoot entry load
    let e := c.emission
    let key : Key := ⟨c.id⟩
    let some (red,_) := SourceHonestSumcheck.callKeys e key | throw (IO.userError s!"{label}: caller keys")
    let some origin := e.origins.find? (·.definition == key) | throw (IO.userError "missing caller origin")
    let #[a] := origin.specification | throw (IO.userError "ambiguous specification")
    let #[("p",.apply _ (.instance target) _)] := a.arguments | throw (IO.userError "missing extension")
    let name (id : Nat) := c.state.table.entries[id]?.map fun v => c.state.program.nameOf v.key.declaration
    let some caller := c.state.results.checked? c.id | throw (IO.userError "missing checked caller")
    let .protocol body := caller.definition.body | throw (IO.userError "expected a protocol")
    let some values := body.ports.find? (·.binder.name == "values") | throw (IO.userError "missing table port")
    unless name red.number == some "Reduce" && name target == some "extension" &&
        e.matchesLocalApplication c.state key a.instruction red [0,1] "p" ⟨target,[.binder values.binder.id]⟩ do
      throw (IO.userError s!"{label}: source association")
    let found := (SourceHonestSumcheck.certificate e c.evidence key n variant).isSome
    unless found == edit.isNone do throw (IO.userError s!"{label}: joint certificate={found}")
    if label ∈ ["swapped honest endpoints","wrong private restriction"] then
      unless SourceHonestSumcheck.openVerifier e c.evidence key n == some true do
        throw (IO.userError s!"{label}: expected open verifier certificate")
    IO.println s!"{label}: rounds={n}, admitted definitions={e.named.definitions.length}, certificate={found}"
