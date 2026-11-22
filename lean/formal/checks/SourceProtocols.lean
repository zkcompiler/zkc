import ZkcFormalTests.Reuse.Controls
import ZkcFormalTests.SourceHonestSumcheck

open Zkc.Core Zkc.Frontend ZkcFormalTests

#eval show IO Unit from do
  let root := (← IO.currentDir) / ".." / ".."
  ZkcFormalTests.SourceProtocolRoots.checkAll root
  ZkcFormalTests.Reuse.run root 0
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
    let found := (SourceHonestSumcheck.atSource c n variant).isSome
    unless found == edit.isNone do throw (IO.userError s!"{label}: joint certificate={found}")
    if label ∈ ["swapped honest endpoints","wrong private restriction"] then
      unless SourceHonestSumcheck.openVerifier e c.evidence key n == some true do
        throw (IO.userError s!"{label}: expected open verifier certificate")
    IO.println s!"{label}: rounds={n}, admitted definitions={e.named.definitions.length}, certificate={found}"

  let entry ← SourcePairReadback.source .original (root / "examples/sumcheck_example.zkc")
  let changed ← SourceProtocolRoots.admitRoot entry fun parts => do
    if parts.back? == some "polynomial" then
      return some (← SourceProtocolRoots.replaceOnce (root / "libraries/zkc/polynomial.zkc")
        "external(\"Zkc.Polynomial.extension\")" "external(\"Example.otherExtension\")")
    SourcePairReadback.loadModule root .original parts
  unless (SourceHonestSumcheck.certificate changed.emission changed.evidence ⟨changed.id⟩ 10 .original).isSome &&
      (SourceHonestSumcheck.atSource changed 10 .original).isNone do
    throw (IO.userError "expected joint completeness with a different source binding")
  IO.println "Alternative extension binding: joint completeness retained, source association refused"
