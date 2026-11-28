import Lean

/-! A check's reader of a built challenge: the challenge module declares exactly the theorems that
the check lists, each with the type that the check spells (elaborated here, compared by
`Expr.equal`, which compares the constants and the binder names of the two terms). -/

open Lean Elab Command Term

namespace ZkcFormalTests.ChallengeReader

/-- A row: a theorem of the challenge and its statement as the check spells it. -/
syntax challengeRow := "|" ident ":=" term

/-- `#challenge_is M rows`: the theorems that the module `M` declares are the rows' names, and
the type of each is the row's term, elaborated here. -/
elab "#challenge_is " m:ident rows:challengeRow* : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "the module {m.getId} is not imported"
  let declared := (env.header.moduleData[idx.toNat]!.constNames.filter fun n =>
    match env.find? n with
    | some (.thmInfo _) => true
    | _ => false).toList
  let mut unchecked := declared
  for row in rows do
    let `(challengeRow| | $n:ident := $t:term) := row | throwUnsupportedSyntax
    unless unchecked.contains n.getId do
      throwErrorAt n "{n.getId}: not a theorem of {m.getId}, or listed twice"
    unchecked := unchecked.erase n.getId
    let some (.thmInfo info) := env.find? n.getId | throwErrorAt n "{n.getId} is no theorem"
    let expected ← liftTermElabM do
      let e ← elabTerm t (some (.sort .zero))
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    unless Expr.equal info.type expected do
      throwErrorAt n m!"{n.getId}: the challenge states{indentExpr info.type}\nthe check spells{indentExpr expected}"
  unless unchecked.isEmpty do throwError "{m.getId} declares more theorems: {unchecked}"
  logInfo m!"{m.getId}: {declared.length} theorems, each the statement that the check spells"

end ZkcFormalTests.ChallengeReader
