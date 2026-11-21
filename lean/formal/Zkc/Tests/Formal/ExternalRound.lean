import Zkc.Tools.Formal.SingleRoundGoal
import Zkc.Tests.Formal.SourceProtocolRoots
import Zkc.Frontend.Written.Statement
import Zkc.Formal.Written.CoefficientPolynomial

namespace Zkc.Tests.Formal.ExternalRound
open Zkc.Core Zkc.Frontend Zkc.Frontend.Written Zkc.Tools.Formal
open Zkc.Formal.Interactive.Sumcheck ReductionRound Zkc.Formal.Written.SumcheckRows

private def endpointLine : LineExpression := ⟨.first,.second⟩

private def replaceOne (text old newText : String) : IO String := do
  unless (text.splitOn old).length == 2 do throw (IO.userError s!"expected one occurrence of {old}")
  return text.replace old newText

private def firstCall := "    first <- Reduce<Pairs, rounds = n>(values, [], claim, spec p = extension(values))\n    guard @V first.value == evaluate(values, first.point)\n"

/-- Compile the written example with the selected round encodings and source controls. -/
private def client (root : System.FilePath) (n : Nat) (order : List Bool)
    (edit : Option (String × String) := none) (permuted prefixPoint : Bool := false)
    (libraryEdit : Option (String × String × String) := none)
    (rootEdit : Option (String × String) := none) : IO AdmittedRoot := do
  let path := root / "examples/mixed_rounds.zkc"
  let mut text ← replaceOne (← IO.FS.readFile path) "Checked = Client<2>" s!"Checked = Client<{n}>"
  let impl (coeff : Bool) := if coeff then "Coefficients" else "Pairs"
  match order with
  | [second] =>
    text ← replaceOne text firstCall ""
    text ← replaceOne text "second <- Reduce<Coefficients," s!"second <- Reduce<{impl second},"
  | [first,second] =>
    text ← replaceOne text "first <- Reduce<Pairs," s!"first <- Reduce<{impl first},"
    text ← replaceOne text "second <- Reduce<Coefficients," s!"second <- Reduce<{impl second},"
  | _ => throw (IO.userError "expected one or two applications")
  if permuted then text ← replaceOne text "Client<n: nat> roles(P, V)" "Client<n: nat> roles(V, P)"
  if prefixPoint then
    text ← replaceOne text "second <- Reduce" "full = values ++ values\n    second <- Reduce"
    text ← replaceOne text "(values, [], claim, spec p = extension(values))" "(values, [claim], claim, spec p = extension(full))"
    text ← replaceOne text "evaluate(values, second.point)" "evaluate(full, second.point)"
  if let some (old,replacement) := rootEdit then text ← replaceOne text old replacement
  let entry : SourceInput := ⟨path.toString,Syntax.parseString path.toString text⟩
  let loader (parts : Array String) : IO (Option SourceInput) := do
    if let some (old, replacement) := edit then
      if parts == #["rounds","coefficients"] then
        return some (← SourceProtocolRoots.replaceOnce (root / "examples/support/rounds/coefficients.zkc") old replacement)
    if let some (file,old,replacement) := libraryEdit then
      if parts.back? == some file then
        let base := if file == "sumcheck" then root / "examples" else root / "libraries/zkc"
        return some (← SourceProtocolRoots.replaceOnce (base / (file ++ ".zkc")) old replacement)
    SourcePairReadback.loadModule root .original parts
  IO.ofExcept (admitSoundnessGoal (← assemble #[entry] loader) "sound")

/-- Read the site and operands from the actual application. Changing either rejects the witness. -/
private def atCall (c : AdmittedRoot) (red site : Key) (args : List Name) (before n prefixSize observer : Nat) (roles : List Role)
    (coeff : Bool) : Except String Unit := do
  let p := c.evidence.admitted.program
  let [⟨_,root⟩] := Member.withKey ProtocolHeader.key ⟨c.id⟩ p.headers.protocols | throw "missing root"
  let rows := sourceRows c.emission.bindings
  let t := rows.scalarTy
  let some call := mappedReduction (p := p) root red site (TableHalves.table t n) t (TableHalves.table t 0) prefixSize n
      (sourceEvents c.emission.bindings) observer roles args (List.replicate before .next) | throw "application"
  if coeff then
    let _ ← installRound (c := c) call Coefficients.expression (Coefficients.companion rows)
  else
    let _ ← installRound (c := c) call endpointLine (rows.endpointCompanion rows.evaluationReadback [rows.affineReadback])

private def check (c : AdmittedRoot) (n : Nat) (order : List Bool) (expected : List (Option String))
    (roles : List Role := [0,1]) (prefixSize : Nat := 0) : IO Unit := do
  let claims ← IO.ofExcept (goalClaims c ["sound"])
  let [goal] := claims.goals | throw (IO.userError "missing goal")
  let some rootUse := goal.caps.uses.getLast? | throw (IO.userError "missing root caps")
  let some (.protocol _ _ _ _ (.mk _ steps _)) := c.emission.named.definitions.find? (·.key.number == c.id)
    | throw (IO.userError "missing emitted root")
  let calls := steps.zipIdx.filterMap fun (step,i) => match step with
    | .op site _ (.apply red roster) args => some (site,red,roster,args,i)
    | _ => none
  unless calls.length == order.length && rootUse.calls.length == order.length &&
      goal.caps.ratio == (order.length * n : Nat) / (Zkc.Vocabulary.Field.bls12381Fr.order : Rat) do
    throw (IO.userError s!"unexpected applications or goal budget {goal.caps.ratio}")
  for ((((site,red,roster,args,i),cap),coeff),failure) in calls.zip rootUse.calls |>.zip order |>.zip expected do
    let some child := goal.caps.uses[cap.callee]? | throw (IO.userError "missing cap use")
    unless roster == roles && cap.key == site && cap.count == 1 && child.definition == red do throw (IO.userError "wrong cap edge")
    let test := atCall c red site args i n prefixSize claims.verifier roles
    match test coeff, failure with
    | .ok (), none =>
      let refuses (test : Except String Unit) (description : String) := do
        if test.isOk then throw (IO.userError s!"accepted {description} at {site.number}")
      refuses (atCall c red site args i n prefixSize claims.prover roles coeff) "the prover as verifier"
      refuses (test !coeff) "the other representation"
      refuses (atCall c red site args.reverse i n prefixSize claims.verifier roles coeff) "reversed operands"
      refuses (atCall c red ⟨site.number + 1⟩ args i n prefixSize claims.verifier roles coeff) "a different site"
      for (_,sibling,_,_,_) in calls do
        if sibling != red then
          refuses (atCall c sibling site args i n prefixSize claims.verifier roles coeff) "a sibling callee"
    | .error why, some wanted =>
      unless why.contains wanted do throw (IO.userError s!"expected {wanted}, got {why}")
    | .error why, none => throw (IO.userError s!"unexpected installation refusal at {site.number}: {why}")
    | .ok (), some wanted => throw (IO.userError s!"expected refusal for {wanted}")
  IO.println s!"rounds={n}, encodings={order}, uses={goal.caps.uses.length}, budget={goal.caps.ratio}"

def run (root : System.FilePath) : IO Unit := do
  for order in [[false,true],[true,false],[true,true],[false,false]] do
    check (← client root 2 order) 2 order [none,none]
  for n in [0,1,4,10] do
    let c ← client root n [true]
    check c n [true] [none]
    let rows := sourceRows c.emission.bindings
    let g ← IO.ofExcept (singleRoundGoal c n "sound" "challenge" Coefficients.expression (Coefficients.companion rows))
    if n > 0 then
      let elsewhere := applicationCharges ⟨g.checked.keys.site.number + 1⟩ g.checked.issued.charge
      if elsewhere == g.goal.caps.sites then throw (IO.userError "the same fees paid at a different application matched")
    unless g.checked.issued.charge.numerator == 1 && g.checked.issued.charge.denominator == Zkc.Vocabulary.Field.bls12381Fr.order do
      throw (IO.userError "expected the exact degree-one fee")
    unless n == 0 || !(chargeSumcheck c n "challenge").isOk do throw (IO.userError "endpoint evidence certified coefficients")
  for change in [("second.value ==", "claim =="), ("second.value ==", "second.value !=")] do
    let c ← client root 2 [true] (rootEdit := some change)
    let rows := sourceRows c.emission.bindings
    match singleRoundGoal c 2 "sound" "challenge" Coefficients.expression (Coefficients.companion rows) with
    | .ok _ => throw (IO.userError "an altered final guard acquired the original bound")
    | .error why => unless why.contains "uncertified Sumcheck verifier" do throw (IO.userError why)
  check (← client root 2 [true] none true true) 2 [true] [none] [1,0] 1
  for edit in [("sumcheck", "value(polynomial(m), r)", "value(polynomial(m), 1)"),
      ("polynomial", "external(\"Zkc.Polynomial.line\")", "external(\"Other.line\")")] do
    check (← client root 2 [true] none false false (some edit)) 2 [true] [some "typed verifier laws"]
  let evaluator := "def evaluate(m, r): m.0 + r * m.1"
  for (edit,why) in [(some (evaluator,"def evaluate(m, r): m.0"),"installed boundary or evaluation"),
      (some ("line(m.0, m.0 + m.1)", "line(m.0, m.1)"),"source polynomial")] do
    check (← client root 2 [false,true] edit) 2 [false,true] [none,some why]
  let original := "pub module Coefficients: Round:"
  for good in [true,false] do
    let value := if good then "m.0 + r * m.1" else "m.1 + r * m.0"
    let helper := s!"def helper(m: (F, F), r: F) -> F: {value}\n\n"
    let path := root / "examples/support/rounds/coefficients.zkc"
    let source ← IO.FS.readFile path
    let wrapper ← replaceOne (← replaceOne source original (helper ++ original)) evaluator "def evaluate(m, r): helper(m, r)"
    let failure := if good then none else some "installed boundary or evaluation"
    check (← client root 2 [true] (some (source,wrapper))) 2 [true] [failure]

end Zkc.Tests.Formal.ExternalRound
