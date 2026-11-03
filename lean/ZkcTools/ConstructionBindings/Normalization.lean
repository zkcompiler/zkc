module

public import Zkc.Source.Structured.NormalForm.Normalize
public meta import ZkcTools.StructuredSource.Presentation.Syntax
public meta import ZkcTools.ConstructionBindings.Syntax
public meta import Lean.Elab.Tactic

public meta section

/-! Untrusted finite source normalization. Consumers must check the proposed
literal against the original normalizer with an ordinary kernel equation. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Normalization
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured NormalForm

private def phase (message : String) : TermElabM Unit := do
  if !(← getOptions).getBool `zkc.connection.trace false then return
  let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
  unless destination.isEmpty do
    IO.FS.withFile destination .append fun h => h.putStrLn message

/-- Compiled proposal using the existing normalizer and literal printer. This
produces source text, never an equation or a proof. Public visibility lets the
meta evaluator invoke it from an importing module. -/
def normalizationLiteral (signature : Signature) {inputs outputs : List Ty}
    (body : Region protocolDialect inputs outputs) (role roster : Nat)
    (pattern : InputPattern inputs) : Except String String := do
  let form ← NormalForm.normalize signature body role roster pattern
  return ZkcTools.StructuredSource.Presentation.formLiteral form

/-- Reduce the finite inputs, then run the normalizer in compiled meta code.
Reducing its whole call with `whnf` repeatedly expands intermediate symbolic
states. The proposed literal is checked against that unchanged call below.
Implicit data indices must also be reduced: a generated syntax constant can
be noncomputable even when its closed data has an executable literal. -/
unsafe def propose (cache : Syntax.Cache) (computation : Expr) : TermElabM Expr := withTransparency .default do
  let computation ← instantiateMVars computation
  unless computation.isAppOf ``NormalForm.normalize &&
      !computation.hasFVar && !computation.hasMVar do
    throwError "connection-normalization-not-closed"
  let mut arguments := computation.getAppArgs
  for index in [:arguments.size] do
    phase s!"normalization literal argument {index}/{arguments.size}: {arguments[index]!.getAppFn.constName?}"
    arguments := arguments.set! index (← withTransparency .all <|
      reduce arguments[index]! (explicitOnly := false) (skipTypes := false))
  phase "normalization literal inputs reflected"
  let proposal := mkAppN (mkConst ``normalizationLiteral) arguments
  let text ← evalExpr (Except String String)
    (← mkAppM ``Except #[mkConst ``String, mkConst ``String]) proposal
  phase "normalization literal proposed"
  let .ok text := text | throwError "connection-native-normalization-refused"
  phase s!"normalization literal bytes {text.utf8ByteSize}"
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "connection-native-normalization-syntax"
  phase "normalization literal parsed"
  -- Elaborate against the reflected finite indices. Keeping projections of
  -- the original input certificate here makes every literal constructor
  -- recompute that certificate during dependent type unification.
  let resultType ← inferType (mkAppN computation.getAppFn arguments)
  let expected ← whnf resultType.getAppArgs.back!
  let indices ← expected.getAppArgs.mapM fun index => withTransparency .all <| Syntax.normalize cache index
  phase "normalization literal indices shared"
  -- Printed constructor annotations resolve in the source vocabulary, even
  -- when the caller opened only the construction API.
  let literal : TSyntax `term := ⟨parsed⟩
  let wrapped ← `(open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm in $literal)
  let proposed ← Term.elabTerm wrapped (some (mkAppN expected.getAppFn indices))
  phase "normalization literal elaborated"
  -- Literal source applications contain finite-index proof obligations. Solve
  -- those before the normal form is frozen behind a kernel declaration.
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposed ← instantiateMVars proposed
  if proposed.hasMVar then throwError "connection-normalization-literal-unresolved"
  return proposed

end ZkcTools.ConstructionBindings.Normalization
