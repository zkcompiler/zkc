import Lean.Elab.Command
import Zkc.Core.Context

/-! What a printed package needs from Lean's elaborator: a proof by reflexivity that
only the kernel checks, and a definition that is added as it was elaborated.

`kernel_rfl%` stands for a proof of an equation `left = right`. It elaborates to
`Eq.refl right`, stated at the expected type, without asking the elaborator to compare
the two sides. The kernel compares them when the declaration is added: it evaluates
`left` to `right`. A printed package uses it for the validity of every reference and for
the facts that link a definition to its raw syntax, so that the elaborator's evaluator,
which is slower than the kernel's, never runs on them.

`linked_def name : type := value` adds a definition whose value is the elaborated term.
The `def` command would first move every proof inside the value into an auxiliary
theorem of its own; the kernel would then check each reference of a typed term in a
separate declaration and evaluate the context of the reference again for each. Added as
elaborated, a definition is one declaration: the kernel evaluates every context once.
The definition is not compiled.

`bindings%` writes the context at the start of a piece of a long body. -/

open Lean Elab Command Term Meta

namespace Zkc.Core

/-- `Eq.refl right` at the expected equation `left = right`, compared by the kernel
alone. -/
elab "kernel_rfl%" : term <= expected => do
  let expected ← instantiateMVars expected
  if expected.hasExprMVar then
    tryPostpone
  let some (carrier, _, right) := expected.eq?
    | throwError "kernel_rfl%: the expected type is not an equation{indentExpr expected}"
  let level ← getLevel carrier
  return mkApp2 (mkConst ``id [Level.zero]) expected
    (mkApp2 (mkConst ``Eq.refl [level]) carrier right)

/-- `bindings% base [a, b] [c] …` is `bindAll (bindAll base [a, b]) [c] …`: the context
after a run of instructions, one `bindAll` per instruction, which is the form the kernel
meets when it checks the run. The term is built directly; only `base` and the entries go
through the term elaborator. -/
syntax (name := bindingsTerm) "bindings% " term:max (" [" term,* "]")* : term

@[term_elab bindingsTerm] def elabBindings : TermElab := fun syntaxTree expected? => do
  match syntaxTree with
  | `(bindings% $base $[[$groups,*]]*) =>
      let base ← elabTerm base expected?
      let listType ← whnfR (← inferType base)
      let entry := listType.appArg!
      let level := listType.getAppFn.constLevels!
      let mut context := base
      for group in groups do
        let entries ← group.getElems.mapM fun item => elabTermEnsuringType item entry
        let list := entries.foldr (fun head tail => mkApp3 (mkConst ``List.cons level) entry head tail)
          (mkApp (mkConst ``List.nil level) entry)
        context := mkApp3 (mkConst ``Zkc.Source.bindAll) entry context list
      return context
  | _ => throwUnsupportedSyntax

/-- A definition added as elaborated: no proof inside its value becomes a declaration of
its own. -/
elab "linked_def " name:ident " : " type:term " := " value:term : command => do
  let declaration := (← getCurrNamespace) ++ name.getId
  let started ← IO.monoNanosNow
  let (type, value) ← profileitM Exception "elaboration" (← getOptions) <|
      liftTermElabM <| withEnableInfoTree false do
    let type ← elabType type
    let value ← elabTermEnsuringType value type
    synthesizeSyntheticMVarsNoPostponing
    pure (← instantiateMVars type, ← instantiateMVars value)
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  let elaborated ← IO.monoNanosNow
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl (.defnDecl {
    name := declaration, levelParams := [], type, value, hints, safety := .safe })
  let checked ← IO.monoNanosNow
  modifyEnv (addNoncomputable · declaration)
  -- With `ZKC_LINKED_TIMES` set, report the two times of every definition.
  if (← IO.getEnv "ZKC_LINKED_TIMES").isSome then
    logInfo m!"{name.getId}: elaboration {(elaborated - started) / 1000} us, kernel {(checked - elaborated) / 1000} us"

end Zkc.Core
