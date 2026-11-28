module

public meta import Lean

public meta section

/-!
Commands that ask the kernel to compute.

`kernel_ok` defines a term of data as the kernel's normal form of what an `Except` expression
holds when the kernel reduces it to `ok`, with the equation between the expression and the new
constant. `kernel_normal` defines a term of data as the kernel's normal form of an expression,
with the equation between the two: the program of a role is the projection of a protocol's
body, which is a term and no `Except`.

Nothing here is trusted. Each definition and each equation is given to the kernel as it is, and
the kernel checks it. Lean's unifier is not asked to compute: on a long program it evaluates a
context again at each use, and its cost grows faster than the program.
-/

open Lean Elab Meta Command Term

namespace Zkc.Kernel

/-- The kernel's head normal form. -/
def whnf (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  ofExceptKernelException (Lean.Kernel.whnf (← getEnv) (← getLCtx) e)

/-- Normal forms already found, by term and expected type. -/
abbrev NormalM := StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM

/-- The proof, so that the type Lean infers for it is the proposition it proves here. A proof
that the kernel finds while it computes can have a type that only more computation makes that
proposition: the proof that a decision gives has the type of what the decision reflects. A
lemma that takes any proof of the proposition then does not match it by its type. -/
def stated (proof proposition : Expr) : MetaM Expr := do
  if (← inferType proof) == proposition then return proof
  return mkApp2 (mkConst ``id [Level.zero]) proposition proof

/-- The normal form of a term of data at an expected type, by the kernel.

The head normal form of the term is taken. When it is an application of a constructor, its
parameters are those of the expected type as they stand there, a field that the constructor's
result type gives as an index is the normal form of that index of the expected type, and every
other field that is neither a proof nor a type nor a function is the normal form of the field
at the type that the constructor gives it. So what a term holds is evaluated from the term, and
what its type says is read from the type and not from the computation that produced the term.
A proof stays as it is, stated at the proposition that the constructor gives its field. A
constant stays the constant: a name is a normal form. -/
partial def normalAt (e expected : Expr) : NormalM Expr := do
  if e.isConst then return e
  if let some found := (← get).get? (e, expected) then return found
  let head ← whnf e
  let result ← constructed head
  modify (·.insert (e, expected) result)
  return result
where
  /-- The head normal form with its parameters from the type and its fields in normal form,
  when it is an application of a constructor; itself otherwise. -/
  constructed (head : Expr) : NormalM Expr := do
    let .const name levels := head.getAppFn | return head
    let some (.ctorInfo info) := (← getEnv).find? name | return head
    let args := head.getAppArgs
    unless args.size == info.numParams + info.numFields do return head
    let numIndices := (← getConstInfoInduct info.induct).numIndices
    let type ← whnf expected
    let typed := type.getAppFn.isConstOf info.induct &&
      type.getAppNumArgs == info.numParams + numIndices
    let params := if typed then type.getAppArgs.extract 0 info.numParams
      else args.extract 0 info.numParams
    -- the fields' types, each over the fields before it, and the constructor's result type
    let mut rest := info.type.instantiateLevelParams info.levelParams levels
    for param in params do
      rest := rest.bindingBody!.instantiate1 param
    let mut domains := #[]
    for _ in [0:info.numFields] do
      domains := domains.push rest.bindingDomain!
      rest := rest.bindingBody!
    -- a field that the result type gives as an index is that index of the expected type
    let mut given : Array (Option Expr) := Array.replicate info.numFields none
    if typed then
      let indices := rest.getAppArgs.extract info.numParams (info.numParams + numIndices)
      let wanted := type.getAppArgs.extract info.numParams (info.numParams + numIndices)
      for index in indices, value in wanted do
        if let .bvar i := index then
          if i < info.numFields then given := given.set! (info.numFields - 1 - i) (some value)
    let mut fields := #[]
    for j in [0:info.numFields] do
      let domain := domains[j]!.instantiateRev fields
      let field := args[info.numParams + j]!
      let value ← match given[j]! with
        | some index => normalAt index domain
        | none =>
          if ← isProp domain then stated field domain
          else if (← Meta.isType field) || (← whnf domain).isForall then pure field
          else normalAt field domain
      fields := fields.push value
    return mkAppN (mkConst name levels) (params ++ fields)

/-- A term with every numeral written as Lean's elaborator writes one: `OfNat.ofNat` at a
literal, where the kernel's normal form has the bare literal. A tactic that matches terms as
they are written (a rule that an author states against a term made from this data) tells the two
apart, and what an author writes has `OfNat.ofNat`. The literal inside an `OfNat.ofNat` stays. -/
def numerals (e : Expr) : Expr :=
  e.replace fun part =>
    if part.isAppOfArity ``OfNat.ofNat 3 then some part
    else match part with
      | .lit (.natVal n) => some (mkNatLit n)
      | _ => none

/-- The normal form of a term of data at its type, by the kernel, with its numerals as Lean
writes them. -/
def normal (e type : Expr) : MetaM Expr := return numerals (← (normalAt e type).run' {})

/-- A definition that the kernel checks. Its value is exported with it, in a module too: what
these commands define is data that the modules after it read. It is not compiled, and it is
marked so: a definition that uses it is then not compiled either, where that is allowed. -/
def define (name : Name) (type value : Expr) : MetaM Unit := do
  addDecl (forceExpose := true) <| .defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  modifyEnv (addNoncomputable · name)

/-- The term with its first explicit arguments of data each named by a definition, in order:
`names[i]` is defined as the `i`-th such argument, at the type that the constructor gives it
after the arguments before it. The term must be an application of a constructor. -/
def nameComponents (scope : Name) (names : Array Name) (term : Expr) : MetaM Expr := do
  if names.isEmpty then return term
  let .const ctor levels := term.getAppFn
    | throwError "kernel_ok: no constructor to name the arguments of{indentExpr term}"
  let some (.ctorInfo info) := (← getEnv).find? ctor
    | throwError "kernel_ok: no constructor to name the arguments of{indentExpr term}"
  let args := term.getAppArgs
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  let mut out := #[]
  let mut next := 0
  for i in [0:args.size] do
    let .forallE _ domain body binder := type
      | throwError "kernel_ok: more arguments than the constructor takes{indentExpr term}"
    let mut arg := args[i]!
    if i ≥ info.numParams && binder == .default && next < names.size then
      unless (← isProp domain) || (← Meta.isType arg) do
        let declName := scope ++ names[next]!
        define declName domain arg
        arg := mkConst declName
        next := next + 1
    out := out.push arg
    type := body.instantiate1 arg
  unless next == names.size do
    throwError "kernel_ok: {names.size} names for {next} explicit arguments of data{indentExpr term}"
  return mkAppN term.getAppFn out

/-- Closes an equation whose two sides the kernel finds definitionally equal, by reflexivity.
Lean's own reduction is not asked. The kernel compares the sides once, here: the equation
becomes a theorem of its own, which the kernel checks as the tactic runs, and the proof that
the tactic closes refers to that theorem, so that the declaration around it does not have the
kernel compare the sides again. A failure is reported at the tactic, also under an option of
the file that turns the kernel's check of declarations off. -/
elab "kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := type.eq?
    | throwError "kernel_rfl: the goal is no equation"
  let refused : MessageData :=
    m!"kernel_rfl: the kernel does not find the two sides definitionally equal"
  if type.hasExprMVar then
    -- an equation with something still to be found is no theorem yet: the kernel compares the
    -- sides as they stand, and again when the proof is closed
    let same ← ofExceptKernelException (Lean.Kernel.isDefEq (← getEnv) (← getLCtx) lhs rhs)
    unless same do throwError refused
    goal.assign (← mkEqRefl lhs)
  else
    let proof ←
      try
        -- checked now and by the kernel whatever the file says: an option that has the
        -- kernel skip a declaration does not reach this one. The theorem is added anew and
        -- never taken from the cache of auxiliary lemmas: a lemma of the same type that
        -- another tactic added earlier in the declaration, under such an option, is there
        -- unchecked.
        -- A `let` of the context keeps its value in the theorem: the kernel has it where it
        -- compares the sides in the goal's context, and an equation that holds by it is one
        withOptions (fun options =>
            debug.skipKernelTC.set (Lean.Elab.async.set options false) false) do
          mkAuxTheorem type (← mkEqRefl lhs) (zetaDelta := true) (cache := false)
      catch failure =>
        -- the kernel's own message shows both sides in full, which for a program is long
        if failure.isRuntime || failure matches .internal .. then throw failure
        throwError refused
    goal.assign proof

/-- `kernel_normal name : type := term` defines `name` as the kernel's normal form of `term`,
and states `name.eq : name = term`, which the kernel checks. -/
elab "kernel_normal " name:ident " : " type:term " := " value:term : command =>
  liftTermElabM do
    let type ← elabType type
    let value ← elabTermEnsuringType value type
    synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    let declName := (← getCurrNamespace) ++ name.getId
    define declName type (← normal value type)
    addDecl <| .thmDecl {
      name := declName ++ `eq, levelParams := [], type := ← mkEq (mkConst declName) value,
      value := ← mkEqRefl (mkConst declName) }

/-- `kernel_ok name with a b c : type := term`, for a `term` of an `Except` type that the kernel
reduces to `ok`: defines `name` as the kernel's normal form of what it holds, states
`name.eq : term = .ok name`, and, when names follow `with`, defines each as one of the first
explicit arguments of data of the constructor that `name` is. A term that the kernel reduces to
`error` is refused, with what the error holds. -/
syntax (name := kernelOk) "kernel_ok " ident (" with " ident+)? " : " term " := " term : command

def elabKernelOk (name : Ident) (names : Array Name) (type value : Term) : CommandElabM Unit :=
  liftTermElabM do
    let type ← elabType type
    let value ← elabTerm value none
    synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    let head ← whnf value
    unless head.isAppOfArity ``Except.ok 3 do
      if head.isAppOfArity ``Except.error 3 then
        let refusal := head.getArg! 2
        throwError "kernel_ok: the kernel reduces the term to an error{indentExpr (← normal refusal (← inferType refusal))}"
      throwError "kernel_ok: the kernel does not reduce the term to `ok`{indentExpr head}"
    let scope ← getCurrNamespace
    let payload ← nameComponents scope names (← normal (head.getArg! 2) type)
    let declName := scope ++ name.getId
    define declName type payload
    let holds := mkAppN head.getAppFn #[head.getArg! 0, head.getArg! 1, mkConst declName]
    addDecl <| .thmDecl {
      name := declName ++ `eq, levelParams := [], type := ← mkEq value holds,
      value := ← mkEqRefl value }

elab_rules : command
  | `(kernel_ok $name:ident with $parts:ident* : $type := $value) =>
      elabKernelOk name (parts.map (·.getId)) type value
  | `(kernel_ok $name:ident : $type := $value) => elabKernelOk name #[] type value

end Zkc.Kernel
