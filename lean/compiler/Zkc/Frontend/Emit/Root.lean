module

public import Zkc.Core.Elaborate
public import Zkc.Core.Lower
public import Zkc.Core.Admission
public import Zkc.Frontend.Emit.Definitions

@[expose] public section

set_option autoImplicit false

/-!
# The package of a root

A package is emitted per root: the function and protocol instances the root reaches, each
from its tree (`Emit.Definitions`), with the records, variants, nominal types and rows they
reach. The definitions are handed to the core as a named program (`Zkc.Core.Named`): every
value is a name, and a value that several roles hold is one name with its holders. The core's
lowering makes the positional form (positions, the captures of a nested region, the site
numbers), and `Zkc.Core.fillMaxima` writes the maximum of a loop of a protocol body from the
core's facts.

Beside the package the emission states what admission checks against it: the keys of its
sites, which functions can stop, and the vocabulary of whose types the data of its literals
are.
-/

namespace Zkc.Frontend.Typing

open Static

/-- What an emission gives the core: the package, and what is stated beside it for admission
to check. -/
structure Emitted where
  package : Zkc.Core.Raw.Package
  claims : Zkc.Core.Admission.Claims

/-- The package of what an emission reaches, with the declarations carrying their shapes, what
is stated beside it, and the emission's value. -/
def emitWith {α : Type} (state : Compile.State) (emission : EmitM α) :
    Except EmitFailure (Emitted × α) := do
  let (value, emitter) ← (emission.run state).run {}
  let named ← emitter.named
  match Zkc.Core.Named.lower named with
  | .ok lowered =>
    -- every row under a name of the core's vocabulary is stated to be its row. A row under
    -- another name (a row of a project, and until their units land the rows of a circuit) is a
    -- row of an extension: the core does not refuse it, and a package with one cannot be run
    -- under the vocabulary's model alone
    let table := Zkc.Core.Vocabulary.table
    return ({ package := Zkc.Core.fillMaxima lowered.package
              claims := { keys := some lowered.keys, stops := some emitter.stops.toList
                          rows := some table, literals := some table } }, value)
  | .error (_, refused) =>
    throw (.defect s!"the lowering refuses the package at node {refused.tag}: {refused.message}")

/-- The emission of a root: a protocol root is the last protocol of its package, a function
root the last function. -/
def rootNumber (root : InstanceId) : EmitM Nat := do
  match (← read).results.body? root with
  | some (.protocol _) => Emit.protocolOf root
  | _ => Emit.functionOf root

/-- The package of a root, with what is stated beside it. -/
def emitRoot (state : Compile.State) (root : InstanceId) : Except EmitFailure Emitted :=
  (emitWith state (rootNumber root)).map (·.1)

/-- The named package of a root, before it is lowered. -/
def namedRoot (state : Compile.State) (root : InstanceId) :
    Except EmitFailure Zkc.Core.Named.Package := do
  let (_, emitter) ← ((rootNumber root).run state).run {}
  emitter.named

/-- The package of a root. -/
def emitPackage (state : Compile.State) (root : InstanceId) : Except EmitFailure Zkc.Core.Raw.Package :=
  (emitRoot state root).map (·.package)

end Zkc.Frontend.Typing
