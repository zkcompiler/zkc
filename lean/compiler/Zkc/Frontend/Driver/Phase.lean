module

public import Zkc.Frontend.Driver.SourcePhases
public import Zkc.Frontend.Semantics.Scheme
public import Zkc.Frontend.Driver.Bodies

@[expose] public section

set_option autoImplicit false

/-!
# The phases as data

A phase is a record: its name, which is also its trace class, the parts of the environment it
reads and the parts it adds to, and its function in the bottom layer. The pipeline is an array
of phases. A command of the tool and a measurement select a prefix of it and run each phase the
same way: with its diagnostics counted, its traces collected, and its duration taken from a
clock that the caller gives, since the library reads no clock.

The pipeline is that of the checker as it stands: assembly (the program, which loading assembled
with the library files it reaches), names (resolution of every written name), instances (the
checks of declarations and the roots), types (the bodies of what the roots reach), defaults
(the default instances of what no root reaches), default bodies (their bodies), packages
(the package of every root, admitted by the core) and schemes (the construction of every
scheme). From instantiation on, a phase does not compute everything of its kind: it asks for
what the roots need, and the requests compute the rest on the way.
-/

namespace Zkc.Frontend.Driver

/-- The body of every instance of the table is typed, the instances that typing adds included. -/
def types : Phase where
  name := "types"
  reads := #[.lowered, .signatures]
  writes := #[.signatures, .bodies]
  run := do
    Typing.typeProgram
    reportSilentRefusals

/-- The default instances of the public declarations that no root reaches (SP7): formed once
the bodies are typed, since a root reaches a declaration through bodies too. -/
def defaults : Phase where
  name := "defaults"
  reads := #[.lowered, .signatures, .bodies]
  writes := #[.signatures]
  run := do
    Instances.defaultProgram
    reportSilentRefusals

/-- The bodies of the default instances, and of what they reach. -/
def defaultBodies : Phase where
  name := "default bodies"
  reads := #[.lowered, .signatures]
  writes := #[.signatures, .bodies]
  run := do
    Typing.typeBodies
    reportSilentRefusals

/-- The package of every root that is a function or a protocol is emitted and admitted by the
core. -/
def packages : Phase where
  name := "packages"
  reads := #[.bodies]
  writes := #[.package]
  run := Typing.reportPackages

/-- Every scheme is constructed by the core, or waits, or is refused. -/
def schemes : Phase where
  name := "schemes"
  reads := #[.bodies]
  writes := #[.package]
  run := constructSchemes

/-- The phases of a whole run, in order, for a program that loading assembled. -/
def pipeline (assembly : Assembly) : Array Phase :=
  sourcePhases assembly ++ #[types, defaults, defaultBodies, packages, schemes]

/-- The phases up to and including the one with a name. -/
def upTo (phases : Array Phase) (name : String) : Array Phase :=
  match phases.findIdx? (·.name == name) with
  | some index => phases.extract 0 (index + 1)
  | none => phases

end Zkc.Frontend.Driver
