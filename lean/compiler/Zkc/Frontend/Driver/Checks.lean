module

public import Zkc.Frontend.Driver.Session

@[expose] public section

set_option autoImplicit false

/-!
# The checks as views of a session

The checks of names, of instances, of the typing of bodies and of schemes, as the tests and the
tools read them: each is a session after its phases, and what it gives is read off the session.
The refusals of a check are the diagnostics of its phases, in source order.
-/

namespace Zkc.Frontend

open Driver

/-- The check of names: a session after assembly and resolution. -/
structure NameCheck where
  session : Session
  deriving Inhabited

namespace NameCheck

def program (check : NameCheck) : Program := check.session.state.program

def resolutions (check : NameCheck) : Resolutions := check.session.state.env.modules.resolutions

/-- The static terms of the comments `// instantiate: m<args>`, with their file. -/
def instantiations (check : NameCheck) : Array (FileId × Syntax.Expr) :=
  check.session.state.env.modules.instantiations

/-- The refusals of assembly and of names, in source order. -/
def refusals (check : NameCheck) : Array Refusal := check.session.refusalsOf #["assemble", "names"]

end NameCheck

/-- Assembles a program from the given sources and the library, and resolves its names. -/
def checkNames {m : Type → Type} [Monad m] (inputs : Array SourceInput)
    (load : Array String → m (Option SourceInput)) : m NameCheck := do
  return ⟨← Session.start.compile inputs load "names"⟩

/-- The check of instances: a session after the phase of instances. -/
structure InstanceCheck where
  session : Session
  deriving Inhabited

namespace InstanceCheck

def names (check : InstanceCheck) : NameCheck := ⟨check.session⟩

def context (check : InstanceCheck) : Compile.Context := check.session.context

def state (check : InstanceCheck) : Compile.State := check.session.state

def fileOrder (check : InstanceCheck) : Array String := check.session.fileOrder

/-- The refusals of the check of instances, in source order, with their chains. -/
def refusals (check : InstanceCheck) : Array Refusal := check.session.refusalsOf #["instances", "defaults"]

/-- The checks of instances left incomplete: a budget of the compiler ran out in each. -/
def incomplete (check : InstanceCheck) : Array Diagnostic :=
  check.session.incompleteOf #["instances", "defaults"]

/-- The number of instances formed, by the kind of their declaration. -/
def countsByKind (check : InstanceCheck) : Array (String × Nat) := Zkc.Frontend.countsByKind check.state

end InstanceCheck

/-- Instantiates the roots of a program whose names resolve: the phase of instances alone,
before any body is typed. -/
def checkRoots (check : NameCheck) (inputs : Array String := #[]) : InstanceCheck :=
  let session := if inputs.isEmpty then check.session else { check.session with inputNames := inputs }
  ⟨session.run Driver.instances⟩

/-- Types the bodies of what the roots reach, forms the default instances, and types their
bodies. -/
def typeBodiesOf (check : InstanceCheck) : InstanceCheck :=
  ⟨check.session.runAll #[Driver.types, Driver.defaults, Driver.defaultBodies]⟩

/-- Instantiates the roots of a program whose names resolve, and forms the default instances of
what no root reaches, which needs the bodies of what the roots reach typed first (SP7). The
refusals of the check are those of the instances: of the roots and of the default instances. -/
def checkInstances (check : NameCheck) (inputs : Array String := #[]) : InstanceCheck :=
  let session := if inputs.isEmpty then check.session else { check.session with inputNames := inputs }
  ⟨session.runAll #[Driver.instances, Driver.types, Driver.defaults]⟩

/-- The check of the typing of bodies: a session after typing and the packages of the roots. -/
structure TypingCheck where
  session : Session
  deriving Inhabited

namespace TypingCheck

def instances (check : TypingCheck) : InstanceCheck := ⟨check.session⟩

def state (check : TypingCheck) : Compile.State := check.session.state

def fileOrder (check : TypingCheck) : Array String := check.session.fileOrder

/-- The package of every root that is a function or a protocol, in the order of the roots. -/
def packages (check : TypingCheck) : Array PackageReport := check.state.results.packageReports

/-- Every refusal so far, the check of instances' included, in source order. -/
def refusals (check : TypingCheck) : Array Refusal :=
  check.session.refusalsOf #["instances", "types", "defaults", "default bodies", "packages"]

/-- Every check left incomplete so far, the check of instances' included. -/
def incomplete (check : TypingCheck) : Array Diagnostic :=
  check.session.incompleteOf #["instances", "types", "defaults", "default bodies", "packages"]

end TypingCheck

/-- Types the bodies of the default instances of a program whose instances are formed and whose
other bodies are typed, and emits and admits the package of every root that is a function or a
protocol. -/
def checkTyping (check : InstanceCheck) (inputs : Array String := #[]) : TypingCheck :=
  let session := if inputs.isEmpty then check.session else { check.session with inputNames := inputs }
  ⟨session.runAll #[Driver.defaultBodies, Driver.packages]⟩

/-- The schemes of a program after the typing of bodies: a session after the phase of schemes. -/
structure SchemeCheck where
  session : Session
  deriving Inhabited

namespace SchemeCheck

def reports (check : SchemeCheck) : Array SchemeReport := check.session.state.results.schemeReports

/-- The diagnostics of the rules of schemes, in the order the schemes were made. -/
def diagnostics (check : SchemeCheck) : Array Diagnostic := check.session.diagnosticsOf #["schemes"]

/-- The refusals of the rules of schemes, in the order the schemes were made. -/
def refusals (check : SchemeCheck) : Array Refusal :=
  (check.diagnostics.filter (·.isError)).map (·.toRefusal Renderer.plain)

end SchemeCheck

/-- Constructs every scheme of a typed program. -/
def checkSchemes (check : TypingCheck) : SchemeCheck := ⟨check.session.run Driver.schemes⟩

end Zkc.Frontend
