module

public import Zkc.Core.Serialize
public import Zkc.Frontend.Basic.Log
public import Zkc.Core.Construction

@[expose] public section

set_option autoImplicit false

/-!
# What emission and the construction of schemes report

Until a run emits one package, every root has a package of its own, which the core admits or
refuses (`PackageReport`), and every scheme is constructed by the core on the package of its
protocol instance (`SchemeReport`). These are the results of the phases of packages and of
schemes, kept in the store of results.

What a run made of the roots it was asked for is an `Admitted` result: the roots it holds, each
with what was made of it, the roots it lacks, each with why, and the number of errors and of
incomplete checks it reported, read from the log of the run. A root is run, proved, verified or
written as a package only from a `Completed` result, which only an admitted one makes: a root is
complete when the run reported no error, left no check incomplete, and holds that root.
-/

namespace Zkc.Frontend

/-- Why an instance is a root of what a run emits. -/
inductive Emit.EntryKind where
  /-- A declaration without static parameters, or the protocol instance of a scheme. -/
  | root
  /-- An instance that a comment `// instantiate:` asks for. -/
  | directive
  /-- A default instance of a public declaration that no root reached (SP7). -/
  | defaultInstance
  deriving Inhabited, BEq, Repr

/-- What became of the package of a root. -/
inductive PackageOutcome where
  /-- Admitted by the core: elaborated, and every function and protocol passes the check of
  facts. -/
  | admitted (package : Zkc.Core.Raw.Package)
  /-- Elaborated by the core; the functions and protocols named do not pass its check of facts,
  each with its first application that is not justified. -/
  | unjustified (functions : Array String) (package : Zkc.Core.Raw.Package)
  /-- Emitted and refused by the core. -/
  | refused (reason : String) (package : Zkc.Core.Raw.Package)
  /-- Not emitted: a form that is not typed yet. -/
  | waiting (reason : String)
  /-- Typed, and not emitted: a specification item whose types or operations have no form in
  the core (`rational`, a `spec type`). -/
  | typedOnly (reason : String)
  /-- Not emitted: a defect of the frontend. -/
  | defect (message : String)
  /-- Not checked to the end: a budget of the compiler ran out (SP10). -/
  | exhausted (exhaustion : Exhaustion)

instance : Inhabited PackageOutcome := ⟨.waiting ""⟩

structure PackageReport where
  root : InstanceId
  /-- The root as source writes it. -/
  description : String
  outcome : PackageOutcome
  deriving Inhabited

/-- A scheme that the core has constructed: the admitted package of the protocol instance with
the rows of the suite and of the layout, the declaration, and the core's construction, in
which what each step returns is admitted. -/
structure Constructed where
  name : String
  /-- The admitted package of the protocol instance with the rows of the suite and of the
  layout. -/
  source : Zkc.Core.Admitted
  /-- The declaration, with the proof identity. -/
  declaration : Zkc.Core.Raw.Declaration
  /-- The core's construction on the admitted package. -/
  construction : Zkc.Core.Construction source declaration
  identity : List Nat
  roles : Array String
  prover : Nat
  verifier : Nat
  /-- The names of the ports that are not `spec`. -/
  ports : Array String
  /-- The ports of the statement and of the witness, in the order of the signature. -/
  statement : Array Nat
  witness : Array Nat
  /-- The port of each input of the entry. -/
  inputPorts : Array Nat
  /-- The projection to the prover's and the verifier's programs: the number of programs, or why
  the core does not project. -/
  projected : Except String Nat

namespace Constructed

/-- The package of the protocol instance with the rows of the suite and of the layout. -/
abbrev package (scheme : Constructed) : Zkc.Core.Raw.Package := scheme.source.package

abbrev typed (scheme : Constructed) : Zkc.Core.Typed := scheme.source.typed

/-- The protocols after the two steps. -/
abbrev stepped (scheme : Constructed) :
    Zkc.Core.Stepped scheme.typed.typeTable (scheme.typed.table.map (·.signature))
      scheme.typed.functions :=
  scheme.construction.serialized

/-- The constructed program as a raw package, without names: the admitted package of what the
serialize step returns. -/
abbrev constructed (scheme : Constructed) : Zkc.Core.Raw.Package :=
  scheme.construction.admitted.package

end Constructed

/-- What became of a scheme. -/
inductive SchemeOutcome where
  | constructed (scheme : Constructed)
  /-- Emitted, and refused by the core's elaboration or by its construction. -/
  | refusedByCore (reason : String) (package : Zkc.Core.Raw.Package)
  | waiting (reason : String)
  | refused (refusal : Diagnostic)
  | defect (message : String)
  /-- Not constructed: the protocol is not checked to the end, a budget of the compiler ran out
  (SP10). -/
  | exhausted (exhaustion : Exhaustion)

instance : Inhabited SchemeOutcome := ⟨.waiting ""⟩

structure SchemeReport where
  name : String
  /-- The scheme as source writes it: `scheme Proof = Schnorr<G1>`. -/
  description : String
  outcome : SchemeOutcome
  deriving Inhabited

/-! ## Admitted and completed results -/

/-- Why a root that was asked for is not in a result. -/
inductive Lack where
  /-- Refused: by the frontend, with an error logged, or by the core. -/
  | refused (reason : String)
  /-- Not computed: it needs a form of a later layer. -/
  | waiting (reason : String)
  /-- Not checked to the end: a budget of the compiler ran out. It is not refused (SP10). -/
  | exhausted (exhaustion : Exhaustion)
  /-- Without a package of its own: a specification item, typed and without a form in the
  core; a function bound to a row of the vocabulary. -/
  | noPackage (reason : String)
  /-- Not computed: a defect of the frontend. -/
  | defect (message : String)
  /-- The program has no root of the name asked for. -/
  | absent
  deriving Inhabited

def Lack.describe : Lack → String
  | .refused reason => s!"refused: {reason}"
  | .waiting reason => s!"waiting for {reason}"
  | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"
  | .noPackage reason => s!"no package of its own: {reason}"
  | .defect message => s!"not computed, a defect of the frontend: {message}"
  | .absent => "no root of this name"

/-- What a run made of the roots it was asked for: those it holds, each with what was made of it,
and those it lacks, each with why, beside the errors and incomplete checks that the run reported.
It is built from the log of the run (`ofLog`); it says what is there and what is not, and nothing
of it is run, proved, verified or written until a completed result is taken from it. -/
structure Admitted (α : Type) where
  private mk ::
  /-- The roots held, each named as source writes it, with what was made of it. -/
  held : Array (String × α)
  /-- The roots asked for that are not held, with why. -/
  lacking : Array (String × Lack)
  /-- The errors that the run reported, anywhere in the program. -/
  errors : Nat
  /-- The checks that the run left incomplete, anywhere in the program. -/
  incomplete : Nat

/-- Roots that are complete: each held, from a run that reported no error and left no check
incomplete. Only an admitted result makes one. -/
structure Completed (α : Type) where
  private mk ::
  held : Array (String × α)

end Zkc.Frontend

end

/- The bodies that make admitted and completed results are not exposed: they alone make them. -/
public section

namespace Zkc.Frontend

namespace Admitted

variable {α : Type}

/-- The result of the roots asked for, each held or lacking with why, with the errors and the
incomplete checks of the log of the run. -/
def ofLog (log : Log) (roots : Array (String × Except Lack α)) : Admitted α :=
  roots.foldl (init := ⟨#[], #[], log.errors, log.incomplete⟩) fun admitted (root, outcome) =>
    match outcome with
    | .ok value => { admitted with held := admitted.held.push (root, value) }
    | .error lack => { admitted with lacking := admitted.lacking.push (root, lack) }

/-- What the run reported that keeps every root from being complete, one line each. -/
def reported (admitted : Admitted α) : Array String :=
  (if admitted.errors == 0 then #[] else #[s!"{admitted.errors} errors are reported"]) ++
    (if admitted.incomplete == 0 then #[] else #[s!"{admitted.incomplete} checks are incomplete"])

/-- The roots that are not complete, one line each with why. -/
def lackingLines (admitted : Admitted α) : Array String :=
  admitted.lacking.map fun (root, lack) => s!"{root}: {lack.describe}"

/-- Every root asked for, complete: when the run reported no error, left no check incomplete,
and holds every root asked for. Otherwise what keeps it from that. This is what a request that
names its roots takes. -/
def complete (admitted : Admitted α) : Except (Array String) (Completed α) :=
  if admitted.errors == 0 && admitted.incomplete == 0 && admitted.lacking.isEmpty then
    .ok ⟨admitted.held⟩
  else .error (admitted.reported ++ admitted.lackingLines)

/-- The roots that are complete, each on its own: those held, when the run reported no error and
left no check incomplete, with those lacking and why. A root that waits keeps no other from
being complete; an error or an incomplete check anywhere keeps every one. -/
def completeRoots (admitted : Admitted α) :
    Except (Array String) (Completed α × Array (String × Lack)) :=
  if admitted.errors == 0 && admitted.incomplete == 0 then
    .ok (⟨admitted.held⟩, admitted.lacking)
  else .error admitted.reported

end Admitted

end Zkc.Frontend

end

@[expose] public section

namespace Zkc.Frontend

/-- Whether a name asked for names a root: the root as source writes it, or the declaration of
a default instance. -/
def namesRoot (name description : String) : Bool :=
  description == name || description == s!"default instance `{name}`"

/-- What a completed result holds for a root it was asked for. -/
def Completed.find? {α : Type} (completed : Completed α) (root : String) : Option α :=
  (completed.held.find? fun (description, _) => namesRoot root description).map (·.2)

end Zkc.Frontend
