module

public import Zkc.Core.Run.Run
public import Zkc.Core.Format.Format
public import Zkc.Core.Program.Syntax

@[expose] public section

/-!
The functions of the core, with their types, as a record: what the statements of
`Statements.lean` are about. For a program of functions, elaboration, admission and the check of
one definition are built as definitions (`Admission/`); the others are still to be built. An
admitted program and a deployed scheme are data, and what is said of them is defined over that
data in the other modules of the core.
-/

namespace Zkc.Core

/-! ## The functions to be built -/

/-- The functions of elaboration, admission, deployment and execution. The printed form of a
typed program is the definition `print`. For a program of functions, `elaborate`, `admit` and
`check` are the definitions `elaborateFunctions`, `admit` and `check`, which refuse a protocol;
the record gets them when protocols are elaborated. The others are still to be built. -/
structure Functions (V : Vocabulary) where
  /-- The typed program of a program by names, of functions and protocols; the refusals of
  elaboration. -/
  elaborate : NamedProgram V → Except (List (ProgramRefusal V)) (Typed V)
  /-- The printed form of a role's code: of its program, and of a clause of a handler. -/
  printRole : ∀ {hs : Headers V} (r : Role) {Γ outs : List (LTy V)},
    Term (roleDialect V hs r) Γ outs → Region (RoleRaw V) (List Role)
  /-- The canonical format of a type: the core's combinators over the formats of the nominal
  carriers that a model with codecs gives. -/
  format : ∀ (M : Model V), Codecs M → ∀ τ : V.Ty, Format (M.Val τ)
  /-- Admission: elaboration, then the check of facts. -/
  admit : NamedProgram V → Association → Except (List (ProgramRefusal V)) (Admitted V)
  /-- The check of one definition against the headers of those before it: what `admit` does
  for each definition, and what a frontend calls while a program is being written. It gives
  the headers with the definition's. -/
  check : Headers V → Definition V → Except (List (ProgramRefusal V)) (Headers V)
  deploy : Admitted V → Declaration → Except (List (ProgramRefusal V)) (Deployed V)
  /-- The identity of a deployed scheme: what its proofs and its transcript are bound to. -/
  identity : Deployed V → List Nat
  /-- The executor: one role in a world, to a limit of steps. It reports how the run ended
  and what the role did. -/
  execute : Executor V
  /-- The scheduler: the roles of a protocol together, each on its part of the inputs, over
  the network, to a limit of steps. It reports the record of the execution and, for each role,
  how it ended. -/
  schedule : ∀ (p : Typed V) (M : Model V) (hdr : ProtocolHeader V)
    (_ : Var p.headers.protocols hdr), (∀ r, HList (RV M r) hdr.ins) → Source M → Nat →
      List (Happened M) × (∀ r, Outcome (HList (RV M r) hdr.outs) Unit)

end Zkc.Core
