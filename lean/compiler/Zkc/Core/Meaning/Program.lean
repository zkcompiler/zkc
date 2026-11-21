module

public import Zkc.Core.Meaning.Role
public import Zkc.Core.Program.Project

@[expose] public section

/-!
The meanings of a whole program.

The definitions of a program come latest first, each applying only earlier ones, so the
processes of its functions, of its protocols (with the record of each run) and of the
programs of their roles are tables built in that order. A caller passes the inputs of a
definition by position; the definition's meaning binds them to the names of its inputs, in an
environment with nothing else in scope. The program of a role is the
projection of its protocol to the role, computed here. That every role program is a projection
of its protocol is the theorem `projection`, in `Projection/Theorem.lean`.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## Tables of a program -/

/-- The process of each function of a program. -/
def Defs.fnTable : {hs : Headers V} → Defs V hs → FnTable M hs.fns
  | _, .nil => fun _ f => nomatch f
  | _, .fn _ inputs body _ rest _ => fun hdr' f ins =>
      match hdr', f, ins with
      | _, .head, ins =>
          body.denote (localSem M _ (Defs.fnTable rest)) [] (Env.empty.extend inputs ins)
      | _, .tail f, ins => Defs.fnTable rest _ f ins
  | _, .protocol (hs := hs) _ _ _ _ rest => Defs.fnTable (hs := hs) rest

/-- The process of each protocol of a program, with the record of its run. -/
def Defs.gTable : {hs : Headers V} → Defs V hs → GTable M hs.protocols
  | _, .nil => fun _ p => nomatch p
  | _, .fn (hs := hs) _ _ _ _ rest _ => Defs.gTable (hs := hs) rest
  | _, .protocol _ inputs body ok rest => fun hdr' p path ins =>
      match hdr', p, ins with
      | _, .head, ins =>
          (Term.observe M (Defs.fnTable M rest) (Defs.gTable rest) body path
              (Env.empty.extend inputs ins)).map
            fun out => (out.1, cast (congrArg (fun s : Shape V => s.fields.Val M) ok.shaped.symm) out.2)
      | _, .tail p, ins => Defs.gTable rest _ p path ins

/-- The program of each role of each protocol of a program: the projection of the protocol
to the role, over the tables of the definitions before it. -/
def Defs.rTable : {hs : Headers V} → Defs V hs → RTable M hs.protocols
  | _, .nil => fun _ p => nomatch p
  | _, .fn (hs := hs) _ _ _ _ rest _ => Defs.rTable (hs := hs) rest
  | _, .protocol _ inputs body _ rest => fun hdr' p j path ins =>
      match hdr', p, ins with
      | _, .head, ins =>
          (project j body).denote (roleSem M j (Defs.fnTable M rest) (Defs.rTable rest)) path
            (Env.empty.extend inputs ins)
      | _, .tail p, ins => Defs.rTable rest _ p j path ins

/-! ## The functions of the meaning -/

/-- A function: a process with no effect. -/
def fnMeaning (p : Typed V) {hdr : FnHeader V} (f : Member p.headers.fns hdr)
    (ins : HList M.Val hdr.ins) : Local (HList M.Val hdr.outs) :=
  Defs.fnTable M p.defs _ f ins

/-- A protocol: one process of all its roles, which returns its results and the record of the
run. -/
def protocolMeaning (p : Typed V) {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr)
    (path : List Frame) (ins : HList (LVal M) hdr.ins) :
    Protocol M (HList (LVal M) hdr.outs × hdr.record.Val M) :=
  Defs.gTable M p.defs _ x path ins

/-- A role program: the process of one role over what it holds. -/
def roleMeaning (p : Typed V) {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr)
    (r : Role) (path : List Frame) (ins : HList (RV M r) hdr.ins) :
    Program M (HList (RV M r) hdr.outs) :=
  Defs.rTable M p.defs _ x r path ins

/-! The three meanings are closed to Lean's own reduction. A statement about a program is about
`fnMeaning`, `roleMeaning` or `protocolMeaning` applied to it; where Lean matches two such
statements, or normalizes one, an open meaning is unfolded into its table and the program is run
by a reduction without sharing. The kernel finds a meaning equal to its table, so a proof passes
between them by a kernel check (`kernel_rfl`), and a theorem that does so by definitional
unfolding opens the names for itself (`unseal … in`). -/
attribute [irreducible] fnMeaning protocolMeaning roleMeaning

end

end Zkc.Core
