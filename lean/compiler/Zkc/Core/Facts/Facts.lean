module

public import Zkc.Core.Facts.Loops
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Meaning.Validity

@[expose] public section

/-!
What an annotation says of a program, as definitions.

`Respects` says that no loop runs more often than the bound that the annotation of an admitted
program gives it, in every function on valid inputs that satisfy the requirements of its header's
summary (`Defs.FunctionsRespect`) and every role program (`Defs.ProtocolsRespect`). The count of
every loop that a run reaches (`Term.EveryLoop`) and the annotation with the bound that it gives a
loop (`Annotation`, `Annotation.Bounded`) are for any dialect, in `Facts/Loops.lean`.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V) (annotation : Annotation)

/-- Every function on valid inputs that satisfy the requirements of its header's summary, bound to
the names of its inputs: no loop runs more often than its bound. -/
def Defs.FunctionsRespect : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn (hs := hs) hdr inputs body _ rest =>
      (∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
        FnHeader.Required M (Defs.fnTable M rest) hdr ins →
        body.EveryLoop (localSem M hs.fns (Defs.fnTable M rest)) (fun _ _ => True)
          (annotation.Bounded hdr.key none) [] [] (Env.empty.extend inputs ins)) ∧
        Defs.FunctionsRespect rest
  | _, .protocol _ _ _ _ rest => Defs.FunctionsRespect rest

/-- Every role program of every protocol on valid inputs, bound to the names of the protocol's
inputs, and permitted replies: no loop runs more often than its bound. -/
def Defs.ProtocolsRespect : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn _ _ _ _ rest => Defs.ProtocolsRespect rest
  | _, .protocol (hs := hs) hdr inputs body _ rest =>
      (∀ (r : Role) (path : List Frame) (ins : HList (RV M r) hdr.ins), ins.All (RV.Valid M r) →
        (project r body).EveryLoop
          (roleSem M r (Defs.fnTable (hs := hs) M rest) (Defs.rTable M rest))
          (Permitted M)
          (annotation.Bounded hdr.key (some r)) path [] (Env.empty.extend inputs ins)) ∧
        Defs.ProtocolsRespect rest

/-- Every function on valid inputs that satisfy its requirements and every role program of every
protocol on valid inputs and permitted replies: no loop runs more often than its bound. -/
def Defs.Respects {hs : Headers V} (defs : Defs V hs) : Prop :=
  Defs.FunctionsRespect M annotation defs ∧ Defs.ProtocolsRespect M annotation defs

/-- Definitions without protocols respect an annotation in their protocols. -/
theorem Defs.protocolsRespect_of_none : ∀ {hs : Headers V} (defs : Defs V hs),
    hs.protocols = [] → Defs.ProtocolsRespect M annotation defs
  | _, .nil, _ => trivial
  | _, .fn _ _ _ _ rest, empty => Defs.protocolsRespect_of_none rest empty
  | _, .protocol _ _ _ _ _, empty => absurd empty (List.cons_ne_nil _ _)

end

/-- A program respects an annotation, under a model. -/
def Respects {V : Vocabulary} (M : Model V) (annotation : Annotation) (p : Typed V) : Prop :=
  Defs.Respects M annotation p.defs

/-- A program without protocols respects an annotation when its functions do. -/
theorem Respects.of_functions {V : Vocabulary} {M : Model V} {annotation : Annotation}
    (p : Typed V) (noProtocols : p.headers.protocols = [])
    (functions : Defs.FunctionsRespect M annotation p.defs) : Respects M annotation p :=
  ⟨functions, Defs.protocolsRespect_of_none M annotation p.defs noProtocols⟩

end Zkc.Core
