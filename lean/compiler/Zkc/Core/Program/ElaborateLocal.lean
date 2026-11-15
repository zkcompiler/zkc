module

public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
The elaboration of a function, and the printed form of a typed program.

A function's body is elaborated by the local rules in the context of its inputs, with the names
of the body's inputs in scope; its results are the header's; its instructions have their own
addresses and its linear values are used once; and its header says whether it can stop with a
reason as its body does (a guard, or a call of a function that can).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## A function -/

/-- The body of a function by names, with what elaboration decides about it, against the
headers of the functions before it. -/
def elabFn (fns : List (FnHeader V)) (hdr : FnHeader V) :
    Region (LocalRaw V) Unit →
      Except (Problem V.Ty (LocalRaw V)) ((body : Fn V fns hdr) ×' FnConditions body)
  | .mk inputs instructions exit =>
      if inputs.length = hdr.ins.length then
        match elabBody (localRules fns) hdr.ins inputs [] instructions exit with
        | .error problem => .error problem
        | .ok ⟨outs, t⟩ =>
            if same : outs = hdr.outs then
              let body : Fn V fns hdr := cast (congrArg (Term (localDialect V fns) hdr.ins) same) t
              match Term.decideDistinct body with
              | isFalse _ => .error (problemOf .distinct .nothing)
              | isTrue distinct =>
                  match Term.decideUsedOnce (fun τ : V.Ty => Ty.isLinear V τ) body with
                  | isFalse _ => .error (problemOf .linear .nothing)
                  | isTrue linear =>
                      if stops : hdr.canStop = body.canStop then .ok ⟨body, distinct, linear, stops⟩
                      else .error (problemOf .stops (.stops hdr.canStop body.canStop))
            else .error (problemOf .outputs (.types hdr.outs outs))
      else .error (problemOf .inputs (.number hdr.ins.length inputs.length))

/-! ## The printed form of a program -/

/-- What is written for an operation of a protocol. -/
def ProtocolOp.print {hs : Headers V} {ins res : List (LTy V)} : ProtocolOp V hs ins res → ProtocolRaw V
  | .compute R o _ _ _ => .compute R (LocalOp.print o)
  | .flow (τ := τ) kind giver getters _ _ => .event (.flow kind giver getters) τ
  | .given kind owner hearers _ τ _ _ _ => .event (.given kind owner hearers) τ
  | .narrow R _ => .narrow R
  | .apply (hdr := hdr) _ roles _ _ _ _ => .apply hdr.key roles

/-- The printed form of a function. -/
def printFn {fns : List (FnHeader V)} (hdr : FnHeader V) (body : Fn V fns hdr) : Definition V :=
  .fn hdr.key hdr.ins hdr.outs hdr.canStop hdr.kernel
    (printRegion (fun o => LocalOp.print o) (fun _ => ()) body)

/-- The printed form of a protocol. -/
def printProtocol {hs : Headers V} (hdr : ProtocolHeader V) (body : Prot V hs hdr) : Definition V :=
  .protocol hdr.key hdr.roles hdr.ins hdr.outs
    (printRegion (fun o => ProtocolOp.print o) (fun w => w) body)

/-- The printed definitions of a program, in order. -/
def Defs.print : {hs : Headers V} → Defs V hs → List (Definition V)
  | _, .nil => []
  | _, .fn hdr body _ rest => rest.print ++ [printFn hdr body]
  | _, .protocol hdr body _ rest => rest.print ++ [printProtocol hdr body]

/-- The printed form of a typed program: each value has its level as its name. -/
def print (p : Typed V) : NamedProgram V := ⟨p.defs.print⟩

/-! ## The round trip of a function -/

/-- The printed body of a function whose case analyses without an arm give nothing, against
headers with distinct keys, elaborates as the body with its conditions. -/
theorem elabFn_printFn {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup)
    {hdr : FnHeader V} (body : Fn V fns hdr) (ok : FnConditions body) (armed : body.armed = true) :
    elabFn fns hdr (printRegion (fun o => LocalOp.print o) (fun _ => ()) body) = .ok ⟨body, ok⟩ := by
  have elaborated : elabBody (localRules fns) hdr.ins (levels hdr.ins) []
      (printBody (fun o => LocalOp.print o) (fun _ => ()) body).1
      (printBody (fun o => LocalOp.print o) (fun _ => ()) body).2 = .ok ⟨hdr.outs, body⟩ :=
    elabBody_print (localRules fns) (localRules_lawful distinct) body armed []
  simp only [printRegion, elabFn, length_levels, ↓reduceIte, elaborated, ↓reduceDIte, cast_eq,
    Decidable.eq_isTrue (Term.decideDistinct body) ok.distinct,
    Decidable.eq_isTrue (Term.decideUsedOnce (fun τ : V.Ty => Ty.isLinear V τ) body) ok.linear,
    ok.stops]

/-- Elaboration gives a function whose case analyses without an arm give nothing. -/
theorem elabFn_armed {fns : List (FnHeader V)} {hdr : FnHeader V} :
    ∀ (region : Region (LocalRaw V) Unit) {body : Fn V fns hdr} {ok : FnConditions body},
    elabFn fns hdr region = .ok ⟨body, ok⟩ → body.armed = true
  | .mk _ instructions exit, _, _, elaborated => by
      simp only [elabFn] at elaborated
      repeat' split at elaborated
      all_goals first
        | (cases elaborated; done)
        | (cases elaborated
           subst_vars
           simp only [cast_eq]
           exact elabBody_armed (localRules _) instructions exit ‹_›)

end

end Zkc.Core
