module

public import Zkc.Core.Program.LocalRules
public import Zkc.Core.Program.Conditions

@[expose] public section

/-!
The elaboration of a function, its printed form, and their round trip.

A function's body is elaborated by the local rules in the context of its inputs, with the names
of the body's inputs in scope; its results are the header's; its instructions have their own
addresses; its linear values are used once; its header says whether it can stop with a reason
as its body does (a guard, or a call of a function that can); and its case analyses without an
arm give nothing, which elaboration gives by construction.
-/

namespace Zkc.Core

/-- A value of a linear type that is not used once, as a refusal of the definition: at the
instruction that binds it, or at the definition for an input. -/
def Misuse.refusal {T Raw : Type} (definition : Key) (misuse : Misuse) : Refusal T Raw :=
  match misuse.instruction with
  | some key => refuseAt definition misuse.blocks key .linear (.uses misuse.position misuse.found)
  | none => refuseWhole definition .linear (.uses misuse.position misuse.found)

section
variable {V : Vocabulary}

/-- The body of a function by names, with what elaboration decides about it, against the
headers of the functions before it. -/
def elabFn (fns : List (FnHeader V)) (hdr : FnHeader V) :
    Region (LocalRaw V) Unit →
      Except (ProgramRefusal V) ((body : Fn V fns hdr) ×' FnConditions body)
  | .mk inputs instructions exit =>
      if inputs.length = hdr.ins.length then
        match elaborated :
            elabBody (localRules fns) hdr.key hdr.ins inputs [] none instructions exit with
        | .error refusal => .error refusal
        | .ok ⟨outs, t⟩ =>
            if same : outs = hdr.outs then
              let body : Fn V fns hdr := cast (congrArg (Term (localDialect V fns) hdr.ins) same) t
              have armed : body.armed = true := by
                subst same
                exact elabBody_armed (localRules fns) instructions exit elaborated
              match repeated : body.repeatedAddress with
              | some (blocks, key) => .error (refuseAt hdr.key blocks key .distinct .nothing)
              | none =>
                  match misused : body.misuse (fun τ : V.Ty => Ty.isLinear V τ) with
                  | some misuse => .error (misuse.refusal hdr.key)
                  | none =>
                      if stops : hdr.canStop = body.canStop then
                        .ok ⟨body, (Term.repeatedAddress_eq_none body).mp repeated,
                          (Term.misuse_eq_none _ body).mp misused, stops, armed⟩
                      else .error (refuseWhole hdr.key .stops (.stops hdr.canStop body.canStop))
            else .error (refuseWhole hdr.key .outputs (.types hdr.outs outs))
      else .error (refuseWhole hdr.key .inputs (.number hdr.ins.length inputs.length))

/-- The printed form of a function. -/
def printFn {fns : List (FnHeader V)} (hdr : FnHeader V) (body : Fn V fns hdr) : Definition V :=
  .fn hdr.key hdr.ins hdr.outs hdr.canStop hdr.kernel
    (printRegion (fun o => LocalOp.print o) (fun _ => ()) body)

/-- The round trip of a function: the printed body of a typed function, against headers with
distinct keys, elaborates as the body with what elaboration decided about it. -/
theorem elabFn_printFn {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup)
    {hdr : FnHeader V} (body : Fn V fns hdr) (ok : FnConditions body) :
    elabFn fns hdr (printRegion (fun o => LocalOp.print o) (fun _ => ()) body) =
      .ok ⟨body, ok⟩ := by
  have elaborated : elabBody (localRules fns) hdr.key hdr.ins (levels hdr.ins) [] none
      (printBody (fun o => LocalOp.print o) (fun _ => ()) body).1
      (printBody (fun o => LocalOp.print o) (fun _ => ()) body).2 = .ok ⟨hdr.outs, body⟩ :=
    elabBody_print (localRules fns) (localRules_lawful distinct) hdr.key body ok.armed [] none
  have repeated := (Term.repeatedAddress_eq_none body).mpr ok.distinct
  have misused := (Term.misuse_eq_none (fun τ : V.Ty => Ty.isLinear V τ) body).mpr ok.linear
  simp only [printRegion, elabFn, length_levels, ↓reduceIte]
  split
  · rename_i refusal found
    rw [elaborated] at found
    cases found
  · rename_i outs t found
    rw [elaborated] at found
    cases found
    simp only [↓reduceDIte, cast_eq]
    split
    · rename_i blocks key found
      rw [repeated] at found
      cases found
    · split
      · rename_i misuse found
        rw [misused] at found
        cases found
      · simp only [ok.stops, ↓reduceDIte]

end

end Zkc.Core
