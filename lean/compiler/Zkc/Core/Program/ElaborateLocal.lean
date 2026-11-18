module

public import Zkc.Core.Program.LocalRules
public import Zkc.Core.Program.Conditions

@[expose] public section

/-!
The elaboration of a function, its erased form, and their round trip in both directions.

A function's body is elaborated by the local rules in the context of its inputs, by the names
that its region gives them, once the positions that the summary of its header names are found to
be within its inputs, and for a guarantee its inputs and results (`Summary.InRange`); its results
are the header's; its instructions have their own
addresses; every name is bound at one place; its linear values are used once; its header says
whether it can stop with a reason as its body does (a guard, or a call of a function that can);
and its case analyses without an arm give nothing, which elaboration gives by construction.

The erased form of a typed function, against headers with distinct keys, elaborates as its input
names, its body and what elaboration decided about it (`elabFn_erase`); a function that
elaboration gives erases to the region that was elaborated (`eraseFn_elab`).
-/

namespace Zkc.Core

/-- A value of a linear type that is not used as it must be, as a refusal of the definition:
at the instruction of the place, or at the definition for an input; a value bound there by its
name (`uses`), a value from around the place by its name (`around`). -/
def Misuse.refusal {T Raw : Type} (definition : Key) (misuse : Misuse) : Refusal T Raw :=
  let detail : Detail T Raw := cond misuse.around (.around misuse.name misuse.found)
    (.uses misuse.name misuse.found)
  match misuse.instruction with
  | some key => refuseAt definition misuse.blocks key .linear detail
  | none => refuseWhole definition .linear detail

/-- A name bound a second time, as a refusal of the definition: at the instruction that binds
it again, or at the definition when no instruction does. -/
def reboundRefusal {T Raw : Type} (definition : Key) (place : Option (List (Key × Nat) × Key))
    (name : Name) : Refusal T Raw :=
  match place with
  | some (blocks, key) => refuseAt definition blocks key .assignment (.name name)
  | none => refuseWhole definition .assignment (.name name)

section
variable {V : Vocabulary}

/-- The body of a function by names, with the names of its inputs and what elaboration decides
about it, against the headers of the functions before it. The summary of its header is checked
first: a requirement that names a position beyond the inputs, or a guarantee one beyond the inputs
and the results, is refused at the definition by the rule `summary`. -/
def elabFn (fns : List (FnHeader V)) (hdr : FnHeader V) :
    Region (LocalRaw V) Unit →
      Except (ProgramRefusal V)
        ((inputs : Names hdr.ins) × (body : Fn V fns hdr inputs) ×' FnConditions body)
  | .mk inputs instructions exit =>
      match placed : hdr.summary.misplaced hdr.ins.length hdr.outs.length,
          Names.ofList hdr.ins inputs with
      | some requirement, _ =>
          .error (refuseWhole hdr.key .summary (.requirement requirement.lift))
      | none, none => .error (refuseWhole hdr.key .inputs (.number hdr.ins.length inputs.length))
      | none, some bound =>
          match elaborated : elabBody (localRules fns) hdr.key (Ctx.empty.extend bound) [] none
              instructions exit with
          | .error refusal => .error refusal
          | .ok ⟨outs, t⟩ =>
              if same : outs = hdr.outs then
                let body : Fn V fns hdr bound :=
                  cast (congrArg (Term (localDialect V fns) (Ctx.empty.extend bound)) same) t
                have armed : body.armed = true := by
                  subst same
                  exact elabBody_armed (localRules fns) instructions exit elaborated
                match repeated : body.repeatedAddress with
                | some (blocks, key) => .error (refuseAt hdr.key blocks key .distinct .nothing)
                | none =>
                    match rebound : body.rebound bound.toList with
                    | some name =>
                        .error (reboundRefusal hdr.key (body.reboundPlace bound.toList) name)
                    | none =>
                        match misused : body.misuse (fun τ : V.Ty => Ty.isLinear V τ) bound with
                        | some misuse => .error (misuse.refusal hdr.key)
                        | none =>
                            if stops : hdr.canStop = body.canStop then
                              .ok ⟨bound, body, (Term.repeatedAddress_eq_none body).mp repeated,
                                by exact misused, stops, armed,
                                (Term.rebound_eq_none bound.toList body).mp rebound, placed⟩
                            else
                              .error (refuseWhole hdr.key .stops (.stops hdr.canStop body.canStop))
              else .error (refuseWhole hdr.key .outputs (.types hdr.outs outs))

/-- The erased form of a function's body: the names of its inputs, its instructions and its
exit. -/
def eraseFn {fns : List (FnHeader V)} {hdr : FnHeader V} (inputs : Names hdr.ins)
    (body : Fn V fns hdr inputs) : Region (LocalRaw V) Unit :=
  let erased := eraseBody (fun o => LocalOp.print o) (fun _ => ()) body
  .mk inputs.toList erased.1 erased.2

/-- The round trip of a function, erased then elaborated: the erased form of a typed function,
against headers with distinct keys, elaborates as its input names, its body and what
elaboration decided about it. -/
theorem elabFn_erase {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup)
    {hdr : FnHeader V} (inputs : Names hdr.ins) (body : Fn V fns hdr inputs)
    (ok : FnConditions body) :
    elabFn fns hdr (eraseFn inputs body) = .ok ⟨inputs, body, ok⟩ := by
  have elaborated : elabBody (localRules fns) hdr.key (Ctx.empty.extend inputs) [] none
      (eraseBody (fun o => LocalOp.print o) (fun _ => ()) body).1
      (eraseBody (fun o => LocalOp.print o) (fun _ => ()) body).2 = .ok ⟨hdr.outs, body⟩ :=
    elabBody_erase (localRules fns) (localRules_lawful distinct) hdr.key body ok.armed [] none
  have repeated := (Term.repeatedAddress_eq_none body).mpr ok.distinct
  have rebound := (Term.rebound_eq_none inputs.toList body).mpr ok.once
  have misused : body.misuse (fun τ : V.Ty => Ty.isLinear V τ) inputs = none := ok.linear
  have placed : hdr.summary.misplaced hdr.ins.length hdr.outs.length = none := ok.summary
  simp only [eraseFn, elabFn, Names.ofList_toList]
  split
  · rename_i requirement found
    rw [placed] at found
    cases found
  · rename_i none
    cases none
  · rename_i bound _ named
    cases named
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
        · rename_i name found
          rw [rebound] at found
          cases found
        · split
          · rename_i misuse found
            rw [misused] at found
            cases found
          · simp only [ok.stops, ↓reduceDIte]

/-- The round trip of a function, elaborated then erased: a function that elaboration gives
erases to the region that was elaborated. -/
theorem eraseFn_elab {fns : List (FnHeader V)} {hdr : FnHeader V}
    (region : Region (LocalRaw V) Unit) {inputs : Names hdr.ins} {body : Fn V fns hdr inputs}
    {ok : FnConditions body}
    (elaborated : elabFn fns hdr region = .ok ⟨inputs, body, ok⟩) :
    eraseFn inputs body = region := by
  obtain ⟨names, instructions, exit⟩ := region
  simp only [elabFn] at elaborated
  split at elaborated
  · cases elaborated
  · cases elaborated
  · rename_i bound named
    split at elaborated
    · cases elaborated
    · rename_i outs t found
      split at elaborated
      · rename_i same
        subst same
        have erased : eraseBody (fun o => LocalOp.print o) (fun _ => ()) t =
            (instructions, exit) :=
          eraseBody_elab (localRules fns) localRules_canonical hdr.key instructions exit [] none t
            found
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [eraseFn, cast_eq, erased, Names.toList_of_ofList hdr.ins names _ named])
      · cases elaborated

end

end Zkc.Core
