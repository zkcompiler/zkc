module

public import Zkc.Core.Program.ElaborateLocal
public import Zkc.Core.Program.ProtocolScopes

@[expose] public section

/-! Elaboration of a named protocol. Its body determines the event shape stored in the header.
Located operand types and participant identities are retained in the diagnostic type. -/

namespace Zkc.Core

section
variable {V : Vocabulary}

abbrev ProtocolRefusal (V : Vocabulary) := Refusal (LTy V) (ProtocolRaw V)

/-- A protocol elaborated against preceding headers. The stored shape is computed from
the same body that supplies the projection and its execution. -/
structure TypedProtocol (hs : Headers V) (key : Key) (roles : Nat)
    (ins outs : List (LTy V)) where
  inputs : Names ins
  body : Term (protocolDialect V hs) (Ctx.empty.extend inputs) outs
  conditions : ProtocolConditions ⟨key, roles, ins, outs, shapeOf body⟩ body

/-- The erased form of a protocol's body: the names of its ports, its instructions and its
exit. -/
def eraseProtocol {hs : Headers V} {hdr : ProtocolHeader V} (inputs : Names hdr.ins)
    (body : Prot V hs hdr inputs) : Region (ProtocolRaw V) (List Role) :=
  let erased := eraseBody (fun o => ProtocolOp.print o) (fun w => w) body
  .mk inputs.toList erased.1 erased.2

def elabProtocol (hs : Headers V) (key : Key) (roles : Nat) (ins outs : List (LTy V)) :
    Region (ProtocolRaw V) (List Role) →
      Except (ProtocolRefusal V) (TypedProtocol hs key roles ins outs)
  | .mk names instructions exit =>
      match Names.ofList ins names with
      | none => .error (refuseWhole key .inputs (.number ins.length names.length))
      | some bound =>
          match found : elabBody (protocolRules hs) key (Ctx.empty.extend bound) [] none
              instructions exit with
          | .error refusal => .error refusal
          | .ok ⟨result, term⟩ =>
              if same : result = outs then
                let body := cast (congrArg (Term (protocolDialect V hs) (Ctx.empty.extend bound))
                  same) term
                have armed : body.armed = true := by
                  subst same
                  exact elabBody_armed (protocolRules hs) instructions exit found
                match repeated : body.repeatedAddress with
                | some (blocks, address) => .error (refuseAt key blocks address .distinct .nothing)
                | none =>
                    match rebound : body.rebound bound.toList with
                    | some name => .error (reboundRefusal key (body.reboundPlace bound.toList) name)
                    | none =>
                        match misused : body.misuse (fun a : LTy V => Ty.isLinear V a.ty) bound with
                        | some misuse => .error (misuse.refusal key)
                        | none =>
                          letI := decideWithin (List.range roles) body
                          letI := decideEnclosed body
                          if located : ∀ a ∈ ins ++ outs, ∀ r ∈ a.holders, r < roles then
                            if participants : Within (List.range roles) body then
                              if enclosed : Enclosed body then
                                .ok ⟨bound, body, participants, located, enclosed,
                                  (Term.repeatedAddress_eq_none body).mp repeated, rfl, misused,
                                  armed, (Term.rebound_eq_none bound.toList body).mp rebound⟩
                              else .error (refuseWhole key .enclosed .nothing)
                            else .error (refuseWhole key .participants .nothing)
                          else .error (refuseWhole key .portHolders (.given (ins ++ outs)))
              else .error (refuseWhole key .outputs (.types outs result))

/-- Every typed protocol can be read back with the exact body and port names. The shape
recorded by the producer follows from the existing formation conditions. -/
theorem elabProtocol_erase {hs : Headers V} (distinct : hs.keys.Nodup) {hdr : ProtocolHeader V}
    (inputs : Names hdr.ins) (body : Prot V hs hdr inputs) (ok : ProtocolConditions hdr body) :
    ∃ typed, elabProtocol hs hdr.key hdr.roles hdr.ins hdr.outs (eraseProtocol inputs body) =
        .ok typed ∧ typed.inputs = inputs ∧ HEq typed.body body := by
  obtain ⟨key, roles, ins, outs, shape⟩ := hdr
  have read : elabBody (protocolRules hs) key (Ctx.empty.extend inputs) [] none
      (eraseBody (fun o => ProtocolOp.print o) (fun w => w) body).1
      (eraseBody (fun o => ProtocolOp.print o) (fun w => w) body).2 = .ok ⟨outs, body⟩ :=
    elabBody_erase (protocolRules hs) (protocolRules_lawful distinct) key body
    ok.armed [] none
  have unique := (Term.repeatedAddress_eq_none body).mpr ok.distinct
  have names := (Term.rebound_eq_none inputs.toList body).mpr ok.once
  have linear := ok.linear
  obtain ⟨inside, located, enclosed, _, _, _, armed, _⟩ := ok
  refine ⟨⟨inputs, body, inside, located, enclosed, (Term.repeatedAddress_eq_none body).mp unique,
    rfl, linear, armed, (Term.rebound_eq_none inputs.toList body).mp names⟩, ?_, rfl, HEq.rfl⟩
  simp only [eraseProtocol, elabProtocol, Names.ofList_toList]
  split
  · rename_i refusal failed; rw [read] at failed; cases failed
  · rename_i outs' t built; rw [read] at built; cases built
    simp only [↓reduceDIte, cast_eq]
    split
    · rename_i _ _ repeated; rw [unique] at repeated; cases repeated
    · split
      · rename_i _ duplicate; rw [names] at duplicate; cases duplicate
      · split
        · rename_i _ misuse; rw [linear] at misuse; cases misuse
        · rw [dite_eq_left located, dite_eq_left inside, dite_eq_left enclosed]

/-- Every successfully read body prints as the complete named region supplied by the caller. -/
theorem eraseProtocol_elab {hs : Headers V} {key : Key} {roles : Nat} {ins outs : List (LTy V)}
    (region : Region (ProtocolRaw V) (List Role)) {typed : TypedProtocol hs key roles ins outs}
    (built : elabProtocol hs key roles ins outs region = .ok typed) :
    eraseProtocol (hdr := ⟨key, roles, ins, outs, shapeOf typed.body⟩) typed.inputs typed.body =
      region := by
  obtain ⟨names, instructions, exit⟩ := region
  simp only [elabProtocol] at built
  split at built
  · cases built
  · rename_i bound named
    split at built
    · cases built
    · rename_i res t found
      split at built
      · rename_i same
        subst same
        have erased : eraseBody (fun o => ProtocolOp.print o) (fun w => w) t = (instructions, exit) :=
          eraseBody_elab (protocolRules hs) protocolRules_canonical key instructions exit [] none t
            found
        repeat' split at built
        all_goals first
          | (cases built; done)
          | (cases built
             simpa only [eraseProtocol, cast_eq, Names.toList_of_ofList ins names _ named] using
               congrArg (fun pair => Region.mk names pair.1 pair.2) erased)
      · cases built


end

end Zkc.Core
