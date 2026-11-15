module

public import Zkc.Core.Meaning.Program
public import Zkc.Core.Projection.Sound

@[expose] public section

/-!
The projection theorem for every definition of a program: the program of every role of every
protocol is a projection of the protocol.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

theorem restrict_ofList (r : Role) : ∀ {Γ : List (LTy V)} (vs : HList (LVal M) Γ),
    restrict M r (Env.ofList vs) = Env.ofList (hideAll M r vs)
  | [], .nil => by
      funext a x
      nomatch x
  | _ :: _, .cons v rest => by
      funext a x
      cases x with
      | head => rfl
      | tail x => exact congrFun (congrFun (restrict_ofList r rest) a) x

/-- A role at or above a protocol's roles does nothing while it runs. -/
theorem Defs.quiet : ∀ {hs : Headers V} (defs : Defs V hs), TableQuiet M (Defs.gTable M defs)
  | _, .nil => fun _ p => nomatch p
  | _, .fn _ _ _ rest => Defs.quiet rest
  | _, .protocol hdr body ok rest => fun _ p j path ins out => by
      cases p with
      | head =>
          have hq := Zkc.Core.quiet M (Defs.fnTable M rest) (Defs.gTable M rest) (r := j)
            (parts := List.range hdr.roles)
            (fun m => absurd out (Nat.not_le.mpr (List.mem_range.mp m)))
            (Defs.quiet rest) body path (Env.ofList ins) ok.within
          rw [← Term.observe_fst] at hq
          exact Proj.map_left M (Proj.of_map_left M _ hq) fun _ _ _ => trivial
      | tail p => exact Defs.quiet rest _ p j path ins out

/-- The program of every role of every protocol is a projection of the protocol. -/
theorem Defs.sound : ∀ {hs : Headers V} (defs : Defs V hs),
    TableSound M (Defs.gTable M defs) (Defs.rTable M defs)
  | _, .nil => fun _ p => nomatch p
  | _, .fn _ _ _ rest => Defs.sound rest
  | _, .protocol hdr body ok rest => fun _ p j path ins => by
      cases p with
      | head =>
          have hs' := project_sound M (Defs.fnTable M rest) (Defs.gTable M rest) j
            (Defs.rTable M rest) (Defs.sound rest) (Defs.quiet M rest)
            body path (Env.ofList ins) ok.enclosed
          rw [restrict_ofList, ← Term.observe_fst] at hs'
          exact Proj.map_left M (Proj.of_map_left M _ hs')
            (f := fun out => (out.1, cast (congrArg (fun s : Shape V => s.fields.Val M)
              ok.shaped.symm) out.2))
            (post' := fun out rvs => rvs = hideAll M j out.1) fun _ _ e => e
      | tail p => exact Defs.sound rest _ p j path ins

/-- Every role program is a projection of its protocol, on parts of one input. -/
theorem projection (p : Typed V) {hdr : ProtocolHeader V} (x : Var p.headers.protocols hdr)
    (r : Role) (path : List Frame) (ins : HList (LVal M) hdr.ins) :
    Proj M r (fun out mine => mine = hideAll M r out.1)
      (protocolMeaning M p x path ins) (roleMeaning M p x r path (hideAll M r ins)) :=
  Defs.sound M p.defs _ x r path ins

end

end Zkc.Core

#print axioms Zkc.Core.Defs.quiet
#print axioms Zkc.Core.Defs.sound
#print axioms Zkc.Core.projection
