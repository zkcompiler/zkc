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

/-- What a role holds of the inputs of a definition, bound to their names, is what it holds of
their values, bound to the same names. -/
theorem restrict_inputs (r : Role) {items : List (LTy V)} (inputs : Names items)
    (vs : HList (LVal M) items) :
    restrict M r (Env.empty.extend inputs vs) = Env.empty.extend inputs (hideAll M r vs) := by
  rw [restrict_extend, restrict_empty]

/-- A role at or above a protocol's roles does nothing while it runs. -/
theorem Defs.quiet : ∀ {hs : Headers V} (defs : Defs V hs), TableQuiet M (Defs.gTable M defs)
  | _, .nil => fun _ p => nomatch p
  | _, .fn _ _ _ _ rest _ => Defs.quiet rest
  | _, .protocol hdr inputs body ok rest => fun _ p j path ins out => by
      cases p with
      | head =>
          have hq := Zkc.Core.quiet M (Defs.fnTable M rest) (Defs.gTable M rest) (r := j)
            (parts := List.range hdr.roles)
            (fun m => absurd out (Nat.not_le.mpr (List.mem_range.mp m)))
            (Defs.quiet rest) body path (Env.empty.extend inputs ins) ok.within
          rw [← Term.observe_fst] at hq
          exact Proj.map_left M (Proj.of_map_left M _ hq) fun _ _ _ => trivial
      | tail p => exact Defs.quiet rest _ p j path ins out

/-- The program of every role of every protocol is a projection of the protocol. -/
theorem Defs.sound : ∀ {hs : Headers V} (defs : Defs V hs),
    TableSound M (Defs.gTable M defs) (Defs.rTable M defs)
  | _, .nil => fun _ p => nomatch p
  | _, .fn _ _ _ _ rest _ => Defs.sound rest
  | _, .protocol _ inputs body ok rest => fun _ p j path ins => by
      cases p with
      | head =>
          have hs' := project_sound M (Defs.fnTable M rest) (Defs.gTable M rest) j
            (Defs.rTable M rest) (Defs.sound rest) (Defs.quiet M rest)
            body path (Env.empty.extend inputs ins) ok.enclosed
          rw [restrict_inputs, ← Term.observe_fst] at hs'
          exact Proj.map_left M (Proj.of_map_left M _ hs')
            (f := fun out => (out.1, cast (congrArg (fun s : Shape V => s.fields.Val M)
              ok.shaped.symm) out.2))
            (post' := fun out rvs => rvs = hideAll M j out.1) fun _ _ e => e
      | tail p => exact Defs.sound rest _ p j path ins

/-- Every role program is a projection of its protocol, on parts of one input. -/
theorem projection (p : Typed V) {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr)
    (r : Role) (path : List Frame) (ins : HList (LVal M) hdr.ins) :
    Proj M r (fun out mine => mine = hideAll M r out.1)
      (protocolMeaning M p x path ins) (roleMeaning M p x r path (hideAll M r ins)) :=
  Defs.sound M p.defs _ x r path ins

end

end Zkc.Core
