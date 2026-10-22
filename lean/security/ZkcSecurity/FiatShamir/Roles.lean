module

public import ZkcSecurity.FiatShamir.Grinding
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Monad.UniformTable

@[expose] public section

/-! Role separation at a fixed key.

Some transcripts derive a proof-of-work test and the challenge it gates from
different calls of one hash function, keyed by the same witness and separated
by distinct tags (domain separation). For a uniformly random function on a
finite input space, the values at distinct role inputs are independent and
uniform (`prEvent_roles`): the tuple of role answers at one key has the product
law. A gate read this way therefore has the law that `gated_escape_le`,
`gated_step_le` and `gated_realized` assume (`prEvent_roles_gate`).

Scope. This is independence at one fixed key. Turning a deployed provider into
one oracle on transcript histories with product answers also needs a
simulation of the whole interaction: the adaptive prover's direct hash calls,
chaining or sponge states shared between calls, collisions between derived
inputs, and the query cost of each grinding attempt. That provider simulation is
a separate obligation of each transcript construction; it is an assumption
wherever these results are used, not a consequence of them.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp

/-- The answers of a uniformly random function at distinct role inputs are
independent and uniform: every event of the role tuple has its uniform
probability. -/
theorem prEvent_roles {X Y Role : Type} [Finite X] [Finite Role] [Finite Y] [Nonempty Y]
    [SampleableType (X → Y)] [SampleableType (Role → Y)] (roles : Role → X)
    (injective : Function.Injective roles) (event : (Role → Y) → Prop) :
    Pr{let table ← $ᵗ (X → Y)}[event (fun role => table (roles role))] =
      Pr{let values ← $ᵗ (Role → Y)}[event values] := by
  let : MeasurableSpace Y := ⊤
  have law := EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective
    ($ᵗ (Role → Y)) ($ᵗ (X → Y)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample injective)
  simpa only [prEvent_map, Function.comp_def] using law.prEvent_eq event

/-- A gate read from two distinct inputs of a uniformly random function, the
test at `test` and the challenge at `challenge`, has the law of a uniform pair:
every event of the two answers has its probability under `$ᵗ (Y × Y)`. -/
theorem prEvent_roles_gate {X Y : Type} [Finite X] [Fintype Y] [Nonempty Y]
    [SampleableType Y] [SampleableType (X → Y)] (test challenge : X) (distinct : test ≠ challenge)
    (event : Y × Y → Prop) :
    Pr{let table ← $ᵗ (X → Y)}[event (table test, table challenge)] =
      Pr{let pair ← $ᵗ (Y × Y)}[event pair] := by
  classical
  have roles := prEvent_roles (Role := Bool) (fun role => if role then challenge else test)
    (by
      intro first second same
      cases first <;> cases second <;> simp_all [eq_comm])
    (fun values => event (values false, values true))
  simp only [Bool.false_eq_true, ↓reduceIte] at roles
  rw [roles]
  exact prEvent_of_bijective (decode := fun values : Bool → Y => (values false, values true))
    ⟨fun first second same => by
        funext role
        cases role
        · exact (Prod.ext_iff.mp same).1
        · exact (Prod.ext_iff.mp same).2,
      fun pair => ⟨fun role => if role then pair.2 else pair.1, by simp⟩⟩ event

end ZkcSecurity.FiatShamir
