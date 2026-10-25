module

public import ZkcSecurity.Families.Sumcheck.TableReference
public import ZkcSecurity.Families.Sumcheck.Composition

@[expose] public section

/-! A list representation of the installed degree-one table component.

The implementation state is deliberately unrestricted: callers retain their
captures, private results, original input and dynamic prefix there. Exact shape
is a representation law at the remaining dimension, independent of scalar
truth. Both consumers use the same decoded table and Process equation.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [Field F] {I : PIR.Signature} {Context : Type}
  {State : Nat → Type}

/-- This law concerns the actual update selected by `program`. It never
constrains received messages to be honest or assumes the initial claim. -/
structure Layout (program : Program I Context State (Message.endpoints F)) where
  entries : {n : Nat} → State n → List F
  shape : ∀ {n} (s : State n), (entries s).length = 2 ^ n
  advance : ∀ {n} (context : Context) (s : State (n + 1)) m r,
    entries (program.advance context s m r) = restrictValues (entries s) r
  claim : ∀ {n} (context : Context) (s : State (n + 1)) m r,
    program.claim (program.advance context s m r) = (Message.endpoints F).evaluate m r

namespace Layout
variable {program : Program I Context State (Message.endpoints F)} (layout : Layout program)

/-- Decoding is total on exact shape, including every false scalar claim. -/
noncomputable def table {n : Nat} (s : State n) : Table F n :=
  (ofList? n (layout.entries s)).get ((ofList?_isSome_iff _).mpr (layout.shape s))

theorem decoded {n : Nat} (s : State n) :
    ofList? n (layout.entries s) = some (layout.table s) := by
  exact (Option.some_get ((ofList?_isSome_iff _).mpr (layout.shape s))).symm

theorem total {n : Nat} (s : State n) :
    (TableReference.data F).total (layout.table s) = (layout.entries s).sum :=
  booleanSum_ofList? _ _ (layout.decoded s)

theorem restrict {n : Nat} (context : Context) (s : State (n + 1)) m r :
    layout.table (program.advance context s m r) =
      (TableReference.data F).restrict (layout.table s) r := by
  apply Option.some.inj
  rw [← layout.decoded, layout.advance]
  exact ofList?_restrictValues _ _ r (layout.decoded s)

/-- One representation object is consumed by both honest equality and
adversarial inequality. Its state includes the entire caller-owned frame. -/
noncomputable def representation : Representation program (TableReference.data F) where
  state := layout.table
  advance := layout.restrict
  claim := layout.claim

theorem yes_iff {n : Nat} (s : State n) :
    layout.representation.Yes s ↔ program.claim s = (layout.entries s).sum := by
  change (True ∧ program.claim s = (TableReference.data F).total (layout.table s)) ↔ _
  rw [layout.total, true_and]

theorem no_iff {n : Nat} (s : State n) :
    layout.representation.No s ↔ program.claim s ≠ (layout.entries s).sum := by
  change (True ∧ program.claim s ≠ (TableReference.data F).total (layout.table s)) ↔ _
  rw [layout.total, true_and]

/-- The implementation's actual half-sum expression has the reference's
polynomial meaning. The equality is about decoded data, not a helper name. -/
theorem honest_endpoints {n : Nat} (s : State (n + 1)) :
    (((layout.entries s).take ((layout.entries s).length / 2)).sum,
      ((layout.entries s).drop ((layout.entries s).length / 2)).sum) =
        Zkc.Protocols.Sumcheck.Multilinear.honestMessage (layout.table s) := by
  exact Prod.ext
    (booleanSum_ofList? _ _ (decode_low_half _ _ (layout.decoded s))).symm
    (booleanSum_ofList? _ _ (decode_high_half _ _ (layout.decoded s))).symm

/-- A source producer needs an exact expression/delivery law. This theorem
then supplies the installed polynomial law without a second reference. -/
theorem honest_message {H : Type}
    (ready : Nat → {n : Nat} → Context → State (n + 1) → (F × F) → H → Prop)
    (delivered : ∀ count {n} (context : Context) (s : State (n + 1)) m h,
      ready count context s m h → m =
        (((layout.entries s).take ((layout.entries s).length / 2)).sum,
          ((layout.entries s).drop ((layout.entries s).length / 2)).sum)) :
    ∀ count {n} (context : Context) (s : State (n + 1)) m h,
      ready count context s m h →
      (Message.endpoints F).polynomial m =
        (TableReference.data F).polynomial (layout.representation.state s) := by
  intro count n context s m h reached
  rw [delivered count context s m h reached, layout.honest_endpoints]
  exact TableReference.honest_polynomial _

/-- A terminal zero-dimensional table is the actual unique represented entry.
The caller still proves its source checker computes this equality. -/
theorem terminal_entries (s : State 0) :
    layout.entries s = [(TableReference.data F).total (layout.table s)] := by
  obtain ⟨value, same⟩ := List.length_eq_one_iff.mp (by simpa using layout.shape s)
  rw [layout.total, same, List.sum_singleton]

end Layout
end ZkcSecurity.Families.Sumcheck.TableComponent
