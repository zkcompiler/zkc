module

public import ZkcFormal.Form.Computation
public import ZkcFormal.Written.Contract
public import PolyFun.PFunctor.Free.Do
public import Std.Tactic.Do

@[expose] public section

/-!
The judgment by fees on the reading of a process, for the standard generator of verification
conditions.

A role's process, read as a computation that may stop (`Reading.read`), has the standard weakest
precondition of the judgment by fees: under a context (the draws of the laws and an allowance of
occurrences) the weakest precondition of the reading of a process is the judgment of the
process (`fold_read`), the budget being the state that a condition reads. So a triple proved on
the reading by Lean's `vcgen` is a judgment by fees of the process (`judged_of_triple`).

There is one rule for each effect of a role, and no two apply to one effect. A coin of the
role's own (`coin`) is where a fee is paid: the rule takes the fee and the excluded replies as
one value of a type that the generator returns as a goal for the user to fill (`DrawChoice`),
indexed by the occurrence of the coin, so that a tool finds the goal of a draw by where the draw
occurs. Every other effect, a request to a service among them, excludes nothing and costs
nothing. A computation without effects is judged by what it returns or how it stops
(`lifted_option`, `lifted_local`). A call is judged from a contract of its callee that holds
(`call`), under the renaming of the callee's roles (`renamed_spec`).

The instance is scoped: it is the judgment by fees, and another judgment of the same
computations (the value, a trace) is another instance.
-/

namespace ZkcFormal.Written.FeeRules
open Zkc.Core ProbabilisticProcess Reading Form Std.WP
open scoped NNRat

/-- What a condition of the judgment by fees reads: the budget that is left. -/
abbrev Credit := ℚ≥0 → Prop

/-- Under which fees a computation is judged: the draws of the laws, and what each occurrence of
an effect may be charged at most. -/
class Context {V : Vocabulary} (M : Model V) where
  draws : LawDraws M
  allowance : Occurrence → ℚ≥0

variable {V : Vocabulary} {M : Model V} [c : Context M]

/-- The judgment by fees of a context. -/
abbrev judgment (c : Context M) : ProcessJudgment (RSig M) Credit :=
  Fees.judgment c.draws c.allowance

/-- The judgment by fees at one effect, as the specification of an operation. -/
def ops (c : Context M) : PFunctor.OpSpec (specOf (RSig M)).toPFunctor Credit :=
  (judgment c).node

theorem ops_monotone : (ops c).Monotone := by
  rintro op k l weaker budget ⟨fee, excluded, within, pays, next⟩
  exact ⟨fee, excluded, within, pays, fun reply ok kept => weaker reply _ (next reply ok kept)⟩

/-- The weakest precondition of the judgment by fees, on computations over a role's effects. -/
scoped instance base : WPMonad (OracleComp (specOf (RSig M))) Credit EStack⟨⟩ :=
  (ops c).toWPMonad ops_monotone

/-- What a judgment of soundness asks of a stop: nothing. -/
abbrev stopped : (Stop → Credit) × EStack⟨⟩ := (fun _ _ => True, ())

/-- **The weakest precondition of a reading is the judgment of the process.** -/
theorem fold_read {A : Type} (p : Program M A) (Q : A → Credit) (E : (Stop → Credit) × EStack⟨⟩) :
    wp (read p) Q E = p.interpret (judgment c) Q E.1 := by
  rw [ExceptT.wp_apply_eq, PFunctor.OpSpec.toWPMonad_wp]
  induction p with
  | done | halt => rfl
  | call op next ih =>
    change (judgment c).node op _ = (judgment c).node op _
    exact congrArg _ (funext ih)

omit c in
/-- **A triple on the reading is a judgment of the process.** Where a computation is the reading
of a process, a triple of it from the budgets of at least `budget` is the judgment by fees of
the process within `budget`. -/
theorem judged_of_triple {A : Type} (c : Context M) (p : Program M A) (form : Comp (RSig M) Stop A)
    (reads : read p = form) (budget : ℚ≥0) (Q : A → Credit) (E : (Stop → Credit) × EStack⟨⟩)
    (proved : letI := c; Triple form (fun left => budget ≤ left) Q E) :
    p.interpret (judgment c) Q E.1 budget := by
  let := c
  rw [← fold_read (E := E), reads]
  exact proved.1 _ le_rfl

/-! ## The rule of each effect -/

/-- **What is decided at a charged draw**: the fee, and the replies that it excludes. The
generator hands a value of this type back as a goal, as it does a loop's invariant; the type
names the occurrence of the draw, so the goal of a draw is found by where the draw occurs. -/
@[spec_invariant_type]
structure DrawChoice (at_ : Occurrence) (α : Type) where
  fee : ℚ≥0
  excluded : α → Prop

/-- An effect at which nothing is excluded: every permitted reply goes on with the budget. -/
theorem free (op : ROp M) (Q : (RSig M).Reply op → Credit) {E} :
    Triple (ask (RSig M) Stop op) (fun left => ∀ reply, Permitted M op reply → Q reply left) Q E := by
  constructor
  intro left holds
  refine ⟨0, fun _ => False, zero_le, ⟨Or.inl ⟨rfl, fun _ no => no⟩, zero_le⟩, ?_⟩
  intro reply ok _
  change Q reply (left - 0)
  simpa using holds reply ok

/-- **A coin of the role's own**: a fee, paid by the sampler of the coin within what the
occurrence is allowed, excludes a set of replies; every other permitted reply goes on with what
the fee leaves. -/
@[spec] theorem coin (law : V.LawKey) (peers : List Role) (at_ : Occurrence) (takes values ty)
    (choice : DrawChoice at_ (M.Val ty)) (Q : M.Val ty → Credit) {E} :
    let op := ROp.own (M := M) (.coin law) peers at_ takes values ty
    Triple (ask (RSig M) Stop op) (fun left => choice.fee ≤ left ∧
      paysWithin (lawSamplers M c.draws) (fun op => c.allowance (ROp.occurrence M op)) op
        choice.fee choice.excluded ∧
      ∀ reply, Permitted M op reply → ¬ choice.excluded reply → Q reply (left - choice.fee)) Q E :=
  ⟨fun _ ⟨within, pays, next⟩ => ⟨choice.fee, choice.excluded, within, pays, next⟩⟩

/-- **A request of the role's own to a service**: no law draws its reply, so no fee excludes
one, and every permitted reply goes on with the budget. -/
@[spec] theorem request (service : Key) (peers : List Role) (at_ : Occurrence) (takes values ty)
    (Q : M.Val ty → Credit) {E} :
    Triple (ask (RSig M) Stop (ROp.own (M := M) (.request service) peers at_ takes values ty))
      (fun left => ∀ reply,
        Permitted M (ROp.own (M := M) (.request service) peers at_ takes values ty) reply →
          Q reply left) Q E :=
  free _ _

@[spec] theorem get (kind role at_ ty) (Q : (RSig M).Reply (ROp.get (M := M) kind role at_ ty) → Credit)
    {E} :
    Triple (ask (RSig M) Stop (ROp.get (M := M) kind role at_ ty))
      (fun left => ∀ reply, Permitted M (ROp.get (M := M) kind role at_ ty) reply → Q reply left) Q E :=
  free _ _

@[spec] theorem give (kind peers at_ ty value)
    (Q : (RSig M).Reply (ROp.give (M := M) kind peers at_ ty value) → Credit) {E} :
    Triple (ask (RSig M) Stop (ROp.give (M := M) kind peers at_ ty value))
      (fun left => ∀ reply, Permitted M (ROp.give (M := M) kind peers at_ ty value) reply →
        Q reply left) Q E :=
  free _ _

@[spec] theorem hear (kind role at_ ty)
    (Q : (RSig M).Reply (ROp.hear (M := M) kind role at_ ty) → Credit) {E} :
    Triple (ask (RSig M) Stop (ROp.hear (M := M) kind role at_ ty))
      (fun left => ∀ reply, Permitted M (ROp.hear (M := M) kind role at_ ty) reply → Q reply left) Q E :=
  free _ _

@[spec] theorem «begin» (at_) (Q : (RSig M).Reply (ROp.begin (M := M) at_) → Credit) {E} :
    Triple (ask (RSig M) Stop (ROp.begin (M := M) at_))
      (fun left => ∀ reply, Permitted M (ROp.begin (M := M) at_) reply → Q reply left) Q E :=
  free _ _

@[spec] theorem settle (at_) (Q : (RSig M).Reply (ROp.settle (M := M) at_) → Credit) {E} :
    Triple (ask (RSig M) Stop (ROp.settle (M := M) at_))
      (fun left => ∀ reply, Permitted M (ROp.settle (M := M) at_) reply → Q reply left) Q E :=
  free _ _

/-! ## A computation without effects -/

/-- A value or a stop among a role's effects: the value goes on with the budget, and a stop is
what the judgment asks of a stop. -/
@[spec] theorem lifted_option {A B : Type} (o : Option A) (f : A → B) (stop : Stop → Stop)
    (Q : B → Credit) {E} :
    Triple (liftEmpty (RSig M) stop (optionE o f))
      (fun left => (∀ a, o = some a → Q (f a) left) ∧ (o = none → E.1 (stop .undefined) left))
      Q E := by
  constructor
  cases o <;> intro left holds
  · exact holds.2 rfl
  · exact holds.1 _ rfl

/-- A local process among a role's effects, by what it is: where it returns a value the value
goes on, and where it stops the judgment's condition on a stop is asked. An equation that says
what a function of the source computes is used here. -/
@[spec] theorem lifted_local {A : Type} (p : Local A) (stop : Stop → Stop) (Q : A → Credit) {E} :
    Triple (liftEmpty (RSig M) stop (read p))
      (fun left => (∀ a, p = .done a → Q a left) ∧ (∀ why, p = .halt why → E.1 (stop why) left))
      Q E := by
  constructor
  cases p with
  | done _ => exact fun _ holds => holds.1 _ rfl
  | halt _ => exact fun _ holds => holds.2 _ rfl
  | call op => exact nomatch op

/-! ## A call -/

open Lean.Order in
/-- The judgment by fees reads no peer: a renamed computation is judged as the computation. -/
@[spec] theorem renamed_spec {A : Type} (ρ : Role → Role) (form : Comp (RSig M) Stop A)
    (Q : A → Credit) {E} : Triple (renamed ρ form) (wp form Q E) Q E := by
  constructor
  simp only [ExceptT.wp_apply_eq, PFunctor.OpSpec.toWPMonad_wp]
  change PFunctor.FreeM.wpFold (ops c) form.run _ ⊑
    PFunctor.FreeM.wpFold (ops c) (form.run.mapLens (renameLens M ρ)) _
  rw [PFunctor.FreeM.wpFold_mapLens]
  have same : (fun op k => ops c ((renameLens M ρ).toFunA op) (k ∘ (renameLens M ρ).toFunB op)) =
      ops c := by
    funext op k
    have blind := Fees.judgment_blind (M := M) ρ c.draws c.allowance op k
    cases op <;> exact blind
  rw [same]

variable {p : Typed V} {h : ProtocolHeader V} {callee : Member p.headers.protocols h} {role : Role}

/-- **The rule of a call, from a contract that holds.** The reading of the role's process in the
callee, from a start at which the context's allowance covers the contract, on inputs and a ghost
that meet the precondition and from a budget that holds the fee: its results meet the
postcondition and at least the budget less the fee is left. -/
theorem call (contract : Fees.Contract M p callee role) (holds : contract.Holds c.draws)
    (start : List Frame) (covers : contract.Covers c.allowance start) (ghost : contract.Ghost)
    (ins : HList (RV M role) h.ins) (Q : HList (RV M role) h.outs → Credit)
    (E : (Stop → Credit) × EStack⟨⟩) (halts : ∀ stop left, E.1 stop left) :
    Triple (read (roleMeaning M p callee role start ins))
      (fun budget => contract.pre ghost ins ∧ contract.fee ≤ budget ∧
        ∀ outs left, contract.post ghost ins outs → budget - contract.fee ≤ left → Q outs left)
      Q E := by
  constructor
  rintro budget ⟨pre, fee, next⟩
  rw [fold_read]
  exact Process.interpret_mono (Fees.judgment_monotone c.draws c.allowance)
    (fun outs left ⟨post, kept⟩ => next outs left post kept) (fun stop left _ => halts stop left)
    _ budget (holds c.allowance start covers ghost ins pre budget fee)

end ZkcFormal.Written.FeeRules
