module

public import Zkc.Core.EveryRun

@[expose] public section

/-! Every run of a region, one operation at a time.

A statement that every run of a region returns is proved along the region: an operation that
returns its results is passed by an equation for it (`EveryRun.step`), and a draw or a sample
by a statement for every reply (`EveryRun.draw`, `EveryRun.sample`). The rest of the region is
then read in the environment with the results bound.

The equation of an operation is where a law of a function is used: a call is the meaning of
the callee on the arguments, and a law of the callee, stated for the table of functions, gives
its result without its body (`returns_of_eq`). A guard is passed on a flag that holds
(`guard_passes`).

A region that is the instructions of one iteration followed by any region is proved once for
the region that follows; the statements of the iterations then compose, one after another.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core PIR

variable {model : Model}

/-- A process that returns a value, followed by another, is the other on the value. -/
theorem returns_of_eq {A B : Type} {process : Process (Effects model) A} {value : A}
    (returns : process = .done value) (next : A → Process (Effects model) B) :
    process.bind next = next value := by
  subst returns
  rfl

/-- A guard on a flag that holds, followed by a process, is the process. -/
theorem guard_passes {A B : Type} {flag : Bool} (holds : flag = true) (value : A) (reason : Stop)
    (next : A → Process (Effects model) B) :
    (cond flag (Process.done value) (.halt reason) : Process (Effects model) A).bind next =
      next value := by
  subst holds
  rfl

/-- A decision of a proposition that holds, whatever decides it. A flag that a row of a model
computes is such a decision at the row's own instance. -/
theorem decide_holds {proposition : Prop} {decides : Decidable proposition}
    (holds : proposition) : @decide proposition decides = true :=
  decide_eq_true holds

/-- A choice on a proposition that holds. -/
theorem if_pos' {A : Type} {proposition : Prop} {decides : Decidable proposition}
    (holds : proposition) {first second : A} :
    @ite A proposition decides first second = first := by
  cases decides with
  | isTrue _ => rfl
  | isFalse fails => exact absurd holds fails

/-- A part of a sized collection, at a size: the operation that the core owns returns it when
the bounds are in order and the part has the size. -/
theorem slice_computes {element : Ty} {size result : Nat}
    (values : Ty.Value model.Carrier (.seq element (some size))) (first last : Nat)
    (ordered : first ≤ last) (within : last ≤ size) (fits : last - first = result) :
    definedProcess model
        (Builtin.eval (Carrier := model.Carrier) (.seqSlice element (some size) (some result))
          (.cons values (.cons (ty := Ty.nat) first (.cons (ty := Ty.nat) last .nil)))) =
      .done (.cons (ty := Ty.seq element (some result))
        ⟨(values.val.drop first).take (last - first), by
          rw [List.length_take, List.length_drop, values.property]
          omega⟩ .nil) := by
  have bounds : (Nat.ble first last && Nat.ble last (Ty.elements (some size) values).length) =
      true := by
    rw [Bool.and_eq_true]
    refine ⟨Nat.ble_eq_true_of_le ordered, Nat.ble_eq_true_of_le ?_⟩
    show last ≤ values.val.length
    rw [values.property]
    exact within
  have sized : ((values.val.drop first).take (last - first)).length = result := by
    rw [List.length_take, List.length_drop, values.property]
    omega
  show definedProcess model
    (if (Nat.ble first last && Nat.ble last (Ty.elements (some size) values).length) = true then
      (Ty.sequence (some result) (((Ty.elements (some size) values).drop first).take (last - first))).map
        fun slice => Values.cons slice Values.nil
    else none) = _
  rw [if_pos' bounds]
  have found : Ty.sequence (Carrier := model.Carrier) (element := element) (some result)
      (((Ty.elements (some size) values).drop first).take (last - first)) =
        some ⟨(values.val.drop first).take (last - first), sized⟩ := by
    show (if same : ((values.val.drop first).take (last - first)).length = result then
      some (⟨(values.val.drop first).take (last - first), same⟩ :
        { items : List (Ty.Value model.Carrier element) // items.length = result }) else none) = _
    split
    · rfl
    · exact absurd sized (by assumption)
  rw [found]
  rfl

/-- `slice_computes`, with its conditions as evaluations: a statement at a body gives them as
closed equations, which the kernel evaluates. -/
theorem slice_computes_of_checks {element : Ty} {size result : Nat}
    (values : Ty.Value model.Carrier (.seq element (some size))) (first last : Nat)
    (ordered : Nat.ble first last = true) (within : Nat.ble last size = true)
    (fits : Nat.beq (last - first) result = true) :
    definedProcess model
        (Builtin.eval (Carrier := model.Carrier) (.seqSlice element (some size) (some result))
          (.cons values (.cons (ty := Ty.nat) first (.cons (ty := Ty.nat) last .nil)))) =
      .done (.cons (ty := Ty.seq element (some result))
        ⟨(values.val.drop first).take (last - first), by
          rw [List.length_take, List.length_drop, values.property]
          have := Nat.le_of_ble_eq_true within
          have := Nat.eq_of_beq_eq_true fits
          omega⟩ .nil) :=
  slice_computes values first last (Nat.le_of_ble_eq_true ordered) (Nat.le_of_ble_eq_true within)
    (Nat.eq_of_beq_eq_true fits)

section Steps

variable {dialect : Dialect} {meaning : RegionMeaning dialect (Effects model)}
  {Γ out : List dialect.Ty} {op : dialect.Op} {arguments : Operands Γ (dialect.arguments op)}
  {bodies : Regions dialect (dialect.regions op)}
  {next : Region dialect (bindAll Γ (dialect.results op)) out}
  {env : Environment meaning.Value Γ} {post : Values meaning.Value out → Prop}

/-- An operation that returns values: every run of the region returns when every run of the
rest does, with the values bound. -/
theorem EveryRun.step (values : Values meaning.Value (dialect.results op))
    (computes : meaning.operation op (Operands.eval env arguments) (bodies.denote meaning) =
      .done values)
    (continues : EveryRun post (next.denote meaning (Environment.bindAll env values))) :
    EveryRun post ((Region.letOp op arguments bodies next).denote meaning env) := by
  show EveryRun post
    ((meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _)
  rw [computes]
  exact continues

/-- An operation that draws and returns values of the reply: every run of the region returns
when, for every reply, every run of the rest does. -/
theorem EveryRun.draw {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
    (results : model.Value law.output → Values meaning.Value (dialect.results op))
    (draws : meaning.operation op (Operands.eval env arguments) (bodies.denote meaning) =
      .call (.draw site law inputs) fun reply => .done (results reply))
    (continues : ∀ reply,
      EveryRun post (next.denote meaning (Environment.bindAll env (results reply)))) :
    EveryRun post ((Region.letOp op arguments bodies next).denote meaning env) := by
  show EveryRun post
    ((meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _)
  rw [draws]
  exact continues

/-- An operation that samples and returns values of the reply. -/
theorem EveryRun.sample {site : Site} {law : SamplingRow}
    {inputs : Values model.Value law.inputs}
    (results : model.Value law.output → Values meaning.Value (dialect.results op))
    (samples : meaning.operation op (Operands.eval env arguments) (bodies.denote meaning) =
      .call (.sample site law inputs) fun reply => .done (results reply))
    (continues : ∀ reply,
      EveryRun post (next.denote meaning (Environment.bindAll env (results reply)))) :
    EveryRun post ((Region.letOp op arguments bodies next).denote meaning env) := by
  show EveryRun post
    ((meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _)
  rw [samples]
  exact continues

/-- An operation that returns values: the region is the rest, with the values bound. -/
theorem denote_step (values : Values meaning.Value (dialect.results op))
    (computes : meaning.operation op (Operands.eval env arguments) (bodies.denote meaning) =
      .done values) :
    (Region.letOp op arguments bodies next).denote meaning env =
      next.denote meaning (Environment.bindAll env values) := by
  show (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind _ = _
  rw [computes]
  rfl

/-- The end of a region: its values, read in the environment. -/
theorem EveryRun.ret {values : Operands Γ out}
    (holds : post (Operands.eval env values)) :
    EveryRun post ((Region.ret (dialect := dialect) values).denote meaning env) :=
  holds

end Steps

end Zkc.Formal
