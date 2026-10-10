import Zkc.Source.TypeInstantiation

/-! Named-call binding after label resolution.

A typed permutation rearranges already evaluated temporaries. It never
permutes expression evaluation. The adapter must establish the label bijection,
expected types and ownership of the authored operands; this is not a proof of
the parser, label checker or native elaborator.
-/

set_option autoImplicit false

namespace Zkc.Source.ArgumentBinding

variable {Ty : Type} {Value : Ty → Type} {authored formal : List Ty}

/-- A constructive bijection of typed ports, including equal-typed occurrences.
There is no constructor for copying or discarding a port. -/
inductive PortPermutation : List Ty → List Ty → Type where
  | nil : PortPermutation [] []
  | keep {xs ys : List Ty} (ty : Ty) : PortPermutation xs ys →
      PortPermutation (ty :: xs) (ty :: ys)
  | swap (a b : Ty) (xs : List Ty) : PortPermutation (a :: b :: xs) (b :: a :: xs)
  | trans {xs ys zs : List Ty} : PortPermutation xs ys → PortPermutation ys zs →
      PortPermutation xs zs

def PortPermutation.bind : {authored formal : List Ty} → PortPermutation authored formal →
    Values Value authored → Values Value formal
  | _, _, .nil, .nil => .nil
  | _, _, .keep _ p, .cons value rest => .cons value (p.bind rest)
  | _, _, .swap _ _ _, .cons a (.cons b rest) => .cons b (.cons a rest)
  | _, _, .trans p q, values => q.bind (p.bind values)

def PortPermutation.inverse : {authored formal : List Ty} →
    PortPermutation authored formal → PortPermutation formal authored
  | _, _, .nil => .nil
  | _, _, .keep ty p => .keep ty p.inverse
  | _, _, .swap a b xs => .swap b a xs
  | _, _, .trans p q => .trans q.inverse p.inverse

theorem PortPermutation.bind_inverse (p : PortPermutation authored formal)
    (values : Values Value authored) : p.inverse.bind (p.bind values) = values := by
  induction p with
  | nil => cases values; rfl
  | keep ty p ih => cases values with
    | cons value rest => simp only [inverse, bind, ih]
  | swap a b xs => cases values with
    | cons a rest => cases rest; rfl
  | trans p q hp hq => simp only [inverse, bind, hq, hp]

@[simp] theorem PortPermutation.inverse_inverse (p : PortPermutation authored formal) :
    p.inverse.inverse = p := by
  induction p with
  | nil => rfl
  | keep ty p ih => simp only [inverse, ih]
  | swap a b xs => rfl
  | trans p q hp hq => simp only [inverse, hp, hq]

theorem PortPermutation.inverse_bind (p : PortPermutation authored formal)
    (values : Values Value formal) : p.bind (p.inverse.bind values) = values := by
  simpa only [inverse_inverse] using p.inverse.bind_inverse values

/-- Binding references then reading values agrees with binding already read
values. `Operands.eval` is an environment lookup, not effectful evaluation. -/
theorem PortPermutation.eval_bind (p : PortPermutation authored formal)
    {Γ : List Ty} (operands : Operands Γ authored) (env : Environment Value Γ) :
    Operands.eval env (p.bind operands) = p.bind (operands.eval env) := by
  induction p with
  | nil => cases operands; rfl
  | keep ty p ih => cases operands with
    | cons value rest => simp only [bind, Operands.eval, ih]
  | swap a b xs => cases operands with
    | cons a rest => cases rest; rfl
  | trans p q hp hq => simp only [bind, hq, hp]

/-- Record every occurrence, even if two ports contain the same value. -/
def occurrences {Token : Type} (token : {ty : Ty} → Value ty → Token) :
    {types : List Ty} → Values Value types → List Token
  | _, .nil => []
  | _, .cons value rest => token value :: occurrences token rest

theorem PortPermutation.occurrences_perm {Token : Type}
    (token : {ty : Ty} → Value ty → Token) (p : PortPermutation authored formal)
    (values : Values Value authored) :
    (occurrences token (p.bind values)).Perm (occurrences token values) := by
  induction p with
  | nil => cases values; exact .nil
  | keep ty p ih => cases values with
    | cons value rest => exact .cons _ (ih rest)
  | swap a b xs => cases values with
    | cons a rest => cases rest with
      | cons b rest => exact .swap _ _ _
  | trans p q hp hq => exact (hq (p.bind values)).trans (hp values)

/-- Affine place-use multiplicity is unchanged, including an already invalid
duplicate use. Binding cannot repair or introduce a repeated operand. -/
theorem PortPermutation.operand_count (p : PortPermutation authored formal)
    {Γ : List Ty} (operands : Operands Γ authored) (index : Nat) :
    (occurrences (fun v => v.index) (p.bind operands)).count index =
      (occurrences (fun v => v.index) operands).count index :=
  (p.occurrences_perm (fun v => v.index) operands).count_eq index

/-- Type selection changes neither the chosen ports nor their multiplicity.
Distinct source types may select the same target type. -/
def PortPermutation.instantiate {Target : Type} (select : Ty → Target) :
    {authored formal : List Ty} → PortPermutation authored formal →
      PortPermutation (authored.map select) (formal.map select)
  | _, _, .nil => .nil
  | _, _, .keep ty p => .keep (select ty) (p.instantiate select)
  | _, _, .swap a b xs => .swap (select a) (select b) (xs.map select)
  | _, _, .trans p q => .trans (p.instantiate select) (q.instantiate select)

/-- Reuse the source's type-instantiated heterogeneous values. No second type
substitution or equality checker is introduced for named calls. -/
theorem PortPermutation.bind_instantiate {Target : Type} (select : Ty → Target)
    {SelectedValue : Target → Type} (p : PortPermutation authored formal)
    (values : Values (fun ty => SelectedValue (select ty)) authored) :
    (p.instantiate select).bind (values.instantiate select) =
      (p.bind values).instantiate select := by
  induction p with
  | nil => cases values; rfl
  | keep ty p ih => cases values with
    | cons value rest => simp only [instantiate, bind, Values.instantiate, ih]
  | swap a b xs => cases values with
    | cons a rest => cases rest; rfl
  | trans p q hp hq => simp only [instantiate, bind, hp, hq]

variable {interface : PIR.Signature}

/-- Evaluate the authored list from left to right, once per reached expression.
Earlier effects may change the state observed by later expressions. -/
def evaluate : {types : List Ty} →
    Values (fun ty => PIR.Proc interface (Value ty)) types →
      PIR.Proc interface (Values Value types)
  | _, .nil => .done .nil
  | _, .cons expression rest => expression.bind fun value =>
      (evaluate rest).bind fun values => .done (.cons value values)

def invoke {Result : Type} (p : PortPermutation authored formal)
    (expressions : Values (fun ty => PIR.Proc interface (Value ty)) authored)
    (callee : Values Value formal → PIR.Proc interface Result) : PIR.Proc interface Result :=
  (evaluate expressions).bind fun values => callee (p.bind values)

/-- Even a reversal of formal ports keeps the two effectful expressions in
authored order. Each is reached once; only their returned values are swapped. -/
theorem invoke_swap {Result : Type} {a b : Ty}
    (first : PIR.Proc interface (Value a)) (second : PIR.Proc interface (Value b))
    (callee : Values Value [b, a] → PIR.Proc interface Result) :
    invoke (.swap a b []) (.cons first (.cons second .nil)) callee =
      first.bind (fun x => second.bind (fun y => callee (.cons y (.cons x .nil)))) := by
  simp only [invoke, evaluate, PortPermutation.bind, PIR.Proc.bind_assoc, PIR.Proc.bind]

/-- The complete authored evaluation runs before formal-port binding. Its
post-state and ordered event prefix are retained, including terminal stops. -/
theorem run_invoke {Result State Event : Type} (p : PortPermutation authored formal)
    (expressions : Values (fun ty => PIR.Proc interface (Value ty)) authored)
    (callee : Values Value formal → PIR.Proc interface Result)
    (handler : PIR.Handler interface State Event) (state : State) :
    (invoke p expressions callee).run handler state =
      ((evaluate expressions).run handler state).follow
        (fun values => (callee (p.bind values)).run handler) :=
  PIR.run_bind handler _ _ state

/-- If the first authored expression stops, later expressions and the callee
are suppressed regardless of where that argument's formal port occurs. -/
theorem run_invoke_head_stopped {Result State Event : Type} {ty : Ty} {rest : List Ty}
    (p : PortPermutation (ty :: rest) formal)
    (expression : PIR.Proc interface (Value ty))
    (expressions : Values (fun ty => PIR.Proc interface (Value ty)) rest)
    (callee : Values Value formal → PIR.Proc interface Result)
    (handler : PIR.Handler interface State Event) (state final : State)
    (events : List Event) (reason : PIR.Stop)
    (stopped : expression.run handler state = ⟨.stopped reason, final, events⟩) :
    (invoke p (.cons expression expressions) callee).run handler state =
      ⟨.stopped reason, final, events⟩ := by
  rw [run_invoke, evaluate, PIR.run_bind, stopped]
  rfl

end Zkc.Source.ArgumentBinding
