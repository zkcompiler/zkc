import Zkc.Source.Finite

/-! Positive and negative controls for the independent finite boundary.
These are symbolic Lean checks and small executions, not native correspondence.
-/

namespace FiniteTests
open PIR Zkc.Source.Finite

abbrev interface : Signature := ⟨Unit, fun _ => Nat⟩

def add (state item : Nat) : Proc interface Nat := .done (state + item)

-- Entry checks survive empty enumeration and otherwise unused definitions.
example : (Domain.check false .refused (.elements ([] : List Nat))).admit =
    .stopped .refused := rfl
example : (Domain.before (.check false .abort (.elements [1]))
    (.elements ([] : List Nat))).admit = .stopped .abort := rfl
example : execute (.check false .refused (.elements ([] : List Nat))) add 7 =
    .halt .refused := rfl
example : execute (.elements ([] : List Nat)) add 7 = .done 7 := rfl

-- A result-only rewrite that drops admission is observably different.
example : execute (.check false .refused (.elements ([] : List Nat))) add 7 ≠
    .done 7 := by intro impossible; cases impossible

-- Empty products admit every factor; zip is strict even if a factor is ignored.
example : (Domain.product (.elements ([] : List Nat))
    (.check false .exhausted (.elements [1]))).admit = .stopped .exhausted := rfl
example : (Domain.zip (.elements [1]) (.elements [2, 3])).admit = .stopped .refused := rfl
example : (Domain.product (.elements [1, 2]) (.elements [3, 4])).admit =
    .returned [(1, 3), (1, 4), (2, 3), (2, 4)] := rfl
example : (Domain.zip (.check false .abort (.elements [1]))
    (.check false .refused (.elements [2]))).admit = .stopped .abort := rfl

-- Equal lengths authorize neither value equality nor substitution of captures.
example : execute (.elements [1, 2]) add 0 = .done 3 := rfl
example : execute (.elements [3, 4]) add 0 = .done 7 := rfl
example : execute (.elements [1, 2]) add 0 ≠ execute (.elements [3, 4]) add 0 := by
  intro impossible
  cases impossible
example : execute (.elements [1, 2]) (fun _ item => (Proc.done (7 + item) : Proc interface Nat)) 7 =
    .done 9 := rfl
example : execute (.elements [1, 2]) add 7 = .done 10 := rfl

-- Pure finite calculations compose with arbitrary replies in an open suffix.
def next (value : Nat) : Proc interface Nat := .call () fun reply => .done (value + reply)

theorem add_sum (items : List Nat) (initial : Nat) :
    items.foldl (· + ·) initial = initial + items.sum := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih => simp only [List.foldl_cons, List.sum_cons, ih, Nat.add_assoc]

theorem sum_replacement (domain : Domain Nat) (initial : Nat) :
    ExactRefinement ((execute domain add initial).bind next)
      ((admitThen domain.admit fun items =>
        Proc.done (initial + items.sum)).bind next) :=
  execute_replace (I := interface) domain add (· + ·) (fun _ _ => rfl)
    (fun items state => state + items.sum) add_sum initial next

-- A dot-like contraction and a Horner residual use the same finite machinery.
def dotStep (state : Nat) (item : Nat × Nat) : Proc interface Nat :=
  .done (state + item.1 * item.2)
example : execute (.zip (.elements [2, 3]) (.elements [5, 7])) dotStep 0 = .done 31 := rfl

def horner (challenge state coefficient : Nat) : Proc interface Nat :=
  .done (state * challenge + coefficient)
example : execute (.elements [2, 3, 4]) (horner 5) 0 = .done 69 := rfl

-- Checking the first transition alone is insufficient for carried-state laws.
def delayedStop (state _item : Nat) : Proc interface Nat :=
  if state = 0 then .done 1 else .halt .reject
example : delayedStop 0 0 = .done 1 := rfl
example : fold delayedStop [0, 0] 0 = .halt .reject := rfl

-- A Local callback remains ordered. A later map failure precedes the reducer.
def collectFailure (_ : Nat) : Proc interface Nat := .halt .abort
def checkedMap (state item : Nat) : Proc interface Nat :=
  if item = 2 then .halt .reject else .done (state + item)
example : (fold checkedMap [1, 2] 0).bind collectFailure = .halt .reject := rfl
example : fold (fun state item => (checkedMap state item).bind collectFailure) [1, 2] 0 =
    .halt .abort := rfl
example : (fold checkedMap [1, 2] 0).bind collectFailure ≠
    fold (fun state item => (checkedMap state item).bind collectFailure) [1, 2] 0 := by
  intro impossible
  cases impossible

-- A reached nested computation differs from eagerly hoisted admission.
def nested (_state _item : Nat) : Proc interface Nat :=
  execute (.check false .refused (.elements [1])) add 0
example : fold nested [] 9 = .done 9 := rfl
example : fold nested [0] 9 = .halt .refused := rfl
example : execute (.before (.check false .refused (.elements [1]))
    (.elements ([] : List Nat))) add 9 = .halt .refused := rfl

-- Arbitrary replies and actual successor state survive a failure mid-loop.
def interactive (state item : Nat) : Proc interface Nat :=
  .call () fun reply => if reply = 0 then .halt .reject else .done (state + item + reply)
def replies : Handler interface Nat Nat := fun _ state =>
  ⟨.returned (if state = 0 then 5 else 0), state + 1, [state]⟩
example : ((fold interactive [1, 2, 3] 0).run replies 0).outcome = .stopped .reject := rfl
example : ((fold interactive [1, 2, 3] 0).run replies 0).state = 2 := rfl
example : ((fold interactive [1, 2, 3] 0).run replies 0).events = [0, 1] := rfl

-- Later admission failure precedes a potential strict-zip mismatch.
example : (Domain.zip (.elements [1])
    (.check false .exhausted (.elements [2, 3]))).admit = .stopped .exhausted := rfl
example : (Domain.zip (.elements ([] : List Nat))
    (.check false .exhausted (.elements [1]))).admit = .stopped .exhausted := rfl
example : (Domain.product (.check false .abort (.elements [1]))
    (.check false .reject (.elements [2]))).admit = .stopped .abort := rfl
example : (Domain.before (.check false .abort (.elements [1]))
    (.check false .reject (.elements [2]))).admit = .stopped .abort := rfl

-- A mutant that skips a later empty-product factor disagrees with admission.
def skipEmptyProduct (xs : List Nat) (right : Domain Nat) : Outcome (List (Nat × Nat)) :=
  if xs.isEmpty then .returned [] else (Domain.product (.elements xs) right).admit
example : skipEmptyProduct [] (.check false .exhausted (.elements [1])) ≠
    (Domain.product (.elements []) (.check false .exhausted (.elements [1]))).admit := by
  intro impossible
  cases impossible

-- Admission is before the first call, including its state transition.
example : ((execute (.check false .refused (.elements [1])) interactive 0).run replies 0).events =
    [] := rfl
example : ((execute (.check false .refused (.elements [1])) interactive 0).run replies 0).state =
    0 := rfl

abbrev itemInterface : Signature := ⟨Nat × Nat, fun _ => Unit⟩
def logItem (state : Nat) (item : Nat × Nat) : Proc itemInterface Nat :=
  .call item fun _ => .done (state + 1)
def itemHandler : Handler itemInterface Nat (Nat × Nat) := fun item state =>
  ⟨.returned (), state + 1, [item]⟩
example : ((execute (.product (.elements [1, 2]) (.elements [3, 4])) logItem 0).run
    itemHandler 0).events = [(1, 3), (1, 4), (2, 3), (2, 4)] := rfl

-- A nested check reached after a call preserves that call, including on failure.
def nestedAfterCall (state item : Nat) : Proc interface Nat :=
  .call () fun _ => execute (.check (item != 2) .refused (.elements [item])) add state
example : ((fold nestedAfterCall [1, 2, 3] 0).run replies 0).events = [0, 1] := rfl
example : ((fold nestedAfterCall [1, 2, 3] 0).run replies 0).outcome =
    .stopped .refused := rfl

-- The useful totality law is restricted by both item membership and a state invariant.
def boundedStep (state item : Nat) : Proc interface Nat :=
  if item < 3 ∧ state < 5 then .done ((state + item) % 5) else .halt .reject
example : ¬ (∀ state item, boundedStep state item = .done ((state + item) % 5)) := by
  intro global
  have impossible := global 0 3
  cases impossible

theorem bounded_replacement :
    ExactRefinement ((execute (.elements [0, 1, 2]) boundedStep 0).bind next)
      ((admitThen (Domain.elements [0, 1, 2]).admit fun _ => Proc.done 3).bind next) := by
  apply execute_replace_on (total := fun state item => (state + item) % 5)
    (valid := fun state => state < 5) (start := by decide)
  · intro items admitted state item member valid
    simp only [Domain.admit, Outcome.returned.injEq] at admitted
    subst items
    have small : item < 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    constructor
    · simp only [boundedStep, small, valid, and_self, ↓reduceIte]
    · exact Nat.mod_lt _ (by decide)
  · intro items admitted
    simp only [Domain.admit, Outcome.returned.injEq] at admitted
    subst items
    rfl

-- Native n-ary zip checks lengths only after every child is admitted.
-- Nesting binary zips can expose a mismatch before a later child refuses.
def admitThree (first second third : Domain Nat) : Outcome Unit :=
  continueWith first.admit fun xs => continueWith second.admit fun ys =>
    continueWith third.admit fun zs =>
      if xs.length = ys.length ∧ ys.length = zs.length then .returned () else .stopped .refused

example : admitThree (.elements [1]) (.elements [2, 3])
    (.check false .exhausted (.elements [4])) = .stopped .exhausted := rfl

example : (Domain.zip (.zip (.elements [1]) (.elements [2, 3]))
    (.check false .exhausted (.elements [4]))).admit = .stopped .refused := rfl

-- Nonidentity translation changes both emitted requests and the used replies.
abbrev numberedInterface : Signature := ⟨Nat, fun _ => Nat⟩
def expand : OperationInterpretation interface numberedInterface :=
  fun _ => .call 99 fun reply => .done (reply + 1)

theorem translated_execution (domain : Domain Nat) (initial : Nat) :
    (execute domain interactive initial).interpret expand =
      execute domain (fun state item =>
        .call (I := numberedInterface) 99 fun reply =>
          if reply + 1 = 0 then .halt .reject else .done (state + item + (reply + 1))) initial := by
  exact interpret_execute expand domain interactive initial

example : (execute (.elements [1, 2]) interactive 0).interpret expand =
    .call 99 (fun first => .call 99 (fun second => .done (1 + (first + 1) + 2 + (second + 1)))) := rfl
example : (execute (.check false .abort (.elements [1])) interactive 0).interpret expand =
    .halt .abort := rfl

#print axioms Zkc.Source.Finite.interpret_execute
#print axioms translated_execution

#print axioms Zkc.Source.Finite.fold_total_on
#print axioms Zkc.Source.Finite.execute_replace_on
#print axioms Zkc.Source.Finite.execute_product
#print axioms bounded_replacement

#print axioms Zkc.Source.Finite.execute_total
#print axioms Zkc.Source.Finite.execute_replace
#print axioms Zkc.Source.Finite.fold_congr
#print axioms sum_replacement
end FiniteTests
