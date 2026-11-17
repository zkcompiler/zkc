import Zkc.Core.Evidence.Call
import Zkc.Core.Facts.LocalLaws
import Zkc.Tests.Core.Facts
import Zkc.Tests.Core.Shapes

/-!
Subjects, on the vocabulary with a field of `Tests/Core/Facts.lean`: what is known of a
computation is said once, of the subject of the instruction that runs it
(`Evidence/Subject.lean`), whether it is a call of a function, a block or an instruction in line.

One function, the sum of two products `a * b + c * d` of naturals, is presented three ways, each
in a caller of four inputs `a, b, c, d` (the names `0, 1, 2, 3`), written as typed terms with
`var`, in every model; the callee's body is the callee by names (`eraseFn`), which the check of
facts accepts:

1. a callee whose body computes it, called by the caller: the subject of the call yields the
   function (`Law.yields`), by the law of the callee, which the instructions of its body give;
2. a block in the caller whose body is the same instructions: the subject of the block yields the
   function, since its body returns it on every path;
3. the instructions in line in the caller: the subject of the last instruction, the sum, yields
   the function on the starts that the two products before it give (`ownedOp_yields`).

Each body is known from the operations that the core owns, which yield their results where their
requirements hold (`ownedOp_yields`), composed by the rule of an instruction for a witness
(`Term.op_yields`). One law of the function is proved once, as mathematics: exchanging the two
products gives the same number (`sumOfProducts_exchange`). From it, for each presentation, the
caller means the same as the caller with the two products exchanged (the call's operands `c, d,
a, b`; the block's body reading `c, d` then `a, b`; the last instruction's operands exchanged),
each by the same lemma, a law lifted through witnesses (`Term.equivalent_of_yields`).

Two controls. A contract is not a witness: the call of the sum of two products satisfies "the
result is at least zero" (`Subject.Yields.satisfies`), and so does the call of a callee that
returns the first product only, whose subject yields another function. And a callee that stops
with a reason on some valid input, `a * b + c * d` after a guard that `a * b < c * d`: its call
satisfies the contract that it returns the sum of two products, with that stop allowed, and does
not yield the function.
-/

namespace Zkc.Core.SubjectsTests

open Zkc.Core.Shapes
open FactsTests (field times plus verdict accepted)

set_option maxRecDepth 4000

/-! ## The function, as mathematics -/

/-- The sum of two products. -/
def sumOfProducts (a b c d : Nat) : Nat := a * b + c * d

/-- **The law of the function**, proved once: exchanging the two products gives the same
number. -/
theorem sumOfProducts_exchange (a b c d : Nat) : sumOfProducts a b c d = sumOfProducts c d a b :=
  Nat.add_comm _ _

/-- Four naturals. -/
abbrev four : List field.Ty := [.nat, .nat, .nat, .nat]

/-- The sum of two products of four values, as a function of a model's values. -/
def sumOfProductsOf (M : Model field) : HList M.Val four → HList M.Val [.nat]
  | .cons a (.cons b (.cons c (.cons d .nil))) => .cons (sumOfProducts a b c d) .nil

/-- The law, of the values of a model. -/
theorem sumOfProductsOf_exchange (M : Model field) (a b c d : Nat) :
    sumOfProductsOf M (.cons a (.cons b (.cons c (.cons d .nil)))) =
      sumOfProductsOf M (.cons c (.cons d (.cons a (.cons b .nil)))) :=
  congrArg (fun n => HList.cons n .nil) (sumOfProducts_exchange a b c d)

/-! ## The operations that the core owns, as witnesses -/

/-- A product of naturals yields the product of its operands' values, from every start: it has
no requirement (`ownedOp_yields`). -/
theorem product_yields (M : Model field) {fns : List (FnHeader field)} (table : FnTable M fns)
    {Γ : Ctx field.Ty} (key : Key) (x y : Var Γ .nat) :
    (Subject.op (localSem M fns table) key (LocalOp.owned .natMul) (.cons x (.cons y .nil))).Yields
      (localSem M fns table) (fun _ _ => True) (fun env => .cons (env.get x * env.get y) .nil) :=
  ownedOp_yields (table := table) key .natMul _ _
    (fun | .cons a (.cons b .nil) => .cons ((a : Nat) * b) .nil)
    (fun args results ran => by
      obtain ⟨a, b, rfl⟩ := HList.two args
      cases ran
      rfl)
    (fun _ _ _ => ⟨trivial, trivial, trivial⟩)
    (fun _ _ _ _ none => nomatch none)

/-- A sum of naturals yields the sum of its operands' values, from every start. -/
theorem addition_yields (M : Model field) {fns : List (FnHeader field)} (table : FnTable M fns)
    {Γ : Ctx field.Ty} (key : Key) (x y : Var Γ .nat) :
    (Subject.op (localSem M fns table) key (LocalOp.owned .natAdd) (.cons x (.cons y .nil))).Yields
      (localSem M fns table) (fun _ _ => True) (fun env => .cons (env.get x + env.get y) .nil) :=
  ownedOp_yields (table := table) key .natAdd _ _
    (fun | .cons a (.cons b .nil) => .cons ((a : Nat) + b) .nil)
    (fun args results ran => by
      obtain ⟨a, b, rfl⟩ := HList.two args
      cases ran
      rfl)
    (fun _ _ _ => ⟨trivial, trivial, trivial⟩)
    (fun _ _ _ _ none => nomatch none)

/-! ## The instructions -/

/-- The four inputs, in order. -/
def inputs : HList (Var (Ctx.positional four)) four :=
  .cons (var 0) (.cons (var 1) (.cons (var 2) (.cons (var 3) .nil)))

/-- The four inputs with the two pairs exchanged: `c, d, a, b`. -/
def exchanged : HList (Var (Ctx.positional four)) four :=
  .cons (var 2) (.cons (var 3) (.cons (var 0) (.cons (var 1) .nil)))

/-- `t1 := a * b; t2 := c * d; s := t1 + t2; return s`: the body of the callee, and of the
block. -/
def sumBody : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .op ⟨1⟩ (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil)) (.cons 4 .nil) <|
  .op ⟨2⟩ (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil)) (.cons 5 .nil) <|
  .op ⟨3⟩ (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil)) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The same instructions reading `c, d` then `a, b`. -/
def sumBodyExchanged : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .op ⟨1⟩ (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil)) (.cons 4 .nil) <|
  .op ⟨2⟩ (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil)) (.cons 5 .nil) <|
  .op ⟨3⟩ (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil)) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The instructions return the sum of two products of the inputs, on every path, by the
witnesses of the operations that the core owns and the rule of an instruction for a witness. -/
theorem sumBody_denote (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    sumBody.denote (localSem M [] table) path env = .done (sumOfProductsOf M (env.all inputs)) := by
  refine (Term.op_yields _ (product_yields M table ⟨1⟩ _ _) _ _ path env trivial).trans ?_
  refine (Term.op_yields _ (product_yields M table ⟨2⟩ _ _) _ _ path _ trivial).trans ?_
  refine (Term.op_yields _ (addition_yields M table ⟨3⟩ _ _) _ _ path _ trivial).trans ?_
  rfl

/-- The instructions reading `c, d` then `a, b` return the sum of two products of the exchanged
inputs. -/
theorem sumBodyExchanged_denote (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    sumBodyExchanged.denote (localSem M [] table) path env =
      .done (sumOfProductsOf M (env.all exchanged)) := by
  refine (Term.op_yields _ (product_yields M table ⟨1⟩ _ _) _ _ path env trivial).trans ?_
  refine (Term.op_yields _ (product_yields M table ⟨2⟩ _ _) _ _ path _ trivial).trans ?_
  refine (Term.op_yields _ (addition_yields M table ⟨3⟩ _ _) _ _ path _ trivial).trans ?_
  rfl

/-! ## 1. A callee, called by the caller -/

/-- The callee, with the key 1: four naturals, one natural, it cannot stop. -/
def sumHeader : FnHeader field := ⟨⟨1⟩, four, [.nat], false, none, Summary.empty⟩

/-- The program of the callee, its body the instructions. -/
def sumDefs : Defs field ⟨[sumHeader], []⟩ :=
  .fn sumHeader (Names.counting 0 _) sumBody ⟨by exact rfl, by exact rfl, by exact rfl,
    by exact rfl, by unfold Term.BoundOnce; decide, by exact rfl⟩ .nil

/-- The callee by names, as the other tests write a function. -/
def sumRegion : Region (LocalRaw field) Unit :=
  .mk [0, 1, 2, 3] [.op ⟨1⟩ [4] times [0, 1], .op ⟨2⟩ [5] times [2, 3], .op ⟨3⟩ [6] plus [4, 5]]
    [6]

/-- The instructions written as a typed term are the callee by names: they erase to it... -/
example : eraseFn (hdr := sumHeader) (Names.counting 0 _) sumBody = sumRegion := by
  decide +kernel

/-- ...and the check of facts accepts the callee by names, with no loop. -/
example : verdict [] sumHeader sumRegion = accepted := by decide +kernel

/-- The callee's table. -/
def sumTable (M : Model field) : FnTable M [sumHeader] := Defs.fnTable M sumDefs

/-- The callee, by its position among the headers. -/
def sumRef : Member [sumHeader] sumHeader := .head

/-- The law of the callee, in every model: its entry returns the sum of two products of its
inputs, since its body does (`sumBody_denote`). -/
theorem sum_law (M : Model field) : Law M (sumTable M) sumRef (sumOfProductsOf M) := by
  constructor
  intro args
  match args with
  | .cons a (.cons b (.cons c (.cons d .nil))) =>
      exact sumBody_denote M (Defs.fnTable M .nil) []
        (Env.empty.extend (Names.counting 0 four) (.cons a (.cons b (.cons c (.cons d .nil)))))

/-- The caller: `s := sum(a, b, c, d); return s`. -/
def callingCaller : Term (localDialect field [sumHeader]) (Ctx.positional four) [.nat] :=
  .op ⟨10⟩ (.call sumRef) inputs (.cons 4 .nil) <| .ret (.cons (var 4) .nil)

/-- The caller with the operands exchanged: `s := sum(c, d, a, b); return s`. -/
def callingExchanged : Term (localDialect field [sumHeader]) (Ctx.positional four) [.nat] :=
  .op ⟨10⟩ (.call sumRef) exchanged (.cons 4 .nil) <| .ret (.cons (var 4) .nil)

/-- **The witness of the call**: in every model, the subject of the call yields the sum of two
products of its operands, by the law of the callee (`Law.yields`). -/
theorem call_yields (M : Model field) (operands : HList (Var (Ctx.positional four)) four) :
    (Subject.op (localSem M [sumHeader] (sumTable M)) ⟨10⟩ (LocalOp.call sumRef) operands).Yields
      (localSem M [sumHeader] (sumTable M)) (fun _ _ => True)
      (fun env => sumOfProductsOf M (env.all operands)) :=
  (sum_law M).yields M (sumTable M) sumRef ⟨10⟩ operands

/-- **The law at the call**: the caller means the same as the caller with the operands exchanged,
in every model, from the witnesses and the law (`Term.equivalent_of_yields`). -/
theorem calling_exchange (M : Model field) :
    Equivalent (localSem M [sumHeader] (sumTable M)) (fun _ _ => True) callingCaller
      callingExchanged (fun _ _ => True) :=
  Term.equivalent_of_yields _ _ (fun path env => Term.op_subject _ _ _ _ _ _ path env)
    (fun path env => Term.op_subject _ _ _ _ _ _ path env) (call_yields M inputs)
    (call_yields M exchanged)
    (fun _ _ _ => sumOfProductsOf_exchange M _ _ _ _)

/-! ## 2. A block in the caller -/

/-- The caller with a block whose body is the instructions: `s := block { … }; return s`. -/
def blockCaller : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .block ⟨20⟩ 0 sumBody (.cons 7 .nil) <| .ret (.cons (var 7) .nil)

/-- The caller with a block whose body reads `c, d` then `a, b`. -/
def blockExchanged : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .block ⟨20⟩ 0 sumBodyExchanged (.cons 7 .nil) <| .ret (.cons (var 7) .nil)

/-- **The witness of the block**: in every model and against any callees, the subject of the
block yields the sum of two products of the inputs. -/
theorem block_yields (M : Model field) (table : FnTable M []) :
    (Subject.block (localSem M [] table) ⟨20⟩ 0 sumBody).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => sumOfProductsOf M (env.all inputs)) :=
  fun _ env _ => sumBody_denote M table _ env

/-- The block reading `c, d` then `a, b` yields the sum of two products of the exchanged
inputs. -/
theorem blockExchanged_yields (M : Model field) (table : FnTable M []) :
    (Subject.block (localSem M [] table) ⟨20⟩ 0 sumBodyExchanged).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => sumOfProductsOf M (env.all exchanged)) :=
  fun _ env _ => sumBodyExchanged_denote M table _ env

/-- **The law at the block**: the caller means the same as the caller whose block reads the
operands exchanged, by the same lemma. -/
theorem block_exchange (M : Model field) (table : FnTable M []) :
    Equivalent (localSem M [] table) (fun _ _ => True) blockCaller blockExchanged
      (fun _ _ => True) :=
  Term.equivalent_of_yields _ _ (fun path env => Term.block_subject _ _ _ _ _ _ path env)
    (fun path env => Term.block_subject _ _ _ _ _ _ path env) (block_yields M table)
    (blockExchanged_yields M table)
    (fun _ _ _ => sumOfProductsOf_exchange M _ _ _ _)

/-! ## 3. The instructions in line -/

/-- The names in scope after the two products: the inputs, `t1` (the name 4) and `t2` (5). -/
abbrev afterProducts : Ctx field.Ty :=
  ((Ctx.positional four).extend (.cons 4 .nil : Names [(.nat : field.Ty)])).extend
    (.cons 5 .nil : Names [(.nat : field.Ty)])

/-- The four inputs, after the two products. -/
def inputsAfter : HList (Var afterProducts) four :=
  .cons (var 0) (.cons (var 1) (.cons (var 2) (.cons (var 3) .nil)))

/-- The four inputs with the two pairs exchanged, after the two products. -/
def exchangedAfter : HList (Var afterProducts) four :=
  .cons (var 2) (.cons (var 3) (.cons (var 0) (.cons (var 1) .nil)))

/-- The starts after the two products: `t1` is `a * b` and `t2` is `c * d`. -/
def afterEntry (M : Model field) (table : FnTable M []) : Entry (localSem M [] table) afterProducts :=
  fun _ env => env.get (var 4) = env.get (var 0) * env.get (var 1) ∧
    env.get (var 5) = env.get (var 2) * env.get (var 3)

/-- The two products, in line, then what follows them. -/
def products (rest : Term (localDialect field []) afterProducts [.nat]) :
    Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .op ⟨31⟩ (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil)) (.cons 4 .nil) <|
  .op ⟨32⟩ (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil)) (.cons 5 .nil) rest

/-- The last instruction in line, then the return: `s := t1 + t2; return s`. -/
def lastSum : Term (localDialect field []) afterProducts [.nat] :=
  .op ⟨33⟩ (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil)) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The last instruction with its operands exchanged: `s := t2 + t1; return s`. -/
def lastSumExchanged : Term (localDialect field []) afterProducts [.nat] :=
  .op ⟨33⟩ (.owned .natAdd) (.cons (var 5) (.cons (var 4) .nil)) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The caller with the instructions in line. -/
def inlineCaller : Term (localDialect field []) (Ctx.positional four) [.nat] := products lastSum

/-- The caller with the instructions in line, the two products exchanged in the last one. -/
def inlineExchanged : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  products lastSumExchanged

/-- **The witness of the last instruction**: in every model and against any callees, after the two
products, the subject of the sum yields the sum of two products of the inputs. -/
theorem last_yields (M : Model field) (table : FnTable M []) :
    (Subject.op (localSem M [] table) ⟨33⟩ (LocalOp.owned .natAdd)
      (.cons (var 4) (.cons (var 5) .nil))).Yields (localSem M [] table) (afterEntry M table)
      (fun env => sumOfProductsOf M (env.all inputsAfter)) := by
  intro path env ⟨first, second⟩
  rw [addition_yields M table (Γ := afterProducts) ⟨33⟩ (var 4) (var 5) path env trivial]
  show (Process.done (.cons (env.get (var 4) + env.get (var 5)) .nil) :
    Local (HList M.Val [.nat])) = _
  rw [first, second]
  rfl

/-- The sum with its operands exchanged yields the sum of two products of the exchanged inputs,
after the two products. -/
theorem lastExchanged_yields (M : Model field) (table : FnTable M []) :
    (Subject.op (localSem M [] table) ⟨33⟩ (LocalOp.owned .natAdd)
      (.cons (var 5) (.cons (var 4) .nil))).Yields (localSem M [] table) (afterEntry M table)
      (fun env => sumOfProductsOf M (env.all exchangedAfter)) := by
  intro path env ⟨first, second⟩
  rw [addition_yields M table (Γ := afterProducts) ⟨33⟩ (var 5) (var 4) path env trivial]
  show (Process.done (.cons (env.get (var 5) + env.get (var 4)) .nil) :
    Local (HList M.Val [.nat])) = _
  rw [first, second]
  rfl

/-- **The law at the last instruction**: after the two products, the sum means the same as the
sum with its operands exchanged, by the same lemma. -/
theorem lastSum_exchange (M : Model field) (table : FnTable M []) :
    Equivalent (localSem M [] table) (fun _ _ => True) lastSum lastSumExchanged
      (afterEntry M table) :=
  Term.equivalent_of_yields _ _ (fun path env => Term.op_subject _ _ _ _ _ _ path env)
    (fun path env => Term.op_subject _ _ _ _ _ _ path env) (last_yields M table)
    (lastExchanged_yields M table)
    (fun _ _ _ => sumOfProductsOf_exchange M _ _ _ _)

/-- The two products in line are their continuation on the environment with `t1` and `t2` bound
to them, by their witnesses. -/
theorem products_denote (M : Model field) (table : FnTable M [])
    (rest : Term (localDialect field []) afterProducts [.nat]) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    (products rest).denote (localSem M [] table) path env =
      rest.denote (localSem M [] table) path
        ((env.extend (.cons 4 .nil) (.cons (env.get (var 0) * env.get (var 1)) .nil)).extend
          (.cons 5 .nil) (.cons (env.get (var 2) * env.get (var 3)) .nil)) :=
  (Term.op_yields _ (product_yields M table ⟨31⟩ _ _) _ _ path env trivial).trans
    (Term.op_yields _ (product_yields M table ⟨32⟩ _ _) _ _ path _ trivial)

/-- **The law in line**: the caller means the same as the caller with the two products exchanged
in its last instruction, in every model: the two products give the starts of the last
instruction, where the law holds. -/
theorem inline_exchange (M : Model field) (table : FnTable M []) :
    Equivalent (localSem M [] table) (fun _ _ => True) inlineCaller inlineExchanged
      (fun _ _ => True) := by
  intro path env _
  show Process.SameWhen _ ((products lastSum).denote _ path env)
    ((products lastSumExchanged).denote _ path env)
  rw [products_denote, products_denote]
  exact lastSum_exchange M table path _ ⟨rfl, rfl⟩

/-! ## A contract is not a witness -/

/-- The result is at least zero. -/
def atLeastZero (M : Model field) {Γ : Ctx field.Ty} :
    Env M.Val Γ → HList M.Val [.nat] → Prop :=
  fun _ results => 0 ≤ (results.single : Nat)

/-- The call of the sum of two products satisfies "the result is at least zero", and never stops:
a witness is a contract (`Subject.Yields.satisfies`). -/
theorem call_atLeastZero (M : Model field) :
    (Subject.op (localSem M [sumHeader] (sumTable M)) ⟨10⟩ (LocalOp.call sumRef) inputs).Satisfies
      (localSem M [sumHeader] (sumTable M)) (fun _ _ => True) (fun _ _ => True) (atLeastZero M)
      (fun _ => False) :=
  (call_yields M inputs).satisfies _ _ (atLeastZero M) fun _ _ _ => Nat.zero_le _

/-- Another callee, with the key 2, of the same signature: it returns the first product only. -/
def firstHeader : FnHeader field := ⟨⟨2⟩, four, [.nat], false, none, Summary.empty⟩

/-- `t1 := a * b; return t1`. -/
def firstBody : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .op ⟨1⟩ (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil)) (.cons 4 .nil) <|
  .ret (.cons (var 4) .nil)

/-- The program of the other callee. -/
def firstDefs : Defs field ⟨[firstHeader], []⟩ :=
  .fn firstHeader (Names.counting 0 _) firstBody ⟨by exact rfl, by exact rfl, by exact rfl,
    by exact rfl, by unfold Term.BoundOnce; decide, by exact rfl⟩ .nil

/-- The other callee, by its position among the headers. -/
def firstRef : Member [firstHeader] firstHeader := .head

/-- The other callee's contract: its result is at least zero, and it never stops. -/
theorem first_contract (M : Model field) :
    Contract M (Defs.fnTable M firstDefs) firstRef (fun _ => True)
      (fun _ results => 0 ≤ (results.single : Nat)) (fun _ _ => False) := by
  constructor
  intro args _
  match args with
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => exact Nat.zero_le _

/-- The call of the other callee satisfies "the result is at least zero" too, and never stops,
by its contract (`Contract.satisfies`)... -/
theorem firstCall_atLeastZero (M : Model field) :
    (Subject.op (localSem M [firstHeader] (Defs.fnTable M firstDefs)) ⟨10⟩
      (LocalOp.call firstRef) inputs).Satisfies (localSem M [firstHeader] (Defs.fnTable M firstDefs))
      (fun _ _ => True) (fun _ _ => True) (atLeastZero M) (fun _ => False) :=
  fun path env _ =>
    (first_contract M).satisfies M _ firstRef ⟨10⟩ inputs (env.all inputs) path env ⟨rfl, trivial⟩

/-- ...and no witness of the sum of two products holds of it: on the inputs `1, 1, 1, 1` it
returns `1`, not `2`. -/
theorem firstCall_not_sum (M : Model field) :
    ¬ (Subject.op (localSem M [firstHeader] (Defs.fnTable M firstDefs)) ⟨10⟩
      (LocalOp.call firstRef) inputs).Yields (localSem M [firstHeader] (Defs.fnTable M firstDefs))
      (fun _ _ => True) (fun env => sumOfProductsOf M (env.all inputs)) := by
  intro yields
  have wrong := yields [] (Env.positional (.cons (1 : Nat) (.cons (1 : Nat) (.cons (1 : Nat)
    (.cons (1 : Nat) .nil))))) trivial
  change (Process.done (.cons (1 : Nat) .nil) : Local (HList M.Val [.nat])) =
    .done (.cons (2 : Nat) .nil) at wrong
  cases wrong

/-! ## A callee that stops with a reason -/

/-- A callee, with the key 3, which can stop. -/
def guardedHeader : FnHeader field := ⟨⟨3⟩, four, [.nat], true, none, Summary.empty⟩

/-- `t1 := a * b; t2 := c * d; guard t1 < t2; s := t1 + t2; return s`. -/
def guardedBody : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .op ⟨1⟩ (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil)) (.cons 4 .nil) <|
  .op ⟨2⟩ (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil)) (.cons 5 .nil) <|
  .op ⟨3⟩ (.owned .natLess) (.cons (var 4) (.cons (var 5) .nil)) (.cons 6 .nil) <|
  .guard ⟨4⟩ () (var 6) rfl .reject <|
  .op ⟨5⟩ (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil)) (.cons 7 .nil) <|
  .ret (.cons (var 7) .nil)

/-- The program of the guarded callee. -/
def guardedDefs : Defs field ⟨[guardedHeader], []⟩ :=
  .fn guardedHeader (Names.counting 0 _) guardedBody ⟨by exact rfl, by exact rfl, by exact rfl,
    by exact rfl, by unfold Term.BoundOnce; decide, by exact rfl⟩ .nil

/-- The guarded callee, by its position among the headers. -/
def guardedRef : Member [guardedHeader] guardedHeader := .head

/-- The stop of the guard, under a call. -/
def guardStop : Stop := .declared .reject ⟨[], ⟨4⟩⟩

/-- The guarded callee's contract: where it returns, it returns the sum of two products of its
inputs; where it stops, it stops at its guard. -/
theorem guarded_contract (M : Model field) :
    Contract M (Defs.fnTable M guardedDefs) guardedRef (fun _ => True)
      (fun args results => results = sumOfProductsOf M args) (fun _ stop => stop = guardStop) := by
  constructor
  intro args _
  match args with
  | .cons a (.cons b (.cons c (.cons d .nil))) =>
      show (cond (Nat.blt (a * b) (c * d)) _ _ : Local (HList M.Val [.nat])).Every _ _ _
      cases Nat.blt (a * b) (c * d) <;> exact rfl

/-- **The call of the guarded callee satisfies its contract**, with the stop of the guard
allowed (`Contract.satisfies`)... -/
theorem guardedCall_satisfies (M : Model field) :
    (Subject.op (localSem M [guardedHeader] (Defs.fnTable M guardedDefs)) ⟨10⟩
      (LocalOp.call guardedRef) inputs).Satisfies
      (localSem M [guardedHeader] (Defs.fnTable M guardedDefs)) (fun _ _ => True)
      (fun _ _ => True) (fun env results => results = sumOfProductsOf M (env.all inputs))
      (· = guardStop) :=
  fun path env _ =>
    (guarded_contract M).satisfies M _ guardedRef ⟨10⟩ inputs (env.all inputs) path env
      ⟨rfl, trivial⟩

/-- ...and it does not yield the sum of two products: on the inputs `1, 1, 1, 1` it stops at its
guard. -/
theorem guardedCall_not_yields (M : Model field) :
    ¬ (Subject.op (localSem M [guardedHeader] (Defs.fnTable M guardedDefs)) ⟨10⟩
      (LocalOp.call guardedRef) inputs).Yields
      (localSem M [guardedHeader] (Defs.fnTable M guardedDefs)) (fun _ _ => True)
      (fun env => sumOfProductsOf M (env.all inputs)) := by
  intro yields
  have wrong := yields [] (Env.positional (.cons (1 : Nat) (.cons (1 : Nat) (.cons (1 : Nat)
    (.cons (1 : Nat) .nil))))) trivial
  change (Process.halt guardStop : Local (HList M.Val [.nat])) =
    .done (.cons (2 : Nat) .nil) at wrong
  cases wrong

end Zkc.Core.SubjectsTests
