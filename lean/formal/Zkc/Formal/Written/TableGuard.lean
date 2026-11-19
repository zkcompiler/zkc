module

public import Zkc.Formal.Written.TableVerifier

@[expose] public section
namespace Zkc.Formal.Written.TableVerifier
open Core Frontend.Emit
variable {b : Bindings} {hs : Headers b.vocabulary} {domain : b.vocabulary.Ty}
variable (calls : Calls hs domain) (M : Model b.vocabulary) (fns : FnTable M hs.fns)
variable (roles : RTable M hs.protocols)

abbrev Tape := Fin 40 → Fin 1024
abbrev indices (tape : Tape) := List.ofFn fun j => (tape j).val
abbrev batch {α : Type} (tape : Tape) (data : Fin 1024 → α) := List.ofFn fun j => data (tape j)

/-- Public row values are tied to the two actual called entries, the scalar conversion
and the equality row. These are model-specific local operation laws. -/
structure Evaluation (p : M.Val (polynomial b)) (dom : M.Val domain)
    [DecidableEq (M.Val (scalar b))] where
  root : Fin 1024 → M.Val (nonzero b)
  coordinate : Fin 1024 → M.Val (scalar b)
  expected : Fin 1024 → M.Val (scalar b)
  pointValue : ∀ i, fns _ calls.point (.cons dom (.cons i.val .nil)) = .done (.cons (root i) .nil)
  unrefine : ∀ i, localOp M fns (.row (V := b.vocabulary) (.inl (.field .fromNonzero .koalaBear .nonzero)) _ rfl)
    (.cons (root i) .nil) = .done (.cons (coordinate i) .nil)
  polyValue : ∀ i, fns _ calls.evaluate (.cons p (.cons (coordinate i) .nil)) = .done (.cons (expected i) .nil)
  equal : ∀ x y : M.Val (scalar b), localOp M fns (.row (V := b.vocabulary) (.inl (.field .equal .koalaBear .all)) _ rfl)
    (.cons x (.cons y .nil)) = .done (.cons (decide (x = y)) .nil)

variable {handle : b.vocabulary.Ty} (h : M.Val handle)
variable (p : M.Val (polynomial b)) (dom : M.Val domain)

def startEnv (ps : List Nat) (rs : List (M.Val (scalar b))) : Env (RV M 1) (ready domain handle) :=
  ((((((((Env.empty.extend (names domain) (.cons p (.cons dom .nil))).insert 2 ()).insert 3 h).insert
    4 ps).insert 5 ()).insert 6 rs).insert 7 (h,ps,rs,())).insert 8 true).insert 9 true

variable [DecidableEq (M.Val (scalar b))] (eval : Evaluation calls M fns p dom)
variable (tape : Tape) (data : Fin 1024 → M.Val (scalar b))

private theorem readAt {V : Core.Vocabulary} (model : Model V) {fs : List (FnHeader V)} (ft : FnTable model fs)
    (item : V.Ty) (free : Ty.isLinear V item = false) (xs : List (model.Val item)) (n i : Nat)
    (x : model.Val item) (found : xs[i]? = some x) :
    localOp model ft (.owned (.seqAt item (some n) free)) (.cons xs (.cons i .nil)) = .done (.cons x .nil) := by
  simp only [localOp, ownedOp, found]

theorem iteration_value (j : Fin 40) (acc : Bool) (path : List Frame) :
    (project 1 (iteration calls handle)).denote (roleSem M 1 fns roles) path
      ((startEnv M h p dom (indices tape) (batch tape data)).extend inputs (.cons j.val (.cons acc .nil))) =
      .done (.cons (acc && decide (data (tape j) = eval.expected (tape j))) .nil) := by
  have getRow : localOp M fns (.owned (.seqAt (scalar b) (some 40) rfl))
      (.cons (batch tape data) (.cons j.val .nil)) = .done (.cons (data (tape j)) .nil) := by
    have found : (batch tape data)[j.val]? = some (data (tape j)) := by
      simp only [batch, List.getElem?_ofFn, j.isLt, dite_eq_left]
    exact readAt M fns _ _ _ _ _ _ found
  have getIndex : localOp M fns (.owned (.seqAt (.fin 1024) (some 40) rfl))
      (.cons (indices tape) (.cons j.val .nil)) = .done (.cons (tape j).val .nil) := by
    have found : (indices tape)[j.val]? = some ((tape j).val) := by
      simp only [indices, List.getElem?_ofFn, j.isLt, dite_eq_left]
    exact readAt M fns _ _ _ _ _ _ found
  change ((liftLocal id (localOp M fns (.owned (.seqAt (scalar b) (some 40) rfl)) (.cons (batch tape data) (.cons j.val .nil)))).map _).bind _ = _
  rw [getRow]
  change ((liftLocal id (localOp M fns (.owned (.seqAt (.fin 1024) (some 40) rfl)) (.cons (indices tape) (.cons j.val .nil)))).map _).bind _ = _
  rw [getIndex]
  change ((liftLocal id (fns _ calls.point (.cons dom (.cons (tape j).val .nil)))).map _).bind _ = _
  rw [eval.pointValue (tape j)]
  change ((liftLocal id (localOp M fns _ (.cons (eval.root (tape j)) .nil))).map _).bind _ = _
  erw [eval.unrefine (tape j)]
  change ((liftLocal id (fns _ calls.evaluate (.cons p (.cons (eval.coordinate (tape j)) .nil)))).map _).bind _ = _
  rw [eval.polyValue (tape j)]
  change ((liftLocal id (localOp M fns _ (.cons (data (tape j)) (.cons (eval.expected (tape j)) .nil)))).map _).bind _ = _
  erw [eval.equal (data (tape j)) (eval.expected (tape j))]
  rfl

abbrev sem := roleSem M 1 fns roles
abbrev Acc := (sem (hs := hs) M fns roles).LoopState [verifier .bool] []
def accumulator (v : Bool) : Acc (hs := hs) M fns roles := (.cons v .nil,.nil)

def step (ps : List Nat) (rs : List (M.Val (scalar b))) :=
  (sem M fns roles).loopStep (each := []) (carried := [verifier .bool]) [1] inputs
    ((project 1 (iteration calls handle)).denote (sem M fns roles)) ⟨16⟩ [] (startEnv M h p dom ps rs)

theorem step_value (j : Fin 40) (acc : Bool) :
    step calls M fns roles h p dom (indices tape) (batch tape data) j.val (accumulator M fns roles acc) =
    .done (accumulator M fns roles (acc && decide (data (tape j) = eval.expected (tape j)))) := by
  change ((project 1 (iteration calls handle)).denote (sem M fns roles) [.iteration ⟨16⟩ j.val]
    ((startEnv M h p dom (indices tape) (batch tape data)).extend inputs (.cons j.val (.cons acc .nil)))).bind _ = _
  rw [iteration_value calls M fns roles h p dom eval tape data j acc]
  rfl

/-- The Boolean carried by the verifier loop after the first `i` comparisons. -/
def prefixMatches {size : Nat} (check : Fin size → Bool) (i : Nat) : Bool :=
  decide (∀ j : Fin size, j.val < i → check j = true)

private theorem prefixMatches_succ {size : Nat} (f : Fin size → Bool) (j : Fin size) :
    (prefixMatches f j.val && f j) = prefixMatches f (j.val+1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [prefixMatches, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨prev, last⟩ k hk
    by_cases e : k.val = j.val
    · exact (Fin.ext e : k = j).symm ▸ last
    · exact prev k (by omega)
  · intro all
    exact ⟨fun k hk => all k (by omega), all j (by omega)⟩

theorem loop_value {n i : Nat} (within : i+n ≤ 40) :
    Process.iterate n (step calls M fns roles h p dom (indices tape) (batch tape data)) i
      (accumulator M fns roles (prefixMatches (fun j => decide (data (tape j) = eval.expected (tape j))) i)) =
    .done (accumulator M fns roles (prefixMatches (fun j => decide (data (tape j) = eval.expected (tape j))) (i+n))) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    let j : Fin 40 := ⟨i,by omega⟩
    rw [Process.iterate, step_value calls M fns roles h p dom eval tape data j]
    rw [prefixMatches_succ (fun k => decide (data (tape k) = eval.expected (tape k))) j]
    exact (ih (i := i+1) (by omega)).trans (by rw [Nat.add_right_comm]; rfl)

end Zkc.Formal.Written.TableVerifier
