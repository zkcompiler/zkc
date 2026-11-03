module

public import Zkc.Source.Structured.CustodyAdmission
public import Zkc.Source.Structured.Interpretation
public import Zkc.Source.Structured.Frame
public import Zkc.Semantics.Custody

@[expose] public section

/-! Custody soundness of the structured evaluator.

Custody values carry no payload. The structured evaluator gives the three
custody transfers a configurable effect (`SiteObservations`); its defaults are
the payload-erased meaning used by participant execution, where every token is
zero and nothing is checked. This module gives the checked meaning: the
transfers become requests of the custody ledger (`PIR.Custody`) for one holder.
Three theorems justify the erasure on admitted bodies:

* `custody_erasure`: the erased meaning is exactly the checked meaning with its
  custody requests interpreted away (`PIR.Custody.forget`);
* `Region.custodySound`: on a body admitted as a custody frame
  (`Region.custodyFrame`), the checked run never refuses, preserves every entry
  the body does not hold, returns distinct live entries of the holder for its
  custody results, and agrees with the erased run on every data position and
  every stop;
* `custody_frames_sound`: every custody frame of an admitted helper table is
  sound in this sense, and every custody-free helper of it makes no custody
  request.

In a custody frame, custody transfers and custody values stay on the spine:
custody transfers, site marks, calls of custody-free helpers and helper-free
operations on data with custody-free callbacks, each custody variable used at
most once. Frame entry, return and stop are ledger operations at the call
boundary (`PIR.Custody.Ledger.enter`, `exit`, `stop`), whose effect on live
entries `PIR.Custody.Ledger.returnFrame_live` and `stop_live` state. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
open PIR.Custody (Ledger Token)

/-- The checked custody meaning of one holder's evaluation. -/
def custodyObservations (holder : String) : SiteObservations PIR.Custody.interface where
  mark _ := .done ()
  createUnit slot := .call (.create slot holder) fun token => .done token
  passUnit slot token := .call (.pass slot holder token) fun next => .done next
  consumeUnit slot token := .call (.consume slot holder token) fun _ => .done ()

theorem custodyObservations_forget (holder : String) :
    SiteObservations.Interprets PIR.Custody.forget (custodyObservations holder) .closed :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Erasure -/

section Erasure
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The erased meaning is the checked meaning with its custody requests
interpreted away, for every body, including dormant callbacks. -/
theorem custody_erasure (holder : String)
    {left : Evaluation.Meanings F G PIR.Custody.interface} {right : Meanings F G}
    (tables : HelperTable.Interprets PIR.Custody.forget left right)
    {Γ out : List Ty} (region : Region dialect Γ out) (env : Environment (assignment F G) Γ) :
    (region.denote (Evaluation.meaning (custodyObservations holder) left) env).interpret
        PIR.Custody.forget =
      region.denote (Evaluation.meaning .closed right) env :=
  Evaluation.denote_interpret _ (custodyObservations_forget holder) tables region env

/-- The checked and erased helper tables of the same definitions correspond. -/
theorem custody_tables_erasure (holder : String) (definitions : List CheckedDefinition) :
    HelperTable.Interprets PIR.Custody.forget
      (definitions.foldl (Evaluation.extendMeanings (F := F) (G := G) (custodyObservations holder)) [])
      (definitions.foldl (Evaluation.extendMeanings .closed) []) :=
  Evaluation.foldMeanings_interpret _ (custodyObservations_forget holder) (.empty _) definitions

end Erasure

/-! ## Soundness of custody frames -/

theorem Var.weakenPrefix_index {Γ : List Ty} {ty : Ty} :
    (extra : List Ty) → (position : Var Γ ty) →
    (position.weakenPrefix extra).index = position.index + extra.length
  | [], _ => rfl
  | _ :: rest, position => by
    simp only [Var.weakenPrefix, Var.index, List.length_cons, weakenPrefix_index rest position]
    omega

/-- A position of a prefixed context is a prefix position or a weakened position. -/
theorem Var.prefixCases {Γ : List Ty} : {Δ : List Ty} → {ty : Ty} → (position : Var (Δ ++ Γ) ty) →
    (∃ inner : Var Δ ty, position.index = inner.index ∧
      ∀ (Value : Ty → Type) (env : Environment Value Γ) (values : Values Value Δ),
        env.prepend values position = values.get inner) ∨
    (∃ outer : Var Γ ty, position = outer.weakenPrefix Δ)
  | [], _, position => .inr ⟨position, rfl⟩
  | _ :: _, _, .here => .inl ⟨.here, rfl, fun _ _ values => by cases values; rfl⟩
  | _ :: _, _, .there position => by
    rcases prefixCases position with ⟨inner, index, value⟩ | ⟨outer, rfl⟩
    · refine .inl ⟨.there inner, by simp [Var.index, index], fun Value env values => ?_⟩
      cases values with
      | cons head rest =>
        simp only [Environment.prepend, Environment.push, Values.get]
        exact value Value env rest
    · exact .inr ⟨outer, rfl⟩

/-- A list type without custody positions. -/
theorem Ty.not_custody_of_any {types : List Ty} (data : types.any Ty.isCustody = false)
    {ty : Ty} (position : Var types ty) : ty.isCustody = false := by
  induction position with
  | here => simp only [List.any_cons, Bool.or_eq_false_iff] at data; exact data.1
  | there _ ih => simp only [List.any_cons, Bool.or_eq_false_iff] at data; exact ih data.2

section Soundness
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Every data position agrees; custody positions carry the tokens of their own run. -/
def DataAgree {Γ : List Ty} (left right : Environment (assignment F G) Γ) : Prop :=
  ∀ {ty : Ty} (position : Var Γ ty), ty.isCustody = false → left position = right position

/-- The custody positions of a frame that are not spent hold distinct live
entries of the holder, of their slot, in the current frame. -/
structure Holds (holder : String) (ledger : Ledger) {Γ : List Ty} (spent : List Nat)
    (env : Environment (assignment F G) Γ) : Prop where
  bounded : ledger.Bounded
  live : ∀ {slot : String} (position : Var Γ (.resourceUnit slot)), position.index ∉ spent →
    ∃ entry ∈ ledger.live, entry.token = env position ∧ entry.slot = slot ∧
      entry.holder = holder ∧ entry.frame = ledger.depth
  distinct : ∀ {first second : String} (left : Var Γ (.resourceUnit first))
    (right : Var Γ (.resourceUnit second)), left.index ∉ spent → right.index ∉ spent →
    (env left : Token) = env right → left.index = right.index

/-- The tokens a frame may still use. -/
def Available {Γ : List Ty} (spent : List Nat) (env : Environment (assignment F G) Γ)
    (token : Token) : Prop :=
  ∃ slot, ∃ position : Var Γ (.resourceUnit slot), position.index ∉ spent ∧ env position = token

/-- What a sound custody run guarantees against the erased run of the same body:
no refusal, a bounded ledger in the same frame, every entry the body does not
hold preserved, new entries fresh, and on return distinct live custody results
and equal data; on a stop, the same stop. -/
def Agrees (holder : String) (ledger : Ledger) (held : Token → Prop) {out : List Ty}
    (run : PIR.Execution Ledger PIR.Custody.Request (Values (assignment F G) out))
    (erased : PIR.Process closedInterface (Values (assignment F G) out)) : Prop :=
  run.state.refused = ledger.refused ∧ run.state.Bounded ∧ run.state.depth = ledger.depth ∧
  ledger.next ≤ run.state.next ∧
  (∀ entry ∈ ledger.live, ¬ held entry.token → entry ∈ run.state.live) ∧
  (∀ entry ∈ run.state.live, entry ∈ ledger.live ∨ ledger.next ≤ entry.token) ∧
  match run.outcome with
  | .returned values => ∃ erasedValues, erased = .done erasedValues ∧
      (∀ {ty : Ty} (position : Var out ty), ty.isCustody = false →
        values.get position = erasedValues.get position) ∧
      Holds holder run.state [] values.get
  | .stopped reason => erased = .halt reason

/-- A closed helper table read in another interface: same bodies, no new calls. -/
def liftTable {I : PIR.Signature} (table : Meanings F G) : Evaluation.Meanings F G I :=
  table.map fun entry => ⟨entry.helper, fun args => (entry.invoke args).interpret closedLift⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem liftTable_interprets {I : PIR.Signature} :
    (table : Meanings F G) → HelperTable.Interprets closedLift table (liftTable (I := I) table)
  | [] => .empty _
  | entry :: rest => by
    simp only [liftTable, List.map_cons]
    exact (liftTable_interprets rest).cons entry.helper _ _ (fun _ => rfl)

/-- Apart from site marks and custody transfers, an operation does not consult
its observations. -/
theorem operation_sites_congr {I : PIR.Signature} (left right : SiteObservations I)
    (table : Evaluation.Meanings F G I) (op : Op) (marks : left.mark = right.mark)
    (notCustody : op.isCustody = false) :
    Evaluation.operation left table op = Evaluation.operation right table op := by
  cases op with
  | createUnit | passUnit | consumeUnit => simp [Op.isCustody] at notCustody
  | mark site =>
    funext arguments callbacks
    cases arguments
    cases callbacks
    change (left.mark site).bind _ = (right.mark site).bind _
    rw [marks]
  | makeProduct =>
    funext arguments callbacks
    cases callbacks
    rfl
  | getProduct | fieldEmbed | vectorLength =>
    funext arguments callbacks
    cases arguments with
    | cons value rest => cases rest; cases callbacks; rfl
  | indexConstant | fieldConstant | booleanConstant | groupIdentity =>
    funext arguments callbacks
    cases arguments
    cases callbacks
    rfl
  | indexEqual | indexLess | indexPowerOfTwo | indexWrappingAdd | indexWrappingSubtract | indexBitAnd |
      indexLogicalShiftRight | multilinearRestrictPrefix | fieldAdd | fieldSubtract | fieldMultiply |
      fieldEqual | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual | boundedAt |
      groupAdd | groupScale | groupEqual =>
    funext arguments callbacks
    cases arguments with
    | cons a rest =>
      cases rest with
      | cons b rest => cases rest; cases callbacks; rfl
  | select =>
    funext arguments callbacks
    cases arguments with
    | cons condition rest =>
      cases rest with
      | cons yes rest =>
        cases rest with
        | cons no rest => cases rest; cases callbacks; rfl
  | exec | invoke | fold | collect | map =>
    funext arguments callbacks
    cases callbacks
    rfl
  | branch =>
    funext arguments callbacks
    cases arguments with
    | cons condition captures =>
      cases callbacks with
      | cons yes rest =>
        cases rest with
        | cons no rest => cases rest; rfl
  | loop | loopCondition =>
    funext arguments callbacks
    cases arguments with
    | cons lower rest =>
      cases rest with
      | cons upper rest =>
        cases callbacks with
        | cons body rest => cases rest; rfl
  | guard =>
    funext arguments callbacks
    cases arguments with
    | cons condition rest => cases rest; cases callbacks; rfl

/-- A helper-free operation that is not a custody transfer has the same
checked and erased meaning, with no custody request. -/
theorem operation_pure_lift (holder : String) (tL : Evaluation.Meanings F G PIR.Custody.interface)
    (tE : Meanings F G) (op : Op) (notCustody : op.isCustody = false) (noHelpers : op.helpers = [])
    (args : Values (assignment F G) op.arguments)
    (bodies : Values (RegionFunction (assignment F G) closedInterface) op.regions) :
    Evaluation.operation (custodyObservations holder) tL op args
        (RegionFunctions.translate (dialect := dialect) closedLift bodies) =
      (Evaluation.operation .closed tE op args bodies).interpret closedLift := by
  rw [Evaluation.operation_interpret closedLift SiteObservations.closed_interpret
    (liftTable_interprets tE) op args bodies]
  rw [operation_sites_congr (custodyObservations holder) (.silent _) tL op rfl notCustody]
  rw [Evaluation.operation_table_congr (.silent _) tL (liftTable tE) op
    (by intro helper member; rw [noHelpers] at member; cases member)]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Agrees.mono {holder : String} {ledger : Ledger} {held narrow : Token → Prop}
    {out : List Ty} {run : PIR.Execution Ledger PIR.Custody.Request (Values (assignment F G) out)}
    {erased : PIR.Process closedInterface (Values (assignment F G) out)}
    (within : ∀ token, narrow token → held token) (agrees : Agrees holder ledger narrow run erased) :
    Agrees holder ledger held run erased := by
  obtain ⟨refused, bounded, depth, next, keeps, fresh, outcome⟩ := agrees
  exact ⟨refused, bounded, depth, next,
    fun entry member outside => keeps entry member (fun inside => outside (within _ inside)),
    fresh, outcome⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Agrees.halt {holder : String} {ledger : Ledger} {held : Token → Prop} {out : List Ty}
    (bounded : ledger.Bounded) (reason : PIR.Stop) (events : List PIR.Custody.Request) :
    Agrees (F := F) (G := G) (out := out) holder ledger held ⟨.stopped reason, ledger, events⟩
      (.halt reason) :=
  ⟨rfl, bounded, rfl, Nat.le_refl _, fun _ member _ => member, fun _ member => .inl member, rfl⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A returned step followed by a sound continuation is sound. -/
theorem Agrees.step {holder : String} {ledger after : Ledger} {held rest : Token → Prop}
    {out : List Ty} {A : Type} {value : A} {events : List PIR.Custody.Request}
    {continuation : A → Ledger → PIR.Execution Ledger PIR.Custody.Request (Values (assignment F G) out)}
    {erased : PIR.Process closedInterface (Values (assignment F G) out)}
    (refused : after.refused = ledger.refused) (depth : after.depth = ledger.depth)
    (next : ledger.next ≤ after.next)
    (keeps : ∀ entry ∈ ledger.live, ¬ held entry.token → entry ∈ after.live ∧ ¬ rest entry.token)
    (fresh : ∀ entry ∈ after.live, entry ∈ ledger.live ∨ ledger.next ≤ entry.token)
    (sound : Agrees holder after rest (continuation value after) erased) :
    Agrees holder ledger held
      ((⟨.returned value, after, events⟩ : PIR.Execution Ledger PIR.Custody.Request A).follow
        continuation) erased := by
  obtain ⟨refused', bounded, depth', next', keeps', fresh', outcome⟩ := sound
  refine ⟨refused'.trans refused, bounded, depth'.trans depth, Nat.le_trans next next', ?_, ?_, outcome⟩
  · intro entry member outside
    obtain ⟨inner, outside'⟩ := keeps entry member outside
    exact keeps' entry inner outside'
  · intro entry member
    rcases fresh' entry member with old | new
    · exact fresh entry old
    · exact .inr (Nat.le_trans next new)

/-- The process of a callback-free step that returns values without custody
results, read in the checked interface. -/
theorem lifted_run {A : Type} (process : PIR.Process closedInterface A) (ledger : Ledger) :
    (process.interpret closedLift).run PIR.Custody.handler ledger =
      match process with
      | .done value => ⟨.returned value, ledger, []⟩
      | .halt reason => ⟨.stopped reason, ledger, []⟩
      | .call impossible _ => nomatch impossible := by
  cases process with
  | done => rfl
  | halt => rfl
  | call impossible => exact nomatch impossible

/-! ### Frame invariants across one step -/

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Prepending results without custody positions keeps the frame invariant. -/
theorem Holds.prepend_data {holder : String} {ledger : Ledger} {Γ Δ : List Ty}
    {spent spent' : List Nat} {env : Environment (assignment F G) Γ}
    (holds : Holds holder ledger spent env) (values : Values (assignment F G) Δ)
    (data : Δ.any Ty.isCustody = false) (shifted : ∀ index ∈ spent, index + Δ.length ∈ spent') :
    Holds holder ledger spent' (env.prepend values) where
  bounded := holds.bounded
  live := by
    intro slot position unspent
    rcases Var.prefixCases position with ⟨inner, _, _⟩ | ⟨outer, rfl⟩
    · exact absurd (Ty.not_custody_of_any data inner) (by simp [Ty.isCustody])
    · rw [Environment.prepend_weakenPrefix]
      refine holds.live outer fun member => unspent ?_
      rw [Var.weakenPrefix_index]
      exact shifted _ member
  distinct := by
    intro first second left right leftUnspent rightUnspent same
    rcases Var.prefixCases left with ⟨inner, _, _⟩ | ⟨leftOuter, rfl⟩
    · exact absurd (Ty.not_custody_of_any data inner) (by simp [Ty.isCustody])
    rcases Var.prefixCases right with ⟨inner, _, _⟩ | ⟨rightOuter, rfl⟩
    · exact absurd (Ty.not_custody_of_any data inner) (by simp [Ty.isCustody])
    rw [Environment.prepend_weakenPrefix, Environment.prepend_weakenPrefix] at same
    rw [Var.weakenPrefix_index, Var.weakenPrefix_index]
    have equal := holds.distinct leftOuter rightOuter
      (fun member => leftUnspent (by rw [Var.weakenPrefix_index]; exact shifted _ member))
      (fun member => rightUnspent (by rw [Var.weakenPrefix_index]; exact shifted _ member)) same
    rw [equal]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Available.prepend_data {Γ Δ : List Ty} {spent spent' : List Nat}
    {env : Environment (assignment F G) Γ} (values : Values (assignment F G) Δ)
    (data : Δ.any Ty.isCustody = false) (shifted : ∀ index ∈ spent, index + Δ.length ∈ spent')
    {token : Token} (available : Available spent' (env.prepend values) token) :
    Available spent env token := by
  obtain ⟨slot, position, unspent, same⟩ := available
  rcases Var.prefixCases position with ⟨inner, _, _⟩ | ⟨outer, rfl⟩
  · exact absurd (Ty.not_custody_of_any data inner) (by simp [Ty.isCustody])
  · refine ⟨slot, outer, fun member => unspent ?_, ?_⟩
    · rw [Var.weakenPrefix_index]
      exact shifted _ member
    · exact (Environment.prepend_weakenPrefix env values outer).symm.trans same

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Binding one new custody result keeps the frame invariant of a ledger that
holds it and every still available entry. -/
theorem Holds.push {holder : String} {ledger : Ledger} {Γ : List Ty} {slot : String}
    {spent spent' : List Nat} {env : Environment (assignment F G) Γ} (token : Token)
    (bounded : ledger.Bounded)
    (here : ∃ entry ∈ ledger.live, entry.token = token ∧ entry.slot = slot ∧
      entry.holder = holder ∧ entry.frame = ledger.depth)
    (old : ∀ {other : String} (position : Var Γ (.resourceUnit other)), position.index ∉ spent →
      ∃ entry ∈ ledger.live, entry.token = env position ∧ entry.slot = other ∧
        entry.holder = holder ∧ entry.frame = ledger.depth)
    (distinct : ∀ {first second : String} (left : Var Γ (.resourceUnit first))
      (right : Var Γ (.resourceUnit second)), left.index ∉ spent → right.index ∉ spent →
      (env left : Token) = env right → left.index = right.index)
    (fresh : ∀ {other : String} (position : Var Γ (.resourceUnit other)), position.index ∉ spent →
      (env position : Token) ≠ token)
    (shifted : ∀ index ∈ spent, index + 1 ∈ spent') :
    Holds holder ledger spent' (Environment.push (ty := .resourceUnit slot) env token) where
  bounded := bounded
  live := by
    intro other position unspent
    cases position with
    | here => exact here
    | there position =>
      exact old position fun member => unspent (by simp only [Var.index]; exact shifted _ member)
  distinct := by
    intro first second left right leftUnspent rightUnspent same
    cases left with
    | here =>
      cases right with
      | here => rfl
      | there right =>
        exact absurd same.symm (fresh right fun member =>
          rightUnspent (by simp only [Var.index]; exact shifted _ member))
    | there left =>
      cases right with
      | here =>
        exact absurd same (fresh left fun member =>
          leftUnspent (by simp only [Var.index]; exact shifted _ member))
      | there right =>
        simp only [Var.index]
        exact congrArg (· + 1) (distinct left right
          (fun member => leftUnspent (by simp only [Var.index]; exact shifted _ member))
          (fun member => rightUnspent (by simp only [Var.index]; exact shifted _ member)) same)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Available.push {Γ : List Ty} {slot : String} {spent spent' : List Nat}
    {env : Environment (assignment F G) Γ} {token other : Token}
    (shifted : ∀ index ∈ spent, index + 1 ∈ spent')
    (available : Available spent' (Environment.push (ty := .resourceUnit slot) env token) other) :
    other = token ∨ Available spent env other := by
  obtain ⟨found, position, unspent, same⟩ := available
  cases position with
  | here => exact .inl same.symm
  | there position =>
    exact .inr ⟨found, position, fun member =>
      unspent (by simp only [Var.index]; exact shifted _ member), same⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A step without custody requests, read from its erased process. -/
theorem Agrees.lifted {holder : String} {ledger : Ledger} {held : Token → Prop}
    {out : List Ty} {A : Type} (process : PIR.Process closedInterface A) {rest : A → Token → Prop}
    {continuation : A → Ledger → PIR.Execution Ledger PIR.Custody.Request (Values (assignment F G) out)}
    {erased : A → PIR.Process closedInterface (Values (assignment F G) out)}
    (bounded : ledger.Bounded)
    (keeps : ∀ value, ∀ entry ∈ ledger.live, ¬ held entry.token → ¬ rest value entry.token)
    (sound : ∀ value, process = .done value →
      Agrees holder ledger (rest value) (continuation value ledger) (erased value)) :
    Agrees holder ledger held
      (((process.interpret closedLift).run PIR.Custody.handler ledger).follow continuation)
      (process.bind erased) := by
  cases process with
  | done value =>
    exact Agrees.step (after := ledger) rfl rfl (Nat.le_refl _)
      (fun entry member outside => ⟨member, keeps value entry member outside⟩)
      (fun _ member => .inl member) (sound value rfl)
  | halt reason => exact Agrees.halt bounded reason []
  | call impossible => exact nomatch impossible

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Holds.mono {holder : String} {ledger : Ledger} {Γ : List Ty} {spent more : List Nat}
    {env : Environment (assignment F G) Γ} (within : ∀ index ∈ spent, index ∈ more)
    (holds : Holds holder ledger spent env) : Holds holder ledger more env where
  bounded := holds.bounded
  live position unspent := holds.live position fun member => unspent (within _ member)
  distinct left right leftUnspent rightUnspent same :=
    holds.distinct left right (fun member => leftUnspent (within _ member))
      (fun member => rightUnspent (within _ member)) same

/-- A custody-free region under the checked meaning is its erased meaning lifted,
given checked and erased tables that agree on the custody-free helpers. -/
theorem region_free_denote (holder : String) {custodyFree : String → Bool}
    {tL : Evaluation.Meanings F G PIR.Custody.interface} {tE : Meanings F G}
    (free : ∀ helper : Helper, custodyFree helper.name = true →
      ∀ args, invoke tL helper args = (invoke tE helper args).interpret closedLift)
    {Γ out : List Ty} (region : Region dialect Γ out)
    (steps : region.erase.operations.all (Op.custodyFreeStep custodyFree) = true)
    (env : Environment (assignment F G) Γ) :
    region.denote (Evaluation.meaning (custodyObservations holder) tL) env =
      (region.denote (Evaluation.meaning .closed tE) env).interpret closedLift := by
  rw [Evaluation.denote_interpret closedLift SiteObservations.closed_interpret
    (liftTable_interprets tE) region env]
  have operations : ∀ op ∈ region.erase.operations,
      Evaluation.operation (custodyObservations holder) tL op =
        Evaluation.operation (.silent _) (liftTable tE) op := by
    intro op member
    have step := List.all_eq_true.mp steps op member
    simp only [Op.custodyFreeStep, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.all_eq_true] at step
    obtain ⟨⟨notCustody, _⟩, helpers⟩ := step
    rw [operation_sites_congr (custodyObservations holder) (.silent _) tL op rfl notCustody]
    apply Evaluation.operation_table_congr
    intro helper used
    funext args
    rw [free helper (helpers helper used) args]
    exact liftTable_interprets tE helper args
  exact congrFun (Region.denote_congr (Evaluation.operation (custodyObservations holder) tL)
    (Evaluation.operation (.silent _) (liftTable tE)) region operations) env

/-- Custody-free callbacks are their erased callbacks lifted. -/
theorem regions_free_translate (holder : String) {custodyFree : String → Bool}
    {tL : Evaluation.Meanings F G PIR.Custody.interface} {tE : Meanings F G}
    (free : ∀ helper : Helper, custodyFree helper.name = true →
      ∀ args, invoke tL helper args = (invoke tE helper args).interpret closedLift) :
    {signatures : List (List Ty × List Ty)} → (bodies : Regions dialect signatures) →
    bodies.erase.operations.all (Op.custodyFreeStep custodyFree) = true →
    bodies.denote (Evaluation.meaning (custodyObservations holder) tL) =
      RegionFunctions.translate (dialect := dialect) closedLift
        (bodies.denote (Evaluation.meaning .closed tE))
  | _, .nil, _ => rfl
  | _, .cons body tail, steps => by
    simp only [Regions.erase, RawRegions.operations, List.all_append, Bool.and_eq_true] at steps
    simp only [Regions.denote, RegionFunctions.translate]
    congr 1
    · funext values
      exact region_free_denote holder free body steps.1 _
    · exact regions_free_translate holder free tail steps.2

theorem Op.custodyStep_pure {custodyFree : String → Bool} {op : Op}
    (step : op.custodyStep custodyFree = true) (notCustody : op.isCustody = false)
    (notInvoke : ∀ helper, op ≠ .invoke helper) :
    op.helpers = [] ∧ (op.arguments ++ op.results).any Ty.isCustody = false := by
  cases op <;> simp_all [Op.custodyStep, Op.isCustody, Op.helpers, Op.arguments, Op.results]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Operands.eval_data {Γ : List Ty} {envL envE : Environment (assignment F G) Γ}
    (agree : DataAgree envL envE) : {args : List Ty} → (operands : Operands Γ args) →
    args.any Ty.isCustody = false → Operands.eval envL operands = Operands.eval envE operands
  | [], .nil, _ => rfl
  | _ :: _, .cons position rest, data => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at data
    exact congrArg₂ Values.cons (agree position data.1) (eval_data agree rest data.2)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem DataAgree.prepend {Γ Δ : List Ty} {envL envE : Environment (assignment F G) Γ}
    (agree : DataAgree envL envE) (values : Values (assignment F G) Δ) :
    DataAgree (envL.prepend values) (envE.prepend values) := by
  intro ty position notCustody
  change envL.prepend values position = envE.prepend values position
  rcases Var.prefixCases position with ⟨inner, _, value⟩ | ⟨outer, rfl⟩
  · rw [value, value]
  · rw [Environment.prepend_weakenPrefix, Environment.prepend_weakenPrefix]
    exact agree outer notCustody

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem DataAgree.push_custody {Γ : List Ty} {slot : String} {envL envE : Environment (assignment F G) Γ}
    (agree : DataAgree envL envE) (left right : Token) :
    DataAgree (Environment.push (ty := .resourceUnit slot) envL left)
      (Environment.push (ty := .resourceUnit slot) envE right) := by
  intro ty position notCustody
  cases position with
  | here => simp [Ty.isCustody] at notCustody
  | there position => exact agree position notCustody

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem Available.mono {Γ : List Ty} {spent more : List Nat} {env : Environment (assignment F G) Γ}
    (within : ∀ index ∈ spent, index ∈ more) {token : Token} (available : Available more env token) :
    Available spent env token := by
  obtain ⟨slot, position, unspent, same⟩ := available
  exact ⟨slot, position, fun member => unspent (within _ member), same⟩

/-! ### The three transfers under the ledger -/

theorem create_run (holder slot : String) (tL : Evaluation.Meanings F G PIR.Custody.interface)
    (ledger : Ledger) :
    (Evaluation.operation (custodyObservations holder) tL (.createUnit slot) .nil .nil).run
        PIR.Custody.handler ledger =
      ⟨.returned (.cons (ledger.create slot holder).1 .nil), (ledger.create slot holder).2,
        [.create slot holder]⟩ := rfl

theorem pass_run (holder slot : String) (tL : Evaluation.Meanings F G PIR.Custody.interface)
    {ledger after : Ledger} {token successor : Token}
    (passed : ledger.pass slot holder token = .ok (successor, after)) :
    (Evaluation.operation (custodyObservations holder) tL (.passUnit slot) (.cons token .nil) .nil).run
        PIR.Custody.handler ledger =
      ⟨.returned (.cons successor .nil), after, [.pass slot holder token]⟩ := by
  change (PIR.Custody.handler (.pass slot holder token) ledger).follow _ = _
  simp only [PIR.Custody.handler, passed]
  rfl

theorem consume_run (holder slot : String) (tL : Evaluation.Meanings F G PIR.Custody.interface)
    {ledger after : Ledger} {token : Token}
    (consumed : ledger.consume slot holder token = .ok after) :
    (Evaluation.operation (custodyObservations holder) tL (.consumeUnit slot) (.cons token .nil) .nil).run
        PIR.Custody.handler ledger =
      ⟨.returned .nil, after, [.consume slot holder token]⟩ := by
  change (PIR.Custody.handler (.consume slot holder token) ledger).follow _ = _
  simp only [PIR.Custody.handler, consumed]
  rfl

theorem create_erased (slot : String) (tE : Meanings F G) :
    Evaluation.operation .closed tE (.createUnit slot) .nil .nil = .done (.cons 0 .nil) := rfl

theorem pass_erased (slot : String) (tE : Meanings F G) (token : Token) :
    Evaluation.operation .closed tE (.passUnit slot) (.cons token .nil) .nil = .done (.cons 0 .nil) := rfl

theorem consume_erased (slot : String) (tE : Meanings F G) (token : Token) :
    Evaluation.operation .closed tE (.consumeUnit slot) (.cons token .nil) .nil = .done .nil := rfl

theorem _root_.Zkc.Source.Region.custodySound {holder : String} {custodyFree : String → Bool}
    {tL : Evaluation.Meanings F G PIR.Custody.interface} {tE : Meanings F G}
    (free : ∀ helper : Helper, custodyFree helper.name = true →
      ∀ args, invoke tL helper args = (invoke tE helper args).interpret closedLift)
    {Γ out : List Ty} (region : Region dialect Γ out) :
    ∀ (spent : List Nat), region.custodyFrame custodyFree spent = true →
    ∀ (envL envE : Environment (assignment F G) Γ) (ledger : Ledger),
      DataAgree envL envE → Holds holder ledger spent envL →
      Agrees holder ledger (Available spent envL)
        ((region.denote (Evaluation.meaning (custodyObservations holder) tL) envL).run
          PIR.Custody.handler ledger)
        (region.denote (Evaluation.meaning .closed tE) envE) := by
  refine Region.rec (dialect := dialect)
    (motive_1 := fun Γ out region => ∀ (spent : List Nat),
      region.custodyFrame custodyFree spent = true →
      ∀ (envL envE : Environment (assignment F G) Γ) (ledger : Ledger),
        DataAgree envL envE → Holds holder ledger spent envL →
        Agrees holder ledger (Available spent envL)
          ((region.denote (Evaluation.meaning (custodyObservations holder) tL) envL).run
            PIR.Custody.handler ledger)
          (region.denote (Evaluation.meaning .closed tE) envE))
    (motive_2 := fun _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ region
  · intro Γ out values spent admitted envL envE ledger agree holds
    simp only [Region.custodyFrame, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at admitted
    obtain ⟨unique, unspent⟩ := admitted
    have notSpent : ∀ {slot : String} (position : Var out (.resourceUnit slot)),
        (values.get position).index ∉ spent := by
      intro slot position member
      have available := unspent _ (Operands.custodyIndices_mem values position)
      simp [member] at available
    refine ⟨rfl, holds.bounded, rfl, Nat.le_refl _, fun _ member _ => member,
      fun _ member => .inl member, ⟨Operands.eval envE values, rfl, ?_, ?_⟩⟩
    · intro ty position notCustody
      rw [Operands.get_eval, Operands.get_eval]
      exact agree _ notCustody
    · refine ⟨holds.bounded, ?_, ?_⟩
      · intro slot position _
        rw [Operands.get_eval]
        exact holds.live _ (notSpent position)
      · intro first second left right _ _ same
        rw [Operands.get_eval, Operands.get_eval] at same
        exact Operands.custodyIndices_inj values unique left right
          (holds.distinct _ _ (notSpent left) (notSpent right) same)
  · intro Γ out reason spent _ envL envE ledger _ holds
    exact Agrees.halt holds.bounded reason []
  · intro Γ out op arguments bodies next _ nextIH spent admitted envL envE ledger agree holds
    simp only [Region.custodyFrame, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at admitted
    obtain ⟨⟨⟨⟨step, bodiesFree⟩, unique⟩, unspent⟩, nextAdmitted⟩ := admitted
    have notSpent : ∀ {slot : String} (position : Var (dialect.arguments op) (.resourceUnit slot)),
        (arguments.get position).index ∉ spent := by
      intro slot position member
      have available := unspent _ (Operands.custodyIndices_mem arguments position)
      simp [member] at available
    have shifted : ∀ index ∈ spent ++ Operands.custodyIndices arguments,
        index + op.results.length ∈
          (spent ++ Operands.custodyIndices arguments).map (· + op.results.length) :=
      fun index member => List.mem_map.mpr ⟨index, member, rfl⟩
    have within : ∀ index ∈ spent, index ∈ spent ++ Operands.custodyIndices arguments :=
      fun index member => List.mem_append_left _ member
    have bounded := holds.bounded
    simp only [Region.denote]
    rw [PIR.run_bind]
    by_cases special : op.isCustody = true ∨ ∃ helper, op = .invoke helper
    · rcases special with custodyOp | ⟨helper, rfl⟩
      · cases op <;> simp only [Op.isCustody, Bool.false_eq_true] at custodyOp
        · -- create
          rename_i slot
          cases arguments
          cases bodies
          simp only [Operands.eval, Regions.denote]
          rw [create_run]
          refine Agrees.step rfl rfl (Nat.le_succ _) ?_ ?_
            (nextIH _ nextAdmitted _ _ _ (DataAgree.push_custody agree _ 0) ?_)
          · intro entry member outside
            refine ⟨Ledger.create_keeps ledger slot holder member, fun available => ?_⟩
            rcases Available.push shifted available with same | old
            · have below : entry.token < ledger.next := bounded.2 entry member
              rw [same] at below
              exact Nat.lt_irrefl _ below
            · exact outside (Available.mono within old)
          · intro entry member
            rcases List.mem_cons.mp member with rfl | member
            · exact .inr (Nat.le_refl _)
            · exact .inl member
          · refine Holds.push _ (Ledger.create_bounded bounded slot holder)
              ⟨_, List.mem_cons_self, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ shifted
            · intro other position unspentHere
              obtain ⟨entry, member, rest⟩ := holds.live position fun m => unspentHere (within _ m)
              exact ⟨entry, List.mem_cons_of_mem _ member, rest⟩
            · intro first second left right leftUnspent rightUnspent same
              exact holds.distinct left right (fun m => leftUnspent (within _ m))
                (fun m => rightUnspent (within _ m)) same
            · intro other position unspentHere same
              obtain ⟨entry, member, value, _⟩ := holds.live position fun m => unspentHere (within _ m)
              have below : entry.token < ledger.next := bounded.2 entry member
              have equal : entry.token = ledger.next := value.trans same
              rw [equal] at below
              exact Nat.lt_irrefl _ below
        · -- pass
          rename_i slot
          cases bodies
          cases arguments with
          | cons token rest =>
            cases rest
            simp only [Operands.eval, Regions.denote]
            obtain ⟨entry, member, value, slotSame, holderSame, frameSame⟩ :=
              holds.live token (notSpent .here)
            have checked := Ledger.check_live bounded.1 member slotSame holderSame frameSame
            rw [value] at checked
            have passed := Ledger.pass_of_check checked
            rw [pass_run holder slot tL passed]
            have available : Available spent envL (envL token) := ⟨slot, token, notSpent .here, rfl⟩
            refine Agrees.step rfl rfl (Nat.le_succ _) ?_ ?_
              (nextIH _ nextAdmitted _ _ _ (DataAgree.push_custody agree _ 0) ?_)
            · intro other inLive outside
              have different : other.token ≠ envL token := fun equal =>
                outside (equal ▸ available)
              refine ⟨List.mem_cons_of_mem _ (Ledger.mem_remove.mpr ⟨inLive, different⟩),
                fun availableNext => ?_⟩
              rcases Available.push shifted availableNext with equal | old
              · have below : other.token < ledger.next := bounded.2 other inLive
                rw [equal] at below
                exact Nat.lt_irrefl _ below
              · exact outside (Available.mono within old)
            · intro other inLive
              rcases List.mem_cons.mp inLive with rfl | inLive
              · exact .inr (Nat.le_refl _)
              · exact .inl (Ledger.mem_remove.mp inLive).1
            · refine Holds.push _ (Ledger.pass_bounded bounded passed)
                ⟨_, List.mem_cons_self, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ shifted
              · intro other position unspentHere
                obtain ⟨found, inLive, found_value, rest⟩ :=
                  holds.live position fun m => unspentHere (within _ m)
                have different : found.token ≠ envL token := by
                  intro equal
                  have same := holds.distinct position token (fun m => unspentHere (within _ m))
                    (notSpent .here) (found_value.symm.trans equal)
                  have used : token.index ∈ Operands.custodyIndices (Values.cons token Values.nil) :=
                    Operands.custodyIndices_mem (Values.cons token Values.nil) .here
                  rw [← same] at used
                  exact unspentHere (List.mem_append_right _ used)
                exact ⟨found, List.mem_cons_of_mem _ (Ledger.mem_remove.mpr ⟨inLive, different⟩),
                  found_value, rest⟩
              · intro first second left right leftUnspent rightUnspent same
                exact holds.distinct left right (fun m => leftUnspent (within _ m))
                  (fun m => rightUnspent (within _ m)) same
              · intro other position unspentHere same
                obtain ⟨found, inLive, found_value, _⟩ :=
                  holds.live position fun m => unspentHere (within _ m)
                have below : found.token < ledger.next := bounded.2 found inLive
                have equal : found.token = ledger.next := found_value.trans same
                rw [equal] at below
                exact Nat.lt_irrefl _ below
        · -- consume
          rename_i slot
          cases bodies
          cases arguments with
          | cons token rest =>
            cases rest
            simp only [Operands.eval, Regions.denote]
            obtain ⟨entry, member, value, slotSame, holderSame, frameSame⟩ :=
              holds.live token (notSpent .here)
            have checked := Ledger.check_live bounded.1 member slotSame holderSame frameSame
            rw [value] at checked
            have consumed := Ledger.consume_of_check checked
            rw [consume_run holder slot tL consumed]
            have available : Available spent envL (envL token) := ⟨slot, token, notSpent .here, rfl⟩
            have removed : Holds holder (ledger.remove (envL token))
                (spent ++ Operands.custodyIndices (Values.cons token Values.nil)) envL :=
              { bounded := Ledger.remove_bounded bounded _
                live := by
                  intro other position unspentHere
                  obtain ⟨found, inLive, found_value, rest⟩ :=
                    holds.live position fun m => unspentHere (within _ m)
                  have different : found.token ≠ envL token := by
                    intro equal
                    have same := holds.distinct position token (fun m => unspentHere (within _ m))
                      (notSpent .here) (found_value.symm.trans equal)
                    have used : token.index ∈ Operands.custodyIndices (Values.cons token Values.nil) :=
                      Operands.custodyIndices_mem (Values.cons token Values.nil) .here
                    rw [← same] at used
                    exact unspentHere (List.mem_append_right _ used)
                  exact ⟨found, Ledger.mem_remove.mpr ⟨inLive, different⟩, found_value, rest⟩
                distinct := fun left right leftUnspent rightUnspent same =>
                  holds.distinct left right (fun m => leftUnspent (within _ m))
                    (fun m => rightUnspent (within _ m)) same }
            refine Agrees.step rfl rfl (Nat.le_refl _) ?_ ?_
              (nextIH _ nextAdmitted _ _ _ (DataAgree.prepend agree .nil)
                (Holds.prepend_data removed .nil rfl shifted))
            · intro other inLive outside
              have different : other.token ≠ envL token := fun equal =>
                outside (equal ▸ available)
              refine ⟨Ledger.mem_remove.mpr ⟨inLive, different⟩, fun availableNext => ?_⟩
              exact outside (Available.mono within
                (Available.prepend_data .nil rfl shifted availableNext))
            · intro other inLive
              exact .inl (Ledger.mem_remove.mp inLive).1
      · -- a call of a custody-free helper on data
        cases bodies
        simp only [Regions.denote]
        simp only [Op.custodyStep, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at step
        obtain ⟨named, data⟩ := step
        have inputs : helper.inputs.any Ty.isCustody = false := by
          simp only [List.any_append, Bool.or_eq_false_iff] at data
          exact data.1
        have outputs : helper.outputs.any Ty.isCustody = false := by
          simp only [List.any_append, Bool.or_eq_false_iff] at data
          exact data.2
        rw [Operands.eval_data agree arguments inputs]
        change Agrees holder ledger _
          (((invoke tL helper (Operands.eval envE arguments)).run PIR.Custody.handler ledger).follow _)
          ((invoke tE helper (Operands.eval envE arguments)).bind _)
        rw [free helper named]
        refine Agrees.lifted _ bounded
          (rest := fun results => Available ((spent ++ Operands.custodyIndices arguments).map
            (· + (Op.invoke helper).results.length)) (envL.prepend results)) ?_ ?_
        · intro results entry _ outside availableNext
          exact outside (Available.mono within
            (Available.prepend_data results outputs shifted availableNext))
        · intro results _
          exact nextIH _ nextAdmitted _ _ _ (DataAgree.prepend agree results)
            (Holds.prepend_data (Holds.mono within holds) results outputs shifted)
    · -- a helper-free operation on data with custody-free callbacks
      have notCustody : op.isCustody = false := by
        cases custody : op.isCustody
        · rfl
        · exact absurd (.inl custody) special
      have notInvoke : ∀ helper, op ≠ .invoke helper := fun helper same => special (.inr ⟨helper, same⟩)
      obtain ⟨noHelpers, data⟩ := Op.custodyStep_pure step notCustody notInvoke
      have argumentsData : op.arguments.any Ty.isCustody = false := by
        simp only [List.any_append, Bool.or_eq_false_iff] at data
        exact data.1
      have resultsData : op.results.any Ty.isCustody = false := by
        simp only [List.any_append, Bool.or_eq_false_iff] at data
        exact data.2
      rw [regions_free_translate holder free bodies (List.all_eq_true.mpr bodiesFree),
        Operands.eval_data agree arguments argumentsData,
        operation_pure_lift holder tL tE op notCustody noHelpers]
      refine Agrees.lifted _ bounded
        (rest := fun results => Available ((spent ++ Operands.custodyIndices arguments).map
          (· + op.results.length)) (envL.prepend results)) ?_ ?_
      · intro results entry _ outside availableNext
        exact outside (Available.mono within
          (Available.prepend_data results resultsData shifted availableNext))
      · intro results _
        exact nextIH _ nextAdmitted _ _ _ (DataAgree.prepend agree results)
          (Holds.prepend_data (Holds.mono within holds) results resultsData shifted)
  · intro Γ mid out body next _ _ spent admitted
    simp [Region.custodyFrame] at admitted
  · trivial
  · intros
    trivial

/-! ### Admitted helper tables -/

/-- A checked table that agrees with the erased table on the named helpers:
there they make no custody request. -/
def TablesAgree (names : List String) (tL : Evaluation.Meanings F G PIR.Custody.interface)
    (tE : Meanings F G) : Prop :=
  ∀ helper : Helper, names.contains helper.name = true →
    ∀ args, invoke tL helper args = (invoke tE helper args).interpret closedLift

/-- A custody-free body under the checked meaning is its erased meaning lifted. -/
theorem custodyFree_denote (holder : String) {names : List String}
    {tL : Evaluation.Meanings F G PIR.Custody.interface} {tE : Meanings F G}
    (agree : TablesAgree names tL tE) (definition : CheckedDefinition)
    (free : definition.custodyFree names.contains = true)
    (env : Environment (assignment F G) definition.inputs) :
    definition.body.denote (Evaluation.meaning (custodyObservations holder) tL) env =
      (definition.body.denote (Evaluation.meaning .closed tE) env).interpret closedLift := by
  simp only [CheckedDefinition.custodyFree, Bool.and_eq_true] at free
  apply region_free_denote holder agree definition.body
  rw [definition.exactBody]
  exact free.2

theorem invoke_extend_other {I : PIR.Signature} (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (definition : CheckedDefinition) (helper : Helper)
    (different : definition.name ≠ helper.name) :
    invoke (Evaluation.extendMeanings observations table definition) helper = invoke table helper :=
  invoke_cons_other table _ helper different

theorem invoke_extend_same {I : PIR.Signature} (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (definition : CheckedDefinition) :
    invoke (Evaluation.extendMeanings observations table definition) definition.helper =
      fun values => definition.body.denote (Evaluation.meaning observations table) values.get :=
  invoke_cons_same table _

theorem invoke_extend_mismatch {I : PIR.Signature} (observations : SiteObservations I)
    (table : Evaluation.Meanings F G I) (definition : CheckedDefinition) (helper : Helper)
    (same : definition.name = helper.name) (different : definition.helper ≠ helper) :
    invoke (Evaluation.extendMeanings observations table definition) helper = fun _ => .halt .refused :=
  invoke_cons_mismatch table _ helper same different

theorem invoke_foldl_other {I : PIR.Signature} (observations : SiteObservations I) (helper : Helper) :
    (definitions : List CheckedDefinition) → (table : Evaluation.Meanings F G I) →
    (∀ definition ∈ definitions, definition.name ≠ helper.name) →
    invoke (definitions.foldl (Evaluation.extendMeanings observations) table) helper =
      invoke table helper
  | [], _, _ => rfl
  | definition :: rest, table, other => by
    simp only [List.foldl_cons]
    rw [invoke_foldl_other observations helper rest _
      (fun later member => other later (List.mem_cons_of_mem _ member))]
    exact invoke_extend_other observations table definition helper
      (other definition List.mem_cons_self)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem custodyFreeNames_mono : (definitions : List CheckedDefinition) → (names : List String) →
    ∀ name ∈ names, name ∈ custodyFreeNames definitions names
  | [], _, _, member => member
  | definition :: rest, names, name, member => by
    simp only [custodyFreeNames]
    apply custodyFreeNames_mono rest
    split
    · exact List.mem_cons_of_mem _ member
    · exact member

/-- Every custody frame of an admitted helper list is sound against the erased
table, and every custody-free helper agrees with it. Names are unique, as whole-
unit admission requires. -/
theorem custody_frames_sound (holder : String) :
    (definitions : List CheckedDefinition) → (names : List String) →
    (tL : Evaluation.Meanings F G PIR.Custody.interface) → (tE : Meanings F G) →
    TablesAgree names tL tE → (names ++ definitions.map (·.name)).Nodup →
    checkCustodyFrames definitions names = .ok () →
    TablesAgree (custodyFreeNames definitions names)
        (definitions.foldl (Evaluation.extendMeanings (custodyObservations holder)) tL)
        (definitions.foldl (Evaluation.extendMeanings .closed) tE) ∧
    ∀ definition ∈ definitions,
      (custodyFreeNames definitions names).contains definition.name = false →
      ∀ (argsL argsE : Values (assignment F G) definition.inputs) (ledger : Ledger),
        DataAgree argsL.get argsE.get → Holds holder ledger [] argsL.get →
        Agrees holder ledger (Available [] argsL.get)
          ((invoke (definitions.foldl (Evaluation.extendMeanings (custodyObservations holder)) tL)
            definition.helper argsL).run PIR.Custody.handler ledger)
          (invoke (definitions.foldl (Evaluation.extendMeanings .closed) tE) definition.helper argsE)
  | [], _, _, _, agree, _, _ => ⟨agree, fun _ member => by cases member⟩
  | definition :: rest, names, tL, tE, agree, unique, checked => by
    have restUnique : (definition.name :: names ++ rest.map (·.name)).Nodup := by
      apply List.Nodup.perm unique
      simp only [List.map_cons, List.cons_append]
      exact List.perm_middle
    have notNamed : definition.name ∉ names := by
      intro member
      have := (List.nodup_cons.mp restUnique).1
      exact this (List.mem_append_left _ member)
    have restOther : ∀ later ∈ rest, later.name ≠ definition.name := by
      intro later member same
      have := (List.nodup_cons.mp restUnique).1
      exact this (List.mem_append_right _ (List.mem_map.mpr ⟨later, member, same⟩))
    simp only [checkCustodyFrames] at checked
    by_cases free : definition.custodyFree names.contains = true
    · simp only [free, ↓reduceIte] at checked
      have extended : TablesAgree (definition.name :: names)
          (Evaluation.extendMeanings (custodyObservations holder) tL definition)
          (Evaluation.extendMeanings .closed tE definition) := by
        intro helper named args
        by_cases same : definition.name = helper.name
        · by_cases exact : definition.helper = helper
          · subst exact
            rw [invoke_extend_same, invoke_extend_same]
            exact custodyFree_denote holder agree definition free args.get
          · rw [invoke_extend_mismatch _ _ _ helper same exact,
              invoke_extend_mismatch _ _ _ helper same exact]
            rfl
        · have old : names.contains helper.name = true := by
            simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at named
            rcases named with equal | old
            · exact absurd equal.symm same
            · exact old
          rw [invoke_extend_other _ _ _ helper same, invoke_extend_other _ _ _ helper same]
          exact agree helper old args
      obtain ⟨tables, frames⟩ := custody_frames_sound holder rest (definition.name :: names) _ _
        extended restUnique checked
      refine ⟨by simpa only [custodyFreeNames, free, ↓reduceIte, List.foldl_cons] using tables, ?_⟩
      intro later member unnamed
      simp only [custodyFreeNames, free, ↓reduceIte] at unnamed
      rcases List.mem_cons.mp member with same | member
      · subst same
        have present := custodyFreeNames_mono rest _ _ (List.mem_cons_self (a := later.name) (l := names))
        simp_all
      · exact frames later member unnamed
    · have notFree : definition.custodyFree names.contains = false := by simpa using free
      simp only [notFree, Bool.false_eq_true, ↓reduceIte] at checked
      split at checked
      · cases checked
      · split at checked
        · cases checked
        · rename_i _ admitted
          have frame : definition.body.custodyFrame names.contains [] = true := by simpa using admitted
          have extended : TablesAgree names
              (Evaluation.extendMeanings (custodyObservations holder) tL definition)
              (Evaluation.extendMeanings .closed tE definition) := by
            intro helper named args
            have different : definition.name ≠ helper.name := by
              intro same
              exact notNamed (by simpa [same] using named)
            rw [invoke_extend_other _ _ _ helper different, invoke_extend_other _ _ _ helper different]
            exact agree helper named args
          have restUnique' : (names ++ rest.map (·.name)).Nodup :=
            (List.nodup_cons.mp restUnique).2
          obtain ⟨tables, frames⟩ := custody_frames_sound holder rest names _ _
            extended restUnique' checked
          refine ⟨by simpa only [custodyFreeNames, notFree, Bool.false_eq_true, ↓reduceIte,
            List.foldl_cons] using tables, ?_⟩
          intro later member unnamed
          simp only [custodyFreeNames, notFree, Bool.false_eq_true, ↓reduceIte] at unnamed
          rcases List.mem_cons.mp member with same | member
          · subst same
            intro argsL argsE ledger dataAgree holds
            simp only [List.foldl_cons]
            rw [invoke_foldl_other _ _ rest _ restOther, invoke_foldl_other _ _ rest _ restOther,
              invoke_extend_same, invoke_extend_same]
            exact Region.custodySound agree
              later.body [] frame argsL.get argsE.get ledger dataAgree holds
          · exact frames later member unnamed

end Soundness

end Zkc.Source.Structured
