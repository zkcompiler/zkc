import Tests.CompositeReuseBodies
import Zkc.Obligations.Assembly

/-! Small mathematical contracts for the admitted source. The first readback
subtracts a shift, so the seam has a nonidentity mathematical map. Runtime
routes and mathematical maps are separately checked, including definedness. -/
set_option autoImplicit false
set_option smartUnfolding false
noncomputable section
namespace Tests.CompositeReuseContracts
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open Tests.CompositeReuseBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def gapped (yes gap : F) : ClaimRelation F Unit where
  Holds value _ := value = yes
  No value := value ≠ yes ∧ value ≠ gap
  no_excludes _ _ wrong correct := wrong.1 correct

omit [DecidableEq F] in
theorem add_no (yes gap delta value : F) (wrong : (gapped yes gap).No value) :
    (gapped (yes + delta) (gap + delta)).No (value + delta) := by
  exact ⟨fun same => wrong.1 (add_right_cancel same),
    fun same => wrong.2 (add_right_cancel same)⟩

omit [DecidableEq F] in
theorem add_yes (yes gap delta value : F) (correct : (gapped yes gap).token.Yes value) :
    (gapped (yes + delta) (gap + delta)).token.Yes (value + delta) := by
  obtain ⟨witness, correct⟩ := correct
  exact ⟨(), congrArg (· + delta) correct⟩

omit [DecidableEq F] in
theorem partial_square (delta : F) (value : Option F) (readback : F)
    (defined : value.map (· - delta) = some readback) : value = some (readback + delta) := by
  cases value with
  | none => cases defined
  | some value =>
    simp only [Option.map_some, Option.some.injEq] at defined ⊢
    rw [← defined, sub_add_cancel]

/-- The enabled guard and the actual ignored operand are explicit scope,
independent of Yes, No, and the gap. Scope does not invent a readback. -/
def scope (marker : F) (runtime : Runtime F) : Prop :=
  runtime.ignored = marker ∧ runtime.enabled = true

abbrev shiftComponent (E : Type) (yes gap delta : F) :
    ComponentInterface (I (F := F) (G := G)) E (Runtime F) (Option F) where
  Parameters := F
  Input := F
  InputWitness := Unit
  Output := F
  OutputWitness := Unit
  input := gapped yes gap
  output := gapped yes gap
  body := shift delta
  Scope marker runtime _ := scope marker runtime
  inputView _ runtime _ := runtime.value
  outputView _ _ _ value := value.map (· - delta)

abbrev outerComponent (E : Type) (yes gap first second : F) :
    ComponentInterface (I (F := F) (G := G)) E (Runtime F) (Option F) where
  Parameters := F
  Input := F
  InputWitness := Unit
  Output := F
  OutputWitness := Unit
  input := gapped yes gap
  output := gapped (yes + first + second) (gap + first + second)
  body := outer first second
  Scope marker runtime _ := scope marker runtime
  inputView _ runtime _ := runtime.value
  outputView _ _ _ value := value

abbrev thirdComponent (E : Type) (yes gap first second last : F) :
    ComponentInterface (I (F := F) (G := G)) E (Runtime F) (Option F) where
  Parameters := F
  Input := F
  InputWitness := Unit
  Output := F
  OutputWitness := Unit
  input := gapped yes gap
  output := gapped (yes + first + second + last) (gap + first + second + last)
  body := third first second last
  Scope marker runtime _ := scope marker runtime
  inputView _ runtime _ := runtime.value
  outputView _ _ _ value := value

abbrev firstConnection (E : Type) (yes gap first second : F) :
    Connection (shiftComponent (G := G) E yes gap first)
      (shiftComponent E (yes + first) (gap + first) second) where
  parameters := id
  route := route
  map value := value + first
  square := fun _ _ _ value output defined => partial_square first value output defined

/-- The actual third source caller routes the composite result into Shift's
second operand, retaining the original marker and enabled capture. -/
abbrev nextConnection (E : Type) (yes gap first second last : F) :
    Connection (outerComponent (G := G) E yes gap first second)
      (shiftComponent E (yes + first + second) (gap + first + second) last) where
  parameters := id
  route := route
  map := id
  square := fun _ _ _ _ _ defined => defined

omit [CommRing F] [DecidableEq F] in
/-- Preserving the enabled capture and original operand needs no No premise. -/
theorem route_scope (marker : F) (runtime : Runtime F) (value : Option F)
    (preserved : scope marker runtime) : scope marker (route runtime value) := preserved

variable {E P : Type} {Raw : E → Type}
  (absorb : Interface (I (F := F) (G := G)) E P Raw) (escape : EscapeJudgment E Raw)

/-- This frame is independent of any claim predicate and readback definedness.
In particular it covers Yes, No, gap, and absent-value prefixes. -/
def shift_frame (delta marker : F) (runtime : Runtime F) (history : List E)
    (preserved : scope marker runtime) :
    Derivation absorb escape (fun _ value => scope marker (route runtime value)) history
      (shift delta runtime) := by
  rw [shift_binding, preserved.2]
  exact .done preserved

def outer_frame (first second marker : F) (runtime : Runtime F) (history : List E)
    (preserved : scope marker runtime) :
    Derivation absorb escape (fun _ value => scope marker (route runtime value)) history
      (outer first second runtime) := by
  apply Derivation.transport (outer_binding first second runtime)
  exact (shift_frame absorb escape first marker runtime history preserved).bind _
    fun reached value invariant =>
      (shift_frame absorb escape second marker (route runtime value) reached invariant).consequence
        (fun _ _ _ => preserved)

def third_frame (first second last marker : F) (runtime : Runtime F) (history : List E)
    (preserved : scope marker runtime) :
    Derivation absorb escape (fun _ value => scope marker (route runtime value)) history
      (third first second last runtime) := by
  apply Derivation.transport (third_binding first second last runtime)
  exact (outer_frame absorb escape first second marker runtime history preserved).bind _
    fun reached value invariant =>
      (shift_frame absorb escape last marker (route runtime value) reached invariant).consequence
        (fun _ _ _ => preserved)

def shift_sound (yes gap delta : F) :
    SoundnessContract (shiftComponent (G := G) E yes gap delta) absorb escape := by
  intro marker runtime history _ wrong
  change Derivation _ _ _ _ (shift (G := G) delta runtime)
  rw [shift_binding]
  split
  · apply Derivation.done
    change ReadbackHolds (gapped yes gap).No
      ((runtime.value.map (· + delta)).map (· - delta))
    change ReadbackHolds (gapped yes gap).No runtime.value at wrong
    simpa only [Option.map_map, Function.comp_def, add_sub_cancel_right, Option.map_id'] using wrong
  · exact .halt .reject

/-- The outer source body is assembled from existing Connection.bind. Its
security proof is opaque to every subsequent client. -/
opaque outer_sound (yes gap first second : F) :
    SoundnessContract (outerComponent (G := G) E yes gap first second) absorb escape := by
  intro marker runtime history preserved wrong
  apply Derivation.transport (outer_binding first second runtime)
  exact (firstConnection E yes gap first second).bind
    (add_no yes gap first) (shift_sound absorb escape yes gap first)
    (shift_sound absorb escape (yes + first) (gap + first) second)
    marker runtime history preserved wrong
    (fun _ value _ => route_scope marker runtime value preserved) _
    (by
      intro _ reached result rejected
      obtain ⟨value, defined, rejected⟩ := rejected
      exact ⟨value + second, partial_square second result value defined,
        add_no (yes + first) (gap + first) second value rejected⟩)

/-- Only the opaque exported composite contract is used at the first call.
The caller equation is checked against the admitted Third source body. -/
def third_sound (yes gap first second last : F) :
    SoundnessContract (thirdComponent (G := G) E yes gap first second last) absorb escape := by
  intro marker runtime history preserved wrong
  apply Derivation.transport (third_binding first second last runtime)
  exact (nextConnection E yes gap first second last).bind
    (ClaimRelation.SoundLink.id _) (outer_sound absorb escape yes gap first second)
    (shift_sound absorb escape (yes + first + second) (gap + first + second) last)
    marker runtime history preserved wrong
    (fun _ value _ => route_scope marker runtime value preserved) _
    (by
      intro _ reached result rejected
      obtain ⟨value, defined, rejected⟩ := rejected
      exact ⟨value + last, partial_square last result value defined,
        add_no (yes + first + second) (gap + first + second) last value rejected⟩)

/-- Honest contracts use the same component, readbacks, scope and source
equations as soundness. Stops have an impossible honest postcondition. -/
def HonestContract (component : ComponentInterface (I (F := F) (G := G)) E (Runtime F) (Option F)) : Prop :=
  ∀ marker runtime history, component.Scope marker runtime history →
    component.InputYes marker runtime history →
    ∀ (S O : Type) (handler : PIR.Handler (I (F := F) (G := G)) S O) (state : S),
      ∃ value, (component.body runtime).run handler state = ⟨.returned value, state, []⟩ ∧
        component.OutputYes marker runtime history value

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A local honest assembly client of the existing run-bind equation and the
same Connection square used by soundness. State and events are preserved. -/
theorem honest_bind
    (head tail composite : ComponentInterface (I (F := F) (G := G)) E (Runtime F) (Option F))
    (connection : Connection head tail)
    (parameters : composite.Parameters → head.Parameters)
    (binding : ∀ runtime, composite.body runtime =
      (head.body runtime).bind fun value => tail.body (connection.route runtime value))
    (enter : ∀ marker runtime history, composite.Scope marker runtime history →
      composite.InputYes marker runtime history →
      head.Scope (parameters marker) runtime history ∧ head.InputYes (parameters marker) runtime history)
    (law : head.output.HonestLink tail.input connection.map)
    (nextScope : ∀ marker runtime history value, composite.Scope marker runtime history →
      tail.Scope (connection.parameters (parameters marker)) (connection.route runtime value) history)
    (exit : ∀ marker runtime history value result,
      tail.OutputYes (connection.parameters (parameters marker)) (connection.route runtime value) history result →
      composite.OutputYes marker runtime history result)
    (headHonest : HonestContract head) (tailHonest : HonestContract tail) :
    HonestContract composite := by
  intro marker runtime history preserved correct S O handler state
  obtain ⟨headScope, headYes⟩ := enter marker runtime history preserved correct
  obtain ⟨value, headRun, headResult⟩ := headHonest (parameters marker) runtime history headScope headYes S O handler state
  obtain ⟨result, tailRun, tailResult⟩ := tailHonest (connection.parameters (parameters marker))
    (connection.route runtime value) history (nextScope marker runtime history value preserved)
    (connection.input_yes law headResult) S O handler state
  refine ⟨result, ?_, exit marker runtime history value result tailResult⟩
  rw [binding, PIR.run_bind, headRun]
  simp only [PIR.Execution.follow, tailRun, List.nil_append]

theorem shift_honest (yes gap delta : F) :
    HonestContract (shiftComponent (G := G) E yes gap delta) := by
  intro marker runtime history preserved correct S O handler state
  refine ⟨runtime.value.map (· + delta), ?_, ?_⟩
  · change (shift (G := G) delta runtime).run handler state = _
    rw [shift_binding, preserved.2]
    rfl
  change ReadbackHolds (gapped yes gap).token.Yes
    ((runtime.value.map (· + delta)).map (· - delta))
  change ReadbackHolds (gapped yes gap).token.Yes runtime.value at correct
  simpa only [Option.map_map, Function.comp_def, add_sub_cancel_right, Option.map_id'] using correct

opaque outer_honest (yes gap first second : F) :
    HonestContract (outerComponent (G := G) E yes gap first second) := by
  apply honest_bind (shiftComponent E yes gap first)
    (shiftComponent E (yes + first) (gap + first) second) (outerComponent E yes gap first second)
    (firstConnection E yes gap first second) id (outer_binding first second)
    (fun _ _ _ preserved correct => ⟨preserved, correct⟩) (add_yes yes gap first)
    (fun _ _ _ _ preserved => preserved)
  · intro marker runtime history value result correct
    obtain ⟨output, defined, correct⟩ := correct
    exact ⟨output + second, partial_square second result output defined,
      add_yes (yes + first) (gap + first) second output correct⟩
  · exact shift_honest yes gap first
  · exact shift_honest (yes + first) (gap + first) second

theorem third_honest (yes gap first second last : F) :
    HonestContract (thirdComponent (G := G) E yes gap first second last) := by
  apply honest_bind (outerComponent E yes gap first second)
    (shiftComponent E (yes + first + second) (gap + first + second) last) (thirdComponent E yes gap first second last)
    (nextConnection E yes gap first second last) id (third_binding first second last)
    (fun _ _ _ preserved correct => ⟨preserved, correct⟩) (ClaimRelation.HonestLink.id _)
    (fun _ _ _ _ preserved => preserved)
  · intro marker runtime history value result correct
    obtain ⟨output, defined, correct⟩ := correct
    exact ⟨output + last, partial_square last result output defined,
      add_yes (yes + first + second) (gap + first + second) last output correct⟩
  · exact outer_honest yes gap first second
  · exact shift_honest (yes + first + second) (gap + first + second) last

end Tests.CompositeReuseContracts
