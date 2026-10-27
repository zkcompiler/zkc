import Tests.ContractComposition
import Zkc.Obligations.Component
import Mathlib.Algebra.Ring.Int.Defs

/-! Contracts attached to an admitted source call. The source fixture uses its
second operand and a swapped role map. The outer composition exercises the
library API; production root generation is tested separately in security.
-/

set_option autoImplicit false
noncomputable section
namespace Tests.ComponentContracts
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open Tests.ContractComposition

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev I := observedInterface F G

def source (runtime : Nat × Nat) : PIR.Process (I (F := F) (G := G)) Nat :=
  (identityCall.denote (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
    (inputs runtime.1 runtime.2).get).bind fun values =>
      match values.get .here with
      | some value => .done value
      | none => .halt .reject

theorem source_binding (runtime : Nat × Nat) :
    source (F := F) (G := G) runtime = .done runtime.2 := by
  unfold source
  rw [generated_substitution]
  rfl

def gapped (base : Nat) : ClaimRelation Nat Unit where
  Holds value _ := value = base
  No value := base + 2 ≤ value
  no_excludes := by intros; omega

def component (E : Type) : ComponentInterface (I (F := F) (G := G)) E (Nat × Nat) Nat where
  Parameters := Unit
  Input := Nat
  InputWitness := Unit
  Output := Nat
  OutputWitness := Unit
  input := gapped 0
  output := gapped 0
  body := source
  Scope _ _ _ := True
  inputView _ runtime _ := some runtime.2
  outputView _ _ _ value := some value

def increment (E : Type) (base : Nat) : ComponentInterface (I (F := F) (G := G)) E Nat Nat where
  Parameters := Unit
  Input := Nat
  InputWitness := Unit
  Output := Nat
  OutputWitness := Unit
  input := gapped base
  output := gapped (base + 1)
  body value := .done (value + 1)
  Scope _ _ _ := True
  inputView _ value _ := some value
  outputView _ _ _ value := some value

variable {E P : Type} {Raw : E → Type}
  (absorb : Interface (I (F := F) (G := G)) E P Raw) (escape : EscapeJudgment E Raw)

def source_contract : SoundnessContract (component (F := F) (G := G) E) absorb escape := by
  intro _ runtime history _ no
  change Derivation _ _ _ _ (source (F := F) (G := G) runtime)
  rw [source_binding]
  exact .done no

def increment_contract (base : Nat) :
    SoundnessContract (increment (F := F) (G := G) E base) absorb escape := by
  intro _ runtime _ _ no
  apply Derivation.done
  obtain ⟨value, defined, wrong⟩ := no
  cases defined
  exact ⟨runtime + 1, rfl, by change base + 1 + 2 ≤ runtime + 1; change base + 2 ≤ runtime at wrong; omega⟩

def firstConnection : Connection (component (F := F) (G := G) E) (increment E 0) where
  parameters := id
  route _ value := value
  map := id
  square := by
    intro _ _ _ _ _ defined
    exact defined

def composed : ComponentInterface (I (F := F) (G := G)) E (Nat × Nat) Nat where
  Parameters := Unit
  Input := Nat
  InputWitness := Unit
  Output := Nat
  OutputWitness := Unit
  input := gapped 0
  output := gapped 1
  body runtime := (source runtime).bind fun value => .done (value + 1)
  Scope _ _ _ := True
  inputView _ runtime _ := some runtime.2
  outputView _ _ _ value := some value

def composed_contract : SoundnessContract (composed (F := F) (G := G) (E := E)) absorb escape := by
  intro parameters runtime history scope no
  exact firstConnection.bind (ClaimRelation.SoundLink.id (gapped 0))
    (source_contract absorb escape) (increment_contract absorb escape 0)
    parameters runtime history scope no (fun _ _ _ => trivial) _ (fun _ _ _ wrong => wrong)

def nextConnection : Connection (composed (F := F) (G := G) (E := E)) (increment E 1) where
  parameters := id
  route _ value := value
  map := id
  square := by
    intro _ _ _ _ _ defined
    exact defined

/-- A composite is reused through its contract constant, without unfolding its
proof or requiring a new process constructor. -/
def third_contract (runtime : Nat × Nat) (history : List E) (no : 2 ≤ runtime.2) :
    Derivation absorb escape (fun _ value => 4 ≤ value) history
      (((composed (F := F) (G := G) (E := E)).body runtime).bind fun value => .done (value + 1)) :=
  nextConnection.bind (ClaimRelation.SoundLink.id (gapped 1))
    (composed_contract absorb escape) (increment_contract absorb escape 1)
    () runtime history trivial ⟨runtime.2, rfl, no⟩ (fun _ _ _ => trivial) _
    (by intro _ _ _ wrong; exact ReadbackHolds.some.mp wrong)

/-- Independent scope preservation holds for Yes, gap and No inputs alike. -/
theorem source_preserves (interaction : PIR.Interaction (I (F := F) (G := G)))
    (phase : interaction.Phase) (runtime : Nat × Nat) :
    PIR.Boundary.Returns interaction (fun value _ => value = runtime.2) (source runtime) phase := by
  rw [source_binding]
  rfl

example (interaction : PIR.Interaction (I (F := F) (G := G))) (phase : interaction.Phase) :
    ∀ value ∈ ([0, 1, 2] : List Nat),
      PIR.Boundary.Returns interaction (fun result _ => result = value) (source (99, value)) phase :=
  fun value _ => source_preserves interaction phase (99, value)

/-- The honest result uses the very same source equation as soundness. -/
theorem source_honest {H O : Type} (handler : PIR.Handler (I (F := F) (G := G)) H O)
    (state : H) (runtime : Nat × Nat) :
    (source runtime).run handler state = ⟨.returned runtime.2, state, []⟩ := by
  rw [source_binding]
  rfl

theorem wrong_operand_refused : source (F := Int) (G := Int) (4, 3) ≠ .done 4 := by
  rw [source_binding]
  intro same
  cases same

theorem missing_readback_refused : ¬ ReadbackHolds (gapped 0).No none := ReadbackHolds.none _

/-- A different runtime representation: the mathematical statement is read
partially from the first vector coordinate. An empty vector actually stops. -/
def wire : ComponentInterface (I (F := F) (G := G)) E (List Nat) Nat where
  Parameters := Unit
  Input := Nat
  InputWitness := Unit
  Output := Nat
  OutputWitness := Unit
  input := gapped 1
  output := gapped 1
  body values := match values with
    | [] => .halt .reject
    | value :: _ => .done value
  Scope _ _ _ := True
  inputView _ values _ := values.head?
  outputView _ _ _ value := some value

def wire_contract : SoundnessContract (wire (F := F) (G := G) (E := E)) absorb escape := by
  intro _ values _ _ no
  cases values with
  | nil => exact .halt .reject
  | cons value rest => exact .done no

/-- Runtime routing constructs a vector; the mathematical map adds one. The
square checks their agreement, rather than identifying the two functions. -/
def wireConnection : Connection (component (F := F) (G := G) E) (wire (E := E)) where
  parameters := id
  route _ value := [value + 1]
  map := fun (value : Nat) => value + 1
  square := by
    intro _ _ _ _ _ defined
    cases defined
    rfl

def changed_representation (runtime : Nat × Nat) (history : List E) (wrong : 2 ≤ runtime.2) :
    Derivation absorb escape (fun _ value => 3 ≤ value) history
      ((source runtime).bind fun value => (wire (F := F) (G := G) (E := E)).body [value + 1]) :=
  wireConnection.bind
    (by change ∀ value : Nat, 2 ≤ value → 3 ≤ value + 1; omega)
    (source_contract absorb escape) (wire_contract absorb escape)
    () runtime history trivial ⟨runtime.2, rfl, wrong⟩ (fun _ _ _ => trivial) _
    (by intro _ _ _ no; exact ReadbackHolds.some.mp no)

theorem wrong_square_refused : ¬ ∀ value : Nat,
    ([value + 2].head? : Option Nat) = some (value + 1) := by
  intro square
  have impossible := square 0
  cases impossible

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mutated_frame_refused (interaction : PIR.Interaction (I (F := F) (G := G)))
    (phase : interaction.Phase) :
    ¬ PIR.Boundary.Returns interaction (fun value _ => value = 3)
      (.done 4 : PIR.Process (I (F := F) (G := G)) Nat) phase := by
  intro impossible
  cases impossible

/-- These relations have the same Yes set but different gaps. -/
def widerGap : ClaimRelation Nat Unit where
  Holds value _ := value = 0
  No value := 3 ≤ value
  no_excludes := by intros; omega

theorem same_yes : ∀ value, (gapped 0).token.Yes value ↔ widerGap.token.Yes value :=
  fun _ => Iff.rfl

theorem no_transport_refused : ¬ (gapped 0).SoundLink widerGap id := by
  intro law
  have bad := law 2 (by change 0 + 2 ≤ 2; decide)
  change 3 ≤ 2 at bad
  omega

theorem no_hidden_scope : ¬ ((False → 2 = 3) → 2 = 3) := by decide

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem rejecting_is_not_complete {H O : Type} (handler : PIR.Handler (I (F := F) (G := G)) H O)
    (state : H) (value : Nat) :
    ((PIR.Process.halt .reject : PIR.Process (I (F := F) (G := G)) Nat).run handler state).outcome ≠
      .returned value := by intro impossible; cases impossible

#print axioms source_contract
#print axioms composed_contract
#print axioms third_contract
#print axioms source_honest

end Tests.ComponentContracts
