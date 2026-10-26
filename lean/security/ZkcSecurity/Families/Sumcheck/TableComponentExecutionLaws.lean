module

public import ZkcSecurity.Families.Sumcheck.TableComponentExecution
public import ZkcSecurity.Families.Sumcheck.TableComponentNominalCost
public import ZkcSecurity.FiatShamir.Budget

@[expose] public section

/-! The installed reference and its existing residual consumer apply to the
nominal table loop. The original raw table and all reached histories
survive the connection. No second polynomial reference or reduction engine is
introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations ZkcSecurity.FiatShamir
open TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev ReferenceState (F G : Type) [Field F] (n : Nat) :=
  PrefixState F (Domain.History (uniformCarriers F G)) n

def project {n : Nat} (state : ReferenceState F G n) : State F G :=
  ⟨state.point, state.scalar, state.frame⟩

def frameUpdate (field : String) : Nominal.FrameUpdate F (Domain.History (uniformCarriers F G)) field :=
  fun sites state message challenge =>
    finalHistory field (sites.low state.point.length) (sites.high state.point.length)
      (sites.query state.point.length) (sites.delivery state.point.length) state.frame message.1 message.2 challenge

noncomputable abbrev component (field : String) :=
  Nominal.programWithFrame (F := F) field (frameUpdate (F := F) (G := G) field)

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem run_remaining (field : String) (sites : Nominal.Schedule field)
    {n : Nat} (count : Nat) (state : ReferenceState F G (n + count)) :
    run field sites (List.range' state.point.length count) (project state) =
      ((component (G := G) field).remaining count sites state).bind
        (fun final => .done (project final)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.range'_succ, run, component, Program.remaining, Nominal.programWithFrame,
      Nominal.program, PIR.Process.bind, project, Message.endpoints, Zkc.Protocols.Sumcheck.Multilinear.boundary]
    congr 1
    funext low
    congr 1
    funext high
    by_cases boundary : state.scalar = low + high
    · simp only [boundary, ite_true, PIR.Process.bind]
      congr 1
      funext challenge
      congr 1
      funext delivered
      simpa only [project, Nominal.programWithFrame, Nominal.program, PrefixState.advance,
        List.length_append, List.length_singleton, frameUpdate, advance, Message.endpoints, Zkc.Protocols.Sumcheck.Multilinear.evaluate]
        using ih ((component (G := G) field).advance sites state (low, high) challenge)
    · simp [boundary, eq_comm, PIR.Process.bind]

/-- The nominal table loop inherits the existing reference residual theorem,
including the immutable original table needed by the actual terminal. -/
noncomputable def run_residual
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (field : String) (sites : Nominal.Schedule field)
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    {n : Nat} (count : Nat) (state : ReferenceState F G (n + count))
    (history : Domain.History (uniformCarriers F G)) (wrong : state.scalar ≠ state.entries.sum) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => ∃ final : ReferenceState F G n, final.original = state.original ∧
        final.scalar ≠ final.entries.sum ∧ result = project final)
      history (run field sites (List.range' state.point.length count) (project state)) := by
  rw [run_remaining]
  let layout := Nominal.layoutWithFrame field (frameUpdate (F := F) (G := G) field)
  have residual := Consumers.residual layout.representation Message.endpoints_laws TableReference.laws
    (Nominal.queriesWithFrame (G := G) field (frameUpdate (F := F) (G := G) field)) sampling count sites state history
      ((layout.no_iff state).mpr wrong)
  let interaction : PIR.Interaction (Nominal.signature F field) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  have original := (component (G := G) field).returns interaction
    (fun {k} (s : ReferenceState F G k) => s.original = state.original)
    (fun _ _ same _ _ => same) count sites state () rfl
  apply (residual.frameReturns interaction (fun final => final.original = state.original) () original).bind
  intro reached final post
  exact .done ⟨final, post.2, (layout.no_iff final).mp post.1, rfl⟩


omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem run_cost (field : String) (sites : Nominal.Schedule field)
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (price : ENNReal) (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (indices : List Nat) (state : State F G) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) field) charge
      (run field sites indices state) history (indices.length • price) := by
  induction indices generalizing state history with
  | nil => trivial
  | cons index rest ih =>
    simp only [run, Typed.ChargedCostBound, Nominal.interface]
    intro payload low decoded payload' high decoded'
    split
    · refine ⟨rest.length • price, ?_, ?_⟩
      · simpa only [List.length_cons, succ_nsmul, add_comm] using
          add_le_add_right (priced _ (sites.query index)) (rest.length • price)
      · intro challenge
        exact ih _ _
    · trivial

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem run_returns_length (field : String) (sites : Nominal.Schedule field)
    (interaction : PIR.Interaction (Nominal.signature F field))
    (indices : List Nat) (state : State F G) (phase : interaction.Phase) :
    PIR.Boundary.Returns interaction
      (fun final _ => final.point.length = state.point.length + indices.length)
      (run field sites indices state) phase := by
  induction indices generalizing state phase with
  | nil => simp [run, PIR.Boundary.Returns]
  | cons index rest ih =>
    simp only [run, PIR.Boundary.Returns]
    intro low high
    split
    · intro challenge delivered
      apply (PIR.Boundary.returns_mono interaction
        (run field sites rest (advance field sites index state low high challenge)) _ _ _
        (ih (advance field sites index state low high challenge) _) )
      intro final finalPhase next
      simpa only [advance, List.length_append, List.length_singleton, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.length_nil, Nat.zero_add] using next
    · trivial

/-- A return is incompatible with terminal acceptance if either its original
shape or its represented scalar is wrong. The same contract retains the
all-return length invariant, so consumers may use a source-normalized terminal
expression. The premise permits every raw shape. -/
noncomputable def run_rejecting
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (field : String) (sites : Nominal.Schedule field)
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    (raw : List F) (claim : F) (count : Nat)
    (initial history : Domain.History (uniformCarriers F G))
    (wrong : raw.length = 2 ^ count → claim ≠ raw.sum) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ final => (raw.length ≠ 2 ^ final.point.length ∨
        final.scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw final.point).sum) ∧
        final.point.length = count)
      history (run field sites (List.range count) ⟨[], claim, initial⟩) := by
  have residual : Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ final => raw.length ≠ 2 ^ final.point.length ∨
        final.scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw final.point).sum)
      history (run field sites (List.range count) ⟨[], claim, initial⟩) := by
    by_cases shape : raw.length = 2 ^ count
    · let state : ReferenceState F G (0 + count) := ⟨raw, [], claim, initial, by simpa using shape⟩
      have head := run_residual field sites charge sampling (n := 0) count state history (by simpa only [state, PrefixState.entries, Zkc.Polynomial.Multilinear.restrictPrefixValues_nil] using wrong shape)
      have sameRange : List.range' 0 count = List.range count := List.range_eq_range'.symm
      simpa only [state, project, List.length_nil, sameRange] using
        head.consequence (Weaker := fun _ final => raw.length ≠ 2 ^ final.point.length ∨
          final.scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw final.point).sum) (fun reached final post => by
          obtain ⟨last, originalEq, different, rfl⟩ := post
          exact Or.inr (by simpa only [project, PrefixState.entries, originalEq] using different))
    · let interaction : PIR.Interaction (Nominal.signature F field) :=
        ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
      have head := (ZkcSecurity.Obligations.unrestricted (absorb := Nominal.interface (G := G) field)
        (charge := charge) (run field sites (List.range count) ⟨[], claim, initial⟩) history).frameReturns
          interaction (fun final => final.point.length = count) () (by
            simpa only [List.length_nil, Nat.zero_add, List.length_range] using
              run_returns_length field sites interaction (List.range count) ⟨[], claim, initial⟩ ())
      exact head.consequence fun reached final post => Or.inl (by simpa only [post.2] using shape)
  let interaction : PIR.Interaction (Nominal.signature F field) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  exact residual.frameReturns interaction (fun final => final.point.length = count) () (by
    simpa only [List.length_nil, Nat.zero_add, List.length_range] using
      run_returns_length field sites interaction (List.range count) ⟨[], claim, initial⟩ ())

end ZkcSecurity.Families.Sumcheck.TableComponent.Execution
