module

public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.Completion
public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Residual

@[expose] public section


namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal

open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open Zkc.Polynomial.Multilinear
open _root_.Interaction.Oracle _root_.Sumcheck.Interaction
open ZkcSecurity.VCVio.Execution
open scoped ENNReal

variable {F S E K : Type}
variable [Field F] [DecidableEq F]

set_option backward.isDefEq.respectTransparency false in
theorem endpointGame_execute [SampleableType F] (n count start : Nat)
    (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (stmt : _root_.Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : EndpointProver (F := F) unifSpec count)
    (terminal : List F → F → Prop) :
    endpointGame count stmt.target (List.ofFn stmt.challenges) prover terminal =
      (do let output ← Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
            booleanDomain count start finish A original stmt impl prover
          return output.map (fun out => terminal (List.ofFn out.stmt.challenges)
            out.stmt.target) = some True) := by
  induction count generalizing start A with
  | zero =>
    have h : start = n := by omega
    subst start
    simp [endpointGame, Native.Core.execute_zero]
  | succ count ih =>
    rw [execute_round]
    simp only [endpointGame]
    rw [bind_assoc]
    apply bind_congr
    rintro ⟨pair, respond⟩
    split
    · simp only [bind_assoc]
      apply bind_congr; intro r
      apply bind_congr; intro next
      have step := ih (start+1) (by omega)
        (Access.extend A (Native.Core.messageInterface F (Message F) evaluate))
        (original.sumWeaken (Native.Core.messageInterface F (Message F) evaluate).spec)
        ⟨evaluate pair r, Fin.snoc stmt.challenges r⟩
        (Access.extendImpl A (Native.Core.messageInterface F (Message F) evaluate) impl pair) next
      simpa only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
        List.concat_eq_append] using step
    · simp only [bind_assoc, pure_bind, Option.map_none, reduceCtorEq]

def tableTerminal {n : Nat} (table : Table F n) (point : List F) (claim : F) : Prop :=
  ∃ coordinates : Fin n → F, List.ofFn coordinates = point ∧ extension n table coordinates = claim

omit [DecidableEq F] in
theorem tableTerminal_ofFn {n : Nat} (table : Table F n) (point : Fin n → F) (claim : F) :
    tableTerminal table (List.ofFn point) claim ↔ extension n table point = claim := by
  simp [tableTerminal, List.ofFn_inj]

theorem endpointGame_experiment [SampleableType F] {n : Nat}
    (table : Table F n) (claim : F) (prover : EndpointProver (F := F) unifSpec n) :
    endpointGame n claim [] prover (tableTerminal table) = experiment table claim prover := by
  rw [show ([] : List F) = List.ofFn (Fin.elim0 : Fin 0 → F) from rfl]
  rw [endpointGame_execute n n 0 (Nat.zero_add n)
    (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1))
    ⟨claim, Fin.elim0⟩
    ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
      (fun _ => oracleStatement table))]
  unfold experiment
  apply bind_congr_of_forall_mem_support
  intro output supported
  cases output with
  | none => rfl
  | some output =>
    have retained := execute_preserves_original unifSpec n ($ᵗ F) booleanDomain
      n 0 (Nat.zero_add n) (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
      (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1))
      ⟨claim, Fin.elim0⟩
      ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
        (fun _ => oracleStatement table)) prover output supported
    apply congrArg pure
    apply propext
    simp only [Option.map_some, Option.some.injEq, eq_iff_iff, iff_true]
    rw [tableTerminal_ofFn]
    change _ ↔ output.oracles ⟨(), output.stmt.challenges⟩ = output.stmt.target
    rw [retained]
    change _ ↔ MvPolynomial.eval output.stmt.challenges (statement table) = _
    rw [statement_evaluate]
    rfl

/-- Chronological challenges are in the mathematical table's MSB-first
    coordinate order. This relation never identifies P's and V's points. -/
def MSBChronology {n : Nat} (point : List F) (coordinates : Fin n → F) : Prop :=
  List.ofFn coordinates = point

omit [Field F] [DecidableEq F] in
theorem msb_chronology_snoc {n : Nat} (point : List F) (coordinates : Fin n → F)
    (r : F) (ordered : MSBChronology point coordinates) :
    MSBChronology (point ++ [r]) (Fin.snoc coordinates r) := by
  simpa only [MSBChronology, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append] using
    congrArg (fun xs => xs ++ [r]) ordered

omit [Field F] [DecidableEq F] in
theorem msb_index_head (n : Nat) (bits : Fin (n+1) → Bool) :
    (index (n+1) bits).val = (if bits 0 then 2^n else 0) +
      (index n (bits ∘ Fin.succ)).val := rfl

omit [DecidableEq F] in
theorem msb_extension_head (n : Nat) (table : Table F (n+1)) (point : Fin (n+1) → F) :
    extension (n+1) table point =
      (1-point 0) * extension n (half table false) (point ∘ Fin.succ) +
      point 0 * extension n (half table true) (point ∘ Fin.succ) := rfl

omit [Field F] [DecidableEq F] in
theorem msb_vector_entry {n : Nat} (values : List F) (table : Table F n)
    (decoded : ofList? n values = some table) (bits : Fin n → Bool) :
    values[(index n bits).val]? = some (table bits) := by
  simpa [vertex_index] using ofList?_entry values table decoded (index n bits)

def rawTerminal (n : Nat) (values : List F) (point : List F) (claim : F) : Prop :=
  ∃ coordinates : Fin n → F, MSBChronology point coordinates ∧ check values coordinates claim = true

theorem rawTerminal_eq_table {n : Nat} (values : List F) (table : Table F n)
    (decoded : ofList? n values = some table) : rawTerminal n values = tableTerminal table := by
  funext point claim
  apply propext
  simp [rawTerminal, MSBChronology, tableTerminal, check_eq_true_iff, decoded]

/-- The public-vector observation is the owner's actual ArkLib observation law.
    Native.Core.execute here belongs to ArkLib, not the zkc native runtime. -/
theorem endpoint_publicTable_observation [SampleableType F] {n : Nat}
    (values : List F) (table : Table F n) (decoded : ofList? n values = some table)
    (claim : F) (prover : EndpointProver (F := F) unifSpec n) :
    endpointGame n claim [] prover (rawTerminal n values) =
      (do let output ← Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
            booleanDomain n 0 (Nat.zero_add n)
            (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
            (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1))
            ⟨claim, Fin.elim0⟩
            ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
              (fun _ => oracleStatement table)) prover
          return output.map (fun out => check values out.stmt.challenges out.stmt.target) = some true) := by
  rw [rawTerminal_eq_table values table decoded, endpointGame_experiment]
  exact publicTable_observation unifSpec table values decoded ($ᵗ F) n 0 (Nat.zero_add n)
    _ _ _ _ prover (fun point => statement_evaluate table point)

/-- This bound is for the joint phase model. Applying it to actual imported
    source requires the separately owned source equation and handler laws. -/
theorem phase_soundness [Fintype F] [SampleableType F] {n : Nat}
    (table : Table F n) (claim : F) (strategy : Strategy F S E n) (s : S)
    (falseClaim : claim ≠ booleanSum table) :
    mass (phaseGame n claim [] strategy s (tableTerminal table)) ≤
      (n : ENNReal) / Fintype.card F := by
  have dominated := domination n claim [] strategy s (tableTerminal table)
  rw [endpointGame_experiment] at dominated
  exact dominated.trans (soundness table claim (complete n claim strategy s) falseClaim)

theorem phase_publicTable_soundness [Fintype F] [SampleableType F] {n : Nat}
    (values : List F) (table : Table F n) (decoded : ofList? n values = some table)
    (claim : F) (strategy : Strategy F S E n) (s : S) (falseClaim : claim ≠ values.sum) :
    mass (phaseGame n claim [] strategy s (rawTerminal n values)) ≤
      (n : ENNReal) / Fintype.card F := by
  rw [rawTerminal_eq_table values table decoded]
  exact phase_soundness table claim strategy s
    (by rwa [booleanSum_ofList? values table decoded])

theorem phase_residual_soundness [Fintype F] [SampleableType F] {remaining count : Nat}
    (table : Table F (remaining + count)) (claim : F)
    (strategy : Strategy F S E count) (s : S) (falseClaim : claim ≠ booleanSum table) :
    mass (phaseGame count claim [] strategy s (tableTerminal (sumRemaining remaining count table))) ≤
      (count : ENNReal) / Fintype.card F := by
  have dominated := domination count claim [] strategy s
    (tableTerminal (sumRemaining remaining count table))
  rw [endpointGame_experiment, ← reductionExperiment_eq] at dominated
  exact dominated.trans (residual_soundness table claim (complete count claim strategy s) falseClaim)

/-- Malformed raw tables reject for every execution distribution, including stops.
No false-claim or freshness premise is needed for this mathematical observation. -/
theorem malformed_raw_zero (n : Nat) (values : List F)
    (wrong : values.length ≠ 2 ^ n)
    (executions : ProbComp (PIR.Execution S E (List F × F))) :
    mass (do let e ← executions; pure (accepts (rawTerminal n values) e)) = 0 := by
  apply OracleComp.prEvent_eq_zero_of_forall_mem_support
  intro e _
  cases e with | mk out state events =>
    cases out with
    | stopped why => simp [accepts]
    | returned pc =>
      rintro ⟨coordinates, _, checked⟩
      rw [check_wrong_shape values coordinates pc.2 wrong] at checked
      contradiction


/-- Residual truth refers to the original table at precisely the challenged
prefix, rather than full evaluation of a padded point. -/
def residualTerminal (remaining count : Nat) (table : Table F (remaining + count))
    (point : List F) (claim : F) : Prop :=
  ∃ coordinates : Fin count → F, MSBChronology point coordinates ∧
    ResidualClaim count table coordinates claim

omit [DecidableEq F] in
theorem residualTerminal_eq_marginal {remaining count : Nat}
    (table : Table F (remaining + count)) :
    residualTerminal remaining count table = tableTerminal (sumRemaining remaining count table) := by
  funext point claim
  simp only [residualTerminal, tableTerminal, MSBChronology, extension_sumRemaining,
    ResidualClaim]

/-- Original-table residual formulation, including zero challenged rounds. -/
theorem residual_phase_soundness [Fintype F] [SampleableType F] {remaining count : Nat}
    (table : Table F (remaining + count)) (claim : F)
    (strategy : Strategy F S E count) (s : S) (falseClaim : claim ≠ booleanSum table) :
    mass (phaseGame count claim [] strategy s (residualTerminal remaining count table)) ≤
      (count : ENNReal) / Fintype.card F := by
  rw [residualTerminal_eq_marginal]
  exact phase_residual_soundness table claim strategy s falseClaim

/-- Arbitrary zero-round trusted terminal work cannot accept a false singleton
claim. In particular stopping at this leaf has no exceptional case. -/
theorem zero_round_false_mass [Fintype F] [SampleableType F]
    (table : Table F 0) (claim : F) (terminal : Strategy F S E 0) (s : S)
    (falseClaim : claim ≠ booleanSum table) :
    mass (phaseGame 0 claim [] terminal s (tableTerminal table)) = 0 := by
  have bound := phase_soundness table claim terminal s falseClaim
  simpa only [Nat.cast_zero, ENNReal.zero_div, nonpos_iff_eq_zero] using bound

end ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal
