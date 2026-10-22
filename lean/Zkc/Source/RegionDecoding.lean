module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Source.Structure
public import Zkc.Source.ContextDecoding

@[expose] public section

/-! Strict formation for the canonical typed region carrier.

Raw regions retain ordered operation results, closed callback signatures and
bind intermediates explicitly. Formation checks every body and suffix, even
when an operation's meaning might skip a callback or a body might stop.
This is independent Lean syntax, not the native Common format or a native
correctness bridge.
-/

set_option autoImplicit false

namespace Zkc.Source

mutual
  inductive RawRegion (Ty Op : Type) where
    | ret (indices : List Nat)
    | stop (reason : PIR.Stop)
    | letOp (op : Op) (arguments : List Nat) (results : List Ty)
        (bodies : RawRegions Ty Op) (next : RawRegion Ty Op)
    | bind (intermediate : List Ty) (body next : RawRegion Ty Op)

  inductive RawRegions (Ty Op : Type) where
    | nil
    | cons (inputs outputs : List Ty) (body : RawRegion Ty Op) (tail : RawRegions Ty Op)
end

/-- Operand diagnostics reuse the shared checked context lookup.
Callback count diagnostics describe the unmatched suffix of the signature.
-/
inductive RegionFormationError (Ty : Type) where
  | operand (error : FormationError Ty)
  | resultTypes (expected actual : List Ty)
  | regionCount (expected actual : Nat)
  | regionInputs (expected actual : List Ty)
  | regionOutputs (expected actual : List Ty)
  deriving DecidableEq, Repr

def RawRegions.length {Ty Op : Type} : RawRegions Ty Op → Nat
  | .nil => 0
  | .cons _ _ _ tail => tail.length + 1

mutual
  /-- All stored operations, including dormant callbacks and stopped suffixes.
  Calls remain single operations; this traversal does not expand their targets. -/
  def RawRegion.operations {Ty Op : Type} : RawRegion Ty Op → List Op
    | .ret _ | .stop _ => []
    | .letOp op _ _ bodies next => op :: (bodies.operations ++ next.operations)
    | .bind _ body next => body.operations ++ next.operations

  def RawRegions.operations {Ty Op : Type} : RawRegions Ty Op → List Op
    | .nil => []
    | .cons _ _ body rest => body.operations ++ rest.operations
end

variable {dialect : Dialect}

mutual
  /-- Resolve all positions and annotations against the supplied signature. -/
  def RawRegion.elaborate [DecidableEq dialect.Ty] (Γ out : List dialect.Ty) :
      RawRegion dialect.Ty dialect.Op →
        Except (RegionFormationError dialect.Ty) (Region dialect Γ out)
    | .ret indices => do
      let values ← (decodeOperands Γ out indices).mapError RegionFormationError.operand
      pure (.ret values)
    | .stop reason => .ok (.stop reason)
    | .letOp op indices results bodies next => do
      if results ≠ dialect.results op then
        throw (.resultTypes (dialect.results op) results)
      let arguments ←
        (decodeOperands Γ (dialect.arguments op) indices).mapError RegionFormationError.operand
      let bodies ← bodies.elaborate (dialect.regions op)
      let next ← next.elaborate (dialect.results op ++ Γ) out
      pure (.letOp op arguments bodies next)
    | .bind intermediate body next => do
      let body ← body.elaborate Γ intermediate
      let next ← next.elaborate (intermediate ++ Γ) out
      pure (.bind body next)

  /-- A callback sees only its declared inputs, never the surrounding context. -/
  def RawRegions.elaborate [DecidableEq dialect.Ty] :
      (signatures : List (List dialect.Ty × List dialect.Ty)) →
      RawRegions dialect.Ty dialect.Op →
        Except (RegionFormationError dialect.Ty) (Regions dialect signatures)
    | [], .nil => .ok .nil
    | (inputs, outputs) :: rest, .cons declaredInputs declaredOutputs body tail => do
      if declaredInputs ≠ inputs then throw (.regionInputs inputs declaredInputs)
      if declaredOutputs ≠ outputs then throw (.regionOutputs outputs declaredOutputs)
      let body ← body.elaborate inputs outputs
      let tail ← tail.elaborate rest
      pure (.cons body tail)
    | signatures, bodies => .error (.regionCount signatures.length bodies.length)
end

mutual
  def Region.erase {Γ out} : Region dialect Γ out → RawRegion dialect.Ty dialect.Op
    | .ret values => .ret (Operands.indices values)
    | .stop reason => .stop reason
    | .letOp op arguments bodies next =>
      .letOp op (Operands.indices arguments) (dialect.results op) bodies.erase next.erase
    | .bind (mid := intermediate) body next => .bind intermediate body.erase next.erase

  def Regions.erase {signatures} :
      Regions dialect signatures → RawRegions dialect.Ty dialect.Op
    | .nil => .nil
    | .cons (inputs := inputs) (outputs := outputs) body tail =>
      .cons inputs outputs body.erase tail.erase
end

/-- Exact formation after erasure for every typed region, with arbitrary result
lists, bind intermediates and nested callback trees. No meaning is assumed. -/
@[simp] theorem Region.elaborate_erase [DecidableEq dialect.Ty] {Γ out}
    (region : Region dialect Γ out) :
    region.erase.elaborate Γ out = .ok region := by
  induction region using Region.rec
      (motive_2 := fun signatures bodies =>
        bodies.erase.elaborate (dialect := dialect) signatures = .ok bodies) with
  | ret values => simp [Region.erase, RawRegion.elaborate]; rfl
  | stop reason => rfl
  | letOp op arguments bodies next bodiesIH nextIH =>
    simp [Region.erase, RawRegion.elaborate, bodiesIH, nextIH]; rfl
  | bind body next bodyIH nextIH =>
    simp [Region.erase, RawRegion.elaborate, bodyIH, nextIH]; rfl
  | nil => rfl
  | cons body tail bodyIH tailIH =>
    simp [Regions.erase, RawRegions.elaborate, bodyIH, tailIH]; rfl

/-- The roundtrip also preserves all closed callback signatures and bodies. -/
@[simp] theorem Regions.elaborate_erase [DecidableEq dialect.Ty] {signatures}
    (bodies : Regions dialect signatures) :
    bodies.erase.elaborate signatures = .ok bodies := by
  cases bodies with
  | nil => rfl
  | cons body tail =>
    simp [Regions.erase, RawRegions.elaborate, Region.elaborate_erase body,
      Regions.elaborate_erase tail]; rfl
termination_by sizeOf bodies

/-- Acceptance retains the entire raw tree, including operand positions, operation
results, bind intermediates and every nested callback annotation and body. -/
theorem RawRegion.erase_of_elaborate [DecidableEq dialect.Ty]
    (raw : RawRegion dialect.Ty dialect.Op) {Γ out : List dialect.Ty}
    {typed : Region dialect Γ out} (accepted : raw.elaborate Γ out = .ok typed) :
    typed.erase = raw := by
  induction raw using RawRegion.rec
      (motive_2 := fun raw => ∀ {signatures} {typed : Regions dialect signatures},
        raw.elaborate signatures = .ok typed → typed.erase = raw) generalizing Γ out with
  | ret indices =>
    cases decoded : decodeOperands Γ out indices with
    | error error =>
      simp [RawRegion.elaborate, decoded] at accepted
      cases accepted
    | ok values =>
      simp [RawRegion.elaborate, decoded] at accepted
      cases accepted
      simp [Region.erase, indices_of_decodeOperands decoded]
  | stop reason =>
    cases accepted
    rfl
  | letOp op indices results bodies next bodiesIH nextIH =>
    by_cases resultsMatch : results = dialect.results op
    · cases decodedArguments : decodeOperands Γ (dialect.arguments op) indices with
      | error error =>
        simp [RawRegion.elaborate, resultsMatch, decodedArguments] at accepted
        cases accepted
      | ok arguments =>
        cases decodedBodies : bodies.elaborate (dialect.regions op) with
        | error error =>
          simp [RawRegion.elaborate, resultsMatch, decodedArguments, decodedBodies] at accepted
          cases accepted
        | ok typedBodies =>
          cases decodedNext : next.elaborate (dialect.results op ++ Γ) out with
          | error error =>
            simp [RawRegion.elaborate, resultsMatch, decodedArguments, decodedBodies,
              decodedNext] at accepted
            cases accepted
          | ok typedNext =>
            simp [RawRegion.elaborate, resultsMatch, decodedArguments, decodedBodies,
              decodedNext] at accepted
            cases accepted
            simp [Region.erase, indices_of_decodeOperands decodedArguments,
              bodiesIH decodedBodies, nextIH decodedNext, resultsMatch]
    · simp [RawRegion.elaborate, resultsMatch] at accepted
      cases accepted
  | bind intermediate body next bodyIH nextIH =>
    cases decodedBody : body.elaborate Γ intermediate with
    | error error =>
      simp [RawRegion.elaborate, decodedBody] at accepted
      cases accepted
    | ok typedBody =>
      cases decodedNext : next.elaborate (intermediate ++ Γ) out with
      | error error =>
        simp [RawRegion.elaborate, decodedBody, decodedNext] at accepted
        cases accepted
      | ok typedNext =>
        simp [RawRegion.elaborate, decodedBody, decodedNext] at accepted
        cases accepted
        simp [Region.erase, bodyIH decodedBody, nextIH decodedNext]
  | nil =>
    rename_i signatures typed accepted
    cases signatures with
    | nil => cases accepted; rfl
    | cons signature rest => simp [RawRegions.elaborate] at accepted
  | cons declaredInputs declaredOutputs body tail bodyIH tailIH =>
    rename_i signatures typed accepted
    cases signatures with
    | nil => simp [RawRegions.elaborate] at accepted
    | cons signature rest =>
      obtain ⟨inputs, outputs⟩ := signature
      by_cases inputsMatch : declaredInputs = inputs
      · by_cases outputsMatch : declaredOutputs = outputs
        · cases decodedBody : body.elaborate inputs outputs with
          | error error =>
            simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody] at accepted
            cases accepted
          | ok typedBody =>
            cases decodedTail : tail.elaborate rest with
            | error error =>
              simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody,
                decodedTail] at accepted
              cases accepted
            | ok typedTail =>
              simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody,
                decodedTail] at accepted
              cases accepted
              simp [Regions.erase, bodyIH decodedBody, tailIH decodedTail,
                inputsMatch, outputsMatch]
        · simp [RawRegions.elaborate, inputsMatch, outputsMatch] at accepted
          cases accepted
      · simp [RawRegions.elaborate, inputsMatch] at accepted
        cases accepted

/-- Acceptance of callback lists retains all declared signatures and raw bodies. -/
theorem RawRegions.erase_of_elaborate [DecidableEq dialect.Ty]
    (raw : RawRegions dialect.Ty dialect.Op) {signatures}
    {typed : Regions dialect signatures} (accepted : raw.elaborate signatures = .ok typed) :
    typed.erase = raw := by
  cases raw with
  | nil =>
    cases signatures with
    | nil => cases accepted; rfl
    | cons signature rest => simp [RawRegions.elaborate] at accepted
  | cons declaredInputs declaredOutputs body tail =>
    cases signatures with
    | nil => simp [RawRegions.elaborate] at accepted
    | cons signature rest =>
      obtain ⟨inputs, outputs⟩ := signature
      by_cases inputsMatch : declaredInputs = inputs
      · by_cases outputsMatch : declaredOutputs = outputs
        · cases decodedBody : body.elaborate inputs outputs with
          | error error =>
            simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody] at accepted
            cases accepted
          | ok typedBody =>
            cases decodedTail : tail.elaborate rest with
            | error error =>
              simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody,
                decodedTail] at accepted
              cases accepted
            | ok typedTail =>
              simp [RawRegions.elaborate, inputsMatch, outputsMatch, decodedBody,
                decodedTail] at accepted
              cases accepted
              simp [Regions.erase, RawRegion.erase_of_elaborate body decodedBody,
                RawRegions.erase_of_elaborate tail decodedTail, inputsMatch, outputsMatch]
        · simp [RawRegions.elaborate, inputsMatch, outputsMatch] at accepted
          cases accepted
      · simp [RawRegions.elaborate, inputsMatch] at accepted
        cases accepted
termination_by sizeOf raw

end Zkc.Source

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Source.RawRegion.operations
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Source.RawRegions.operations
