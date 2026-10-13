module

public import Zkc.Source.Constructed.Execution
public import Zkc.Source.FiniteControl

@[expose] public section

/-! Structured composition of checked constructed-source fragments.

Runtime iteration retains one body, explicit captures and an ordered carried
tuple. The count is checked before entering the body. Normal completion enters
the suffix; an effect stop terminates the process with its actual state/events.
Native export and the interpretation of unsigned indices are separate boundaries.
-/

namespace Zkc.Source.Constructed.Control

set_option backward.isDefEq.respectTransparency false

def append {V : String → Type} {Γ Δ : List String} :
    Values V Γ → Values V Δ → Values V (Γ ++ Δ)
  | .nil, right => right
  | .cons value rest, right => .cons value (append rest right)

def scalars {V : String → Type} {Γ : List String} :
    Values V Γ → Values (Values V) (Γ.map scalar)
  | .nil => .nil
  | .cons value rest => .cons (.cons value .nil) (scalars rest)

/-- Index representation is explicit. This does not assert native ui64
implementation conformance or provide an arbitrary integer overflow convention. -/
structure Meaning (I : PIR.Signature) extends Constructed.Meaning I where
  index : Nat → Value "ui64"
  count : Value "ui64" → Nat

inductive Body : List String → List String → Type where
  | flat {Γ outputs} (program : Program language (Γ.map scalar) outputs) : Body Γ outputs
  | sequence {Γ intermediate outputs}
      (first : Body Γ intermediate) (next : Body intermediate outputs) : Body Γ outputs
  | branch {Γ outputs} (condition : Var Γ "i1") (yes no : Body Γ outputs) : Body Γ outputs
  | loop {Γ carried captures outputs} (maximum : Nat) (count : Var Γ "ui64")
      (initial : Operands Γ carried) (captured : Operands Γ captures)
      (body : Body ("ui64" :: (carried ++ captures)) carried)
      (next : Body (carried ++ Γ) outputs) : Body Γ outputs

def Body.denote {I : PIR.Signature} (meaning : Meaning I) :
    {Γ outputs : List String} → Body Γ outputs →
      Values meaning.Value Γ → PIR.Proc I (Values meaning.Value outputs)
  | _, _, .flat program, values =>
      program.denote meaning.toMeaning.interpretation (scalars values).get
  | _, _, .sequence first next, values =>
      (first.denote meaning values).bind (next.denote meaning)
  | _, _, .branch condition yes no, values =>
      if meaning.condition (values.get condition) then yes.denote meaning values
      else no.denote meaning values
  | _, _, .loop maximum count initial captured body next, values =>
      let selected := meaning.count (values.get count)
      if selected ≤ maximum then
        (FiniteControl.iterateFrom selected 0
          (fun index carried => body.denote meaning
            (.cons (meaning.index index) (append carried (Operands.eval values.get captured))))
          (Operands.eval values.get initial)).bind
            (fun carried => next.denote meaning (append carried values))
      else .halt .refused

inductive RawBody where
  | flat (instructions : List Instruction) (returned : List Nat)
  | sequence (intermediate : List String) (first next : RawBody)
  | branch (condition : Nat) (yes no : RawBody)
  | loop (maximum count : Nat) (carried : List String) (initial : List Nat)
      (captures : List String) (captured : List Nat) (body next : RawBody)
  deriving DecidableEq, Repr

/-- All bodies and suffixes are checked, including zero-trip loops and dormant
branches. Bounds are runtime admission, not a reason to skip static checking. -/
def RawBody.elaborate (Γ outputs : List String) : RawBody → Except String (Body Γ outputs)
  | .flat instructions returned => do
      let raw ← lower outputs returned instructions
      let program ← (raw.elaborate (language := language) (Γ.map scalar) outputs).mapError
        (fun _ => "constructed-control-operands")
      return .flat program
  | .sequence intermediate first next => do
      return .sequence (← first.elaborate Γ intermediate) (← next.elaborate intermediate outputs)
  | .branch index yes no => do
      let condition ← (decodeVariable Γ "i1" index).mapError (fun _ => "constructed-control-condition")
      return .branch condition (← yes.elaborate Γ outputs) (← no.elaborate Γ outputs)
  | .loop maximum index carried initial captures captured body next => do
      let count ← (decodeVariable Γ "ui64" index).mapError (fun _ => "constructed-control-count")
      let initial ← (decodeOperands Γ carried initial).mapError (fun _ => "constructed-control-carried")
      let captured ← (decodeOperands Γ captures captured).mapError (fun _ => "constructed-control-captures")
      return .loop maximum count initial captured
        (← body.elaborate ("ui64" :: (carried ++ captures)) carried)
        (← next.elaborate (carried ++ Γ) outputs)

/-- Execute the raw structured carrier directly. Flat execution uses the
independent instruction evaluator, not the typed fragment produced by admission. -/
def RawBody.denote {I : PIR.Signature} (meaning : Meaning I) :
    RawBody → {Γ : List String} → (outputs : List String) →
      Values meaning.Value Γ → PIR.Proc I (Values meaning.Value outputs)
  | .flat instructions returned, _, outputs, values =>
      denoteInstructions meaning.toMeaning outputs returned instructions (scalars values).get
  | .sequence intermediate first next, _, outputs, values =>
      (first.denote meaning intermediate values).bind (next.denote meaning outputs)
  | .branch index yes no, Γ, outputs, values =>
      match decodeVariable Γ "i1" index with
      | .error _ => .halt .refused
      | .ok condition =>
          if meaning.condition (values.get condition) then yes.denote meaning outputs values
          else no.denote meaning outputs values
  | .loop maximum index carried initial captures captured body next, Γ, outputs, values =>
      match decodeVariable Γ "ui64" index, decodeOperands Γ carried initial,
          decodeOperands Γ captures captured with
      | .ok count, .ok initial, .ok captured =>
          let selected := meaning.count (values.get count)
          if selected ≤ maximum then
            (FiniteControl.iterateFrom selected 0
              (fun index state => body.denote meaning carried
                (.cons (meaning.index index) (append state (Operands.eval values.get captured))))
              (Operands.eval values.get initial)).bind
                (fun state => next.denote meaning outputs (append state values))
          else .halt .refused
      | _, _, _ => .halt .refused

theorem RawBody.denote_elaborate {I : PIR.Signature} (meaning : Meaning I)
    (raw : RawBody) {Γ outputs} (program : Body Γ outputs)
    (checked : raw.elaborate Γ outputs = .ok program) (values : Values meaning.Value Γ) :
    raw.denote meaning outputs values = program.denote meaning values := by
  induction raw generalizing Γ outputs with
  | flat instructions returned =>
      cases lowered : lower outputs returned instructions with
      | error e => simp [elaborate, lowered] at checked; cases checked
      | ok fragment =>
          simp only [RawBody.elaborate, lowered] at checked
          dsimp only [Bind.bind, Except.instMonad, Except.bind, Pure.pure, Except.pure] at checked
          cases formed : fragment.elaborate (language := language) (Γ.map scalar) outputs with
          | error e => rw [formed] at checked; cases checked
          | ok typed =>
              rw [formed] at checked
              cases checked
              exact (lower_denotation meaning.toMeaning outputs returned instructions fragment
                lowered (scalars values).get).trans
                  (fragment.denote_elaborate meaning.toMeaning.interpretation typed formed _)
  | sequence intermediate first next firstIH nextIH =>
      cases firstEq : first.elaborate Γ intermediate with
      | error e => simp [elaborate, firstEq] at checked; cases checked
      | ok left =>
          cases nextEq : next.elaborate intermediate outputs with
          | error e => simp [elaborate, firstEq, nextEq] at checked; cases checked
          | ok right =>
              simp [elaborate, firstEq, nextEq] at checked
              cases checked
              simp only [RawBody.denote, Body.denote, firstIH left firstEq values]
              congr 1
              funext result
              exact nextIH right nextEq result
  | branch index yes no yesIH noIH =>
      cases lookup : decodeVariable Γ "i1" index with
      | error e => simp [elaborate, lookup] at checked; cases checked
      | ok condition =>
          cases yesEq : yes.elaborate Γ outputs with
          | error e => simp [elaborate, lookup, yesEq] at checked; cases checked
          | ok left =>
              cases noEq : no.elaborate Γ outputs with
              | error e => simp [elaborate, lookup, yesEq, noEq] at checked; cases checked
              | ok right =>
                  simp [elaborate, lookup, yesEq, noEq] at checked
                  cases checked
                  simp only [RawBody.denote, lookup, Body.denote,
                    yesIH left yesEq values, noIH right noEq values]
  | loop maximum index carried initial captures captured body next bodyIH nextIH =>
      cases countEq : decodeVariable Γ "ui64" index with
      | error e => simp [elaborate, countEq] at checked; cases checked
      | ok count =>
          cases initialEq : decodeOperands Γ carried initial with
          | error e => simp [elaborate, countEq, initialEq] at checked; cases checked
          | ok initial =>
              cases capturedEq : decodeOperands Γ captures captured with
              | error e => simp [elaborate, countEq, initialEq, capturedEq] at checked; cases checked
              | ok captured =>
                  cases bodyEq : body.elaborate ("ui64" :: (carried ++ captures)) carried with
                  | error e => simp [elaborate, countEq, initialEq, capturedEq, bodyEq] at checked; cases checked
                  | ok iteration =>
                      cases nextEq : next.elaborate (carried ++ Γ) outputs with
                      | error e =>
                          simp [elaborate, countEq, initialEq, capturedEq, bodyEq, nextEq] at checked
                          cases checked
                      | ok suffix =>
                          simp [elaborate, countEq, initialEq, capturedEq, bodyEq, nextEq] at checked
                          cases checked
                          simp only [RawBody.denote, countEq, initialEq, capturedEq, Body.denote]
                          split
                          · congr 1
                            · congr 1
                              funext index state
                              exact bodyIH iteration bodyEq _
                            · funext state
                              exact nextIH suffix nextEq _
                          · rfl

end Zkc.Source.Constructed.Control
