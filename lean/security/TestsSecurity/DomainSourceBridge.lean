module

public import ZkcSecurity.FiatShamir.DomainViewReading
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator

@[expose] public section

/-! A control on the real constructed SmallSumcheck round challenge. The exact
artifact instruction and its generated equation are used; no copied protocol
body or source invocation is substituted. This is a local integration control,
not a whole-root security receipt. -/
set_option autoImplicit false
namespace TestsSecurity.DomainSourceBridge
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir.DomainReduction

abbrev field := "bls12-381.fr"
abbrev suite := ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.policy.suite

def context : Context :=
  Context.fiatShamir (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.policy.entry) ([ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.policy.producer, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.policy.validator]) 0 1 3 "random.bls12-381.fr/0" (some (.draw field)) (suite) (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.policy.draws)

abbrev instruction : Instruction :=
  ((ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact.instructions[2]'(by decide +kernel)).body[13]'(by decide +kernel))

def template : Template :=
  match instruction.operation with
  | .challenge _ _ template => template
  | _ => ⟨"", [], []⟩

def origin : Origin :=
  (Domain.queryOrigin context suite field template [0]).get (by decide +kernel)

theorem origin_found : Domain.queryOrigin context suite field template [0] = some origin :=
  (Option.some_get _).symm

theorem origin_request : origin.request = some (.draw field) :=
  Domain.queryOrigin_request context suite field template [0] origin origin_found

abbrev historyPosition : Nat := instruction.operands[0]'(by decide +kernel)
abbrev coordinatesPosition : Nat := instruction.operands[1]'(by decide +kernel)

def environment (model : Structured.DomainModel) (history : Domain.History model.toCarriers) :
    Domain.Environment model.toCarriers :=
  List.replicate historyPosition (.data (.index 0)) ++ [.transcript suite history] ++
    List.replicate (coordinatesPosition - historyPosition - 1) (.data (.index 0)) ++ [.indices [0]]

/-- Every typed challenge reply, complete SSA environment, and carried history
is preserved at the actual source round's checked constructed query seam. -/
theorem actual_challenge (model : Structured.DomainModel) (program : Structured.Program)
    (history : Domain.History model.toCarriers) :
    Bridge queryInterface (fun _ _ => True) history
      (Domain.step model program context instruction (environment model history))
      (.call (.query history origin) fun raw => .done
        (environment model history ++ [.data (.field field (fieldReply origin_request raw)),
          .transcript suite (history ++ [.challenge origin])])) := by
  rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep2BodyStep13_eq model program context]
  change Bridge queryInterface (fun _ _ => True) history
    (Domain.View.challenge context suite field template historyPosition coordinatesPosition
      [.data (.field field), .transcript suite] (environment model history)) _
  exact ⟨challenge_reading context suite field template historyPosition coordinatesPosition _ history [0] origin
    (by rfl) (by rfl) origin_found origin_request,
    challenge_coherent context suite field template historyPosition coordinatesPosition _ history [0] origin
      (by rfl) (by rfl) origin_found origin_request⟩

end TestsSecurity.DomainSourceBridge
