module

public import Zkc.Tests.Protocol.Construction.Pilot
public import Zkc.Tests.Protocol.Construction.AdaptiveSource
public meta import Lean

/-! Stored proof-body checks for repeated and nested calls. These inspect declaration
references, not source text or pretty-printed proof terms. Runtime loop counts are varied
separately from static source size. No semantic charge is removed by proof sharing. -/

@[expose] public section
noncomputable section
set_option experimental.vcgen true
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples.ConstructionPilot

namespace ProtocolProofExamples.ConstructionSharing

attribute [local instance] proofLogic

def flat1 : Region (scalarDialect language) [(), ()] [()] :=
  (.bind helper (.ret (.singleton .here)))

theorem flat1_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      flat1.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold flat1
  construct_region

def flat2 : Region (scalarDialect language) [(), ()] [()] :=
  (.bind helper (.bind (helper.rename (fun ref => .there (ref))) (.ret (.singleton .here))))

theorem flat2_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      flat2.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold flat2
  construct_region

def flat4 : Region (scalarDialect language) [(), ()] [()] :=

    (.bind helper
    (.bind (helper.rename (fun ref => .there (ref)))
    (.bind (helper.rename (fun ref => .there (.there (ref))))
    (.bind (helper.rename (fun ref => .there (.there (.there (ref)))))
      (.ret (.singleton .here))))))

theorem flat4_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      flat4.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold flat4
  construct_region

def flat8 : Region (scalarDialect language) [(), ()] [()] :=

    (.bind helper
    (.bind (helper.rename (fun ref => .there (ref)))
    (.bind (helper.rename (fun ref => .there (.there (ref))))
    (.bind (helper.rename (fun ref => .there (.there (.there (ref)))))
    (.bind (helper.rename (fun ref => .there (.there (.there (.there (ref))))))
    (.bind (helper.rename (fun ref => .there (.there (.there (.there (.there (ref)))))))
    (.bind (helper.rename (fun ref => .there (.there (.there (.there (.there (.there (ref))))))))
    (.bind (helper.rename (fun ref => .there (.there (.there (.there (.there (.there (.there (ref)))))))))
      (.ret (.singleton .here))))))))))

theorem flat8_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      flat8.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold flat8
  construct_region

def nested1 : Region (scalarDialect language) [(), ()] [()] :=
  helper

@[spec high] theorem nested1_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      nested1.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold nested1
  construct_region

def nested2 : Region (scalarDialect language) [(), ()] [()] :=
  .bind nested1 (.bind (nested1.rename (fun ref => .there ref)) (.ret (.singleton .here)))

@[spec high] theorem nested2_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      nested2.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold nested2
  construct_region

def nested4 : Region (scalarDialect language) [(), ()] [()] :=
  .bind nested2 (.bind (nested2.rename (fun ref => .there ref)) (.ret (.singleton .here)))

@[spec high] theorem nested4_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      nested4.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold nested4
  construct_region

def nested8 : Region (scalarDialect language) [(), ()] [()] :=
  .bind nested4 (.bind (nested4.rename (fun ref => .there ref)) (.ret (.singleton .here)))

@[spec high] theorem nested8_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      nested8.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  unfold nested8
  construct_region

section RuntimeCounts
attribute [local instance] AdaptiveSource.upperLogic
theorem count0_law (e : AdaptiveChecks.Environment)
    (env : Environment (AdaptiveSource.meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (AdaptiveSource.potential (AdaptiveChecks.factor e.residual ^ 0 * value)
      (env .here))⦄
      (AdaptiveSource.rounds 0).denote (AdaptiveSource.meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (AdaptiveSource.potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  construct_region

theorem count1_law (e : AdaptiveChecks.Environment)
    (env : Environment (AdaptiveSource.meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (AdaptiveSource.potential (AdaptiveChecks.factor e.residual ^ 1 * value)
      (env .here))⦄
      (AdaptiveSource.rounds 1).denote (AdaptiveSource.meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (AdaptiveSource.potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  construct_region

theorem count8_law (e : AdaptiveChecks.Environment)
    (env : Environment (AdaptiveSource.meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (AdaptiveSource.potential (AdaptiveChecks.factor e.residual ^ 8 * value)
      (env .here))⦄
      (AdaptiveSource.rounds 8).denote (AdaptiveSource.meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (AdaptiveSource.potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  construct_region

theorem count1024_law (e : AdaptiveChecks.Environment)
    (env : Environment (AdaptiveSource.meaning e).Value [.accumulator]) (value : ENNReal) :
    ⦃OrderDual.toDual (AdaptiveSource.potential (AdaptiveChecks.factor e.residual ^ 1024 * value)
      (env .here))⦄
      (AdaptiveSource.rounds 1024).denote (AdaptiveSource.meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (AdaptiveSource.potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  construct_region

end RuntimeCounts

end ProtocolProofExamples.ConstructionSharing
