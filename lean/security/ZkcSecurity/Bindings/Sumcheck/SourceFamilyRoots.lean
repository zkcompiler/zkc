module

public import ZkcSecurity.Bindings.Sumcheck.SourceFamily
public import Zkc.Source.Structured.NormalizedRoot

@[expose] public section

/-! Root-owned normal forms instantiate one installed family callee. All local
helpers are kept from the admitted library, with no source-selected SSA slots,
call sites, terminal trees or declaration positions in the family interface. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamily
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured NormalForm ZkcExamples.Structured
variable {program : Zkc.Source.Structured.Program} (installation : Installation program)

def producerSignature : Signature :=
  ⟨[], false, true, program.payload.definitions.map CheckedDefinition.helper,
    [⟨reductionSignature installation.reductionName, 0, producerPattern, [none,none,none,none]⟩]⟩

variable (model : DomainModel)

def producerCallees :
    CalleeProcesses model (producerSignature installation).callees (Occurrence.signature model.toCarriers) :=
  fun entry => match entry with
  | ⟨0, _⟩ => producerReduction installation model
  | ⟨_+1, outside⟩ => absurd outside (by simp [producerSignature])

theorem producerCallees_hold {types : List Ty} (input : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model program.payload) (producerCallees installation model) input := by
  intro entry ctx args others _ distinct
  match entry with
  | ⟨0, _⟩ => exact producer_invoke installation model ctx distinct args others
  | ⟨_+1, outside⟩ => exact absurd outside (by simp [producerSignature])

def producerResults : LawResults model (producerSignature installation).laws := ⟨fun entry => Fin.elim0 entry⟩

theorem producer_equation
    (root : Zkc.Source.Structured.NormalizedRoot.Checked program 0 (producerSignature installation))
    (args : Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 0).scope) :
    Occurrence.participant model program 0 (Zkc.Source.Structured.NormalizedRoot.inputs model args) =
      (root.form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload)
        (producerResults installation model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
          (Occurrence.table model program.payload) {} 0) (producerCallees installation model) args).bind
            fun returned => .done (maskValues 0 program.payload.entry.outputScopes returned) :=
  Zkc.Source.Structured.NormalizedRoot.equation root model args (producerResults installation model) (producerCallees installation model)
    (fun entry => Fin.elim0 entry) (producerCallees_hold installation model _)

def validatorSignature : Signature :=
  ⟨[], false, true, program.payload.definitions.map CheckedDefinition.helper,
    [⟨reductionSignature installation.reductionName, 1, validatorPattern, [none,none,none,none]⟩]⟩

variable (model : DomainModel)

def validatorCallees :
    CalleeProcesses model (validatorSignature installation).callees (Occurrence.signature model.toCarriers) :=
  fun entry => match entry with
  | ⟨0, _⟩ => fun ctx args => SumcheckReductionReference.reference model program.payload.definitions
    (Occurrence.table model program.payload) installation.maximum ctx
    (entryAt args .here) (entryAt args (.there .here)) (entryAt args (.there (.there .here)))
    (entryAt args (.there (.there (.there .here))))
  | ⟨_+1, outside⟩ => absurd outside (by simp [validatorSignature])

theorem validatorCallees_hold {types : List Ty} (input : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model program.payload) (validatorCallees installation model) input := by
  intro entry ctx args others _ distinct
  match entry with
  | ⟨0, _⟩ => exact validator_invoke installation model ctx distinct args others
  | ⟨_+1, outside⟩ => exact absurd outside (by simp [validatorSignature])

def validatorResults : LawResults model (validatorSignature installation).laws := ⟨fun entry => Fin.elim0 entry⟩

theorem validator_equation
    (root : Zkc.Source.Structured.NormalizedRoot.Checked program 1 (validatorSignature installation))
    (args : Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope) :
    Occurrence.participant model program 1 (Zkc.Source.Structured.NormalizedRoot.inputs model args) =
      (root.form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload)
        (validatorResults installation model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
          (Occurrence.table model program.payload) {} 1) (validatorCallees installation model) args).bind
            fun returned => .done (maskValues 1 program.payload.entry.outputScopes returned) :=
  Zkc.Source.Structured.NormalizedRoot.equation root model args (validatorResults installation model) (validatorCallees installation model)
    (fun entry => Fin.elim0 entry) (validatorCallees_hold installation model _)

end ZkcSecurity.Realizations.Sumcheck.SourceFamily
