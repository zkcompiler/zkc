module

public import ZkcExamples.Structured.OriginalSumcheckLibrary
public import ZkcSecurity.Families.Sumcheck.TableComponentPrefix

@[expose] public section

/-! Shared original call context and table mathematics. Honest readback uses
the reference layout and full source result embedding; all-input source
correspondence uses the call context and observed loop site. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ZkcSecurity.Realizations.Sumcheck.Original
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open SumcheckVerifierBodies
open ZkcSecurity.Families.Sumcheck TableComponent

variable {F G Frame : Type} [Field F] [DecidableEq F]

structure Context where
  protocol : ProtocolContext
  handle : Nat

abbrev signature := OriginalSumcheckLibrary.signature (F := F) (G := G)

def loopSite (context : Context) : String :=
  qualifyProtocolSite context.protocol.applicationPrefix "s15"

noncomputable def program :
    Program (signature (F := F) (G := G)) Context (PrefixState F Frame) (Message.endpoints F) where
  claim state := state.scalar
  receive context state :=
    .call (.enter ⟨loopSite context, state.point.length⟩) fun _ =>
    .call (.action (.receive (.field "bls12-381.fr")
      (SumcheckVerifierLaws.lowSite context.protocol) (context.protocol.roles 0))) fun low =>
    .call (.action (.receive (.field "bls12-381.fr")
      (SumcheckVerifierLaws.highSite context.protocol) (context.protocol.roles 0))) fun high =>
    .done (some (low, high))
  query context _ _ := .action (.query (SumcheckVerifierLaws.challengeSite context.protocol)
    "bls12-381.fr" (.cons context.handle .nil))
  challenge _ _ _ reply := reply
  deliver context state _ challenge :=
    .call (.action (.send (ty := .field "bls12-381.fr")
      (SumcheckVerifierLaws.deliverySite context.protocol) (context.protocol.roles 0) challenge)) fun _ =>
    .call (.leave ⟨loopSite context, state.point.length⟩) fun _ => .done ()
  advance _ state message challenge := state.advance message challenge

/-- The same table mathematics covers every false claim and every endpoint
pair. Exact shape is independent of truth and all caller data remains in Frame. -/
noncomputable def layout : Layout (program (F := F) (G := G) (Frame := Frame)) where
  entries := PrefixState.entries
  shape := PrefixState.entries_shape
  advance _ state message challenge := PrefixState.advance_entries state message challenge
  claim _ _ _ _ := rfl

end ZkcSecurity.Realizations.Sumcheck.Original
