module

public import Zkc.Core.SerializeReplayRegions
public import Zkc.Core.ThreadProgram
public import Zkc.Core.ThreadEntrySerialize

public section

/-! The parts of every protocol of a program that is serialized replay its grouped run.

`rewriteProtocols_replays`: for the protocols of a program on which the serialize step
returns, every protocol and every way it is reached from the declared entry (`Reached`):

- reached as the entry, or by an application with a pair of roles for which it has the image
  that threads: the grouped process and the two parts under handlers that follow the marks
  of the step are related over the channel of the step (`ThreadedReplays`);
- reached by an application in any other way: they are related under the handlers that
  perform every effect as it is (`PlainReplays`).

The induction follows the protocols in program order, as `rewriteProtocols` recurses. For
one definition, `touches` is a finding for every way it is reached, since the step returned
(`classify`); the definition has the image that threads for a pair of roles for which it
changes; and its applications reach their callees with the preimages of the two roles, so
the statement for the earlier protocols covers every callee. That a handler which follows
the marks fits the body is `region_fits`, and that the layout carries the messages of the
body is `rewriteProtocols_newest_carries`: both follow from the equation of the step.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Program

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {functionTable : FunctionTable model functions}

/-- The statement for a protocol and a way it is reached. -/
@[expose] def DemandReplays {old : List ProtocolHeader} (layout : Layout operations)
    (laws : layout.Lawful model) (threads : Nat → TranscriptRoles → Bool)
    (marks : MarkTable operations old) (oldTable : ProtocolTable model old)
    {header : ProtocolHeader} (callee : Var old header) : Demand → Prop
  | .entry roles => ThreadedReplays layout laws marks oldTable callee roles
  | .applied prover verifier =>
      CalleeReplays layout laws threads marks oldTable callee prover verifier

/-- A definition without a rewritten operation for a pair of roles, either of which may be
absent, when the callees it applies are related. -/
theorem definition_replays_plain {t : Threads} {old new : List ProtocolHeader}
    {table : CalleeTable t.header old new} (quiet : QuietTable functionTable)
    {oldTable : ProtocolTable model old} (idle : CalleesIdle oldTable) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (identity : Nat)
    (prover verifier : Option Nat)
    (untouched : touches t false table identity prover verifier definition.body = .ok false)
    (callees : ∀ {other : ProtocolHeader} (callee : Var old other) (roleMap : RoleMap),
      (callee.index, roleMap) ∈ applications definition.body [] →
      ¬Threaded table.threads callee.index (preimageOf roleMap prover)
        (preimageOf roleMap verifier) →
      PlainReplays oldTable callee (preimageOf roleMap prover) (preimageOf roleMap verifier)) :
    PlainReplays (Values.cons (definition.meaning model functionTable oldTable identity) oldTable)
      (Var.here : Var (header :: old) header) prover verifier := by
  intro Writer Reader channel path first second disjoint holdsProver holdsVerifier arguments
  exact region_replays definition.body
    (region_admits_plain quiet idle channel identity prover verifier header.roles
      (ownSites identity path) first second disjoint holdsProver holdsVerifier definition.body none
      [] (definition.body_legal wellFormed) (definition_shape definition wellFormed).1 untouched
      callees)
    _ _ _ (Restricts.ofValues arguments) (Restricts.ofValues arguments)

/-- A definition that is reached with a pair of roles, under handlers that follow its
marks for the pair, when `touches` is a finding, the layout carries the messages of the body
and the callees it applies are related. -/
theorem definition_replays_threaded (layout : Layout operations) (laws : layout.Lawful model)
    {old new : List ProtocolHeader} {table : CalleeTable layout.threads.header old new}
    (quiet : QuietTable functionTable) {oldTable : ProtocolTable model old}
    (idle : CalleesIdle oldTable) (passes : TablePasses oldTable) (marks : MarkTable operations old)
    {header : ProtocolHeader} (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (identity : Nat) (specialized : Bool)
    (inner : TranscriptRoles) {active : Bool}
    (accepted : touches layout.threads false table identity (some inner.prover)
      (some inner.verifier) definition.body = .ok active)
    (carries : RegionCarries layout inner definition.body)
    (callees : ∀ {other : ProtocolHeader} (callee : Var old other) (roleMap : RoleMap),
      (callee.index, roleMap) ∈ applications definition.body [] →
      CalleeReplays layout laws table.threads marks oldTable callee
        (preimageOf roleMap (some inner.prover)) (preimageOf roleMap (some inner.verifier))) :
    ThreadedReplays layout laws
      (Values.cons (fun roles => regionMarks table.threads marks ⟨identity, roles, specialized⟩
        definition.body) marks)
      (Values.cons (definition.meaning model functionTable oldTable identity) oldTable)
      (Var.here : Var (header :: old) header) inner := by
  intro path first second disjoint holdsProver holdsVerifier proverWrites proverReads verifierWrites
    verifierReads sameProverWrites sameProverReads sameVerifierWrites sameVerifierReads writes reads
    proverHandler verifierHandler followsProver followsVerifier arguments
  subst sameProverWrites sameProverReads sameVerifierWrites sameVerifierReads
  obtain ⟨noReader, noWriter, _⟩ :=
    roles_apart ⟨identity, inner, specialized⟩ first second disjoint writes reads
  have fitsProver := region_fits (serializeRule (functions := functions) layout)
    (serializeMeaning layout) quiet passes table marks ⟨identity, inner, specialized⟩ first
    (.inl ⟨writes, noReader⟩) identity path proverHandler definition.body
    (ProtocolDefinition.regionSites_nodup wellFormed) followsProver
  have fitsVerifier := region_fits (serializeRule (functions := functions) layout)
    (serializeMeaning layout) quiet passes table marks ⟨identity, inner, specialized⟩ second
    (.inr ⟨noWriter, reads⟩) identity path verifierHandler definition.body
    (ProtocolDefinition.regionSites_nodup wellFormed) followsVerifier
  exact region_replays definition.body
    (region_admits layout laws quiet idle marks ⟨identity, inner, specialized⟩ header.roles
      (ownSites identity path) first second disjoint holdsProver holdsVerifier writes reads
      proverHandler verifierHandler definition.body none [] (definition.body_legal wellFormed)
      (definition_shape definition wellFormed).1 ⟨active, accepted⟩ carries fitsProver fitsVerifier
      callees)
    _ _ _ (Restricts.ofValues arguments) (Restricts.ofValues arguments)

/-- Every protocol of a program on which the serialize step returns, for every way it is
reached: the grouped process and the two parts are related. -/
theorem rewriteProtocols_replays (layout : Layout operations) (laws : layout.Lawful model)
    (quiet : QuietTable functionTable) (identities : Identities) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      (demands : List (List Demand))
      (rewritten : Rewritten layout.threads typeTable operations functions old),
      rewriteProtocols layout.threads (serializeRule layout) identities protocols demands =
        .ok rewritten →
      ∀ {header : ProtocolHeader} (callee : Var old header) (demand : Demand),
        Reached demands callee.index demand →
        DemandReplays layout laws rewritten.table.threads rewritten.marks
          (protocols.table model functionTable identities) callee demand
  | _, .nil, _, _, _, _, callee, _, _ => callee.elimNil
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition wellFormed,
      demands, rewritten, rewrites, other, callee, demand, reached => by
      obtain ⟨prior, specialized, rewritesEarlier, sameMarks, sameTable, classified⟩ :=
        rewriteProtocols_newest_images (serializeRule_external layout) identities earlier definition
          wellFormed demands rewritten rewrites
      have carried := rewriteProtocols_newest_carries layout identities earlier definition wellFormed
        demands rewritten rewrites
      have ih := fun {inner : ProtocolHeader} (applied : Var earlierHeaders inner) (way : Demand)
          (reaches : Reached (propagate (demands.headD []) (applications definition.body [])
            demands.tail) applied.index way) =>
        rewriteProtocols_replays layout laws quiet identities earlier _ prior rewritesEarlier
          applied way reaches
      rw [sameMarks]
      cases callee with
      | there callee =>
          have statement := ih callee demand (propagate_mono _ _ _ _ _ reached.earlier)
          cases demand with
          | entry roles => exact statement
          | applied prover verifier =>
              exact ⟨fun inner atProver atVerifier threads =>
                  statement.1 inner atProver atVerifier ((sameTable _ _).symm.trans threads),
                fun notThreaded => statement.2 fun ⟨inner, atProver, atVerifier, threads⟩ =>
                  notThreaded ⟨inner, atProver, atVerifier, (sameTable _ _).trans threads⟩⟩
      | here =>
          obtain ⟨active, touched, images⟩ := classified demand reached.newest
          have idle : CalleesIdle (earlier.table model functionTable identities) :=
            program_idle functionTable identities earlier
          have passes : TablePasses (earlier.table model functionTable identities) :=
            Protocols.table_passes quiet identities earlier
          have callees : ∀ {inner : ProtocolHeader} (applied : Var earlierHeaders inner)
              (roleMap : RoleMap), (applied.index, roleMap) ∈ applications definition.body [] →
              CalleeReplays layout laws prior.table.threads prior.marks
                (earlier.table model functionTable identities) applied
                (preimageOf roleMap demand.prover) (preimageOf roleMap demand.verifier) :=
            fun applied roleMap applies =>
              ih applied _ (propagate_reached_applied _ _ _ reached.newest applies)
          cases demand with
          | entry roles =>
              exact definition_replays_threaded layout laws quiet idle passes prior.marks definition
                wellFormed _ specialized roles touched (carried _ reached.newest roles rfl rfl) callees
          | applied prover verifier =>
              refine ⟨fun inner atProver atVerifier threads => ?_, fun notThreaded => ?_⟩
              · subst atProver atVerifier
                exact definition_replays_threaded layout laws quiet idle passes prior.marks
                  definition wellFormed _ specialized inner touched
                  (carried _ reached.newest inner rfl rfl) callees
              · cases active with
                | false =>
                    exact definition_replays_plain quiet idle definition wellFormed _ prover verifier
                      touched fun applied roleMap applies => (callees applied roleMap applies).2
                | true =>
                    obtain ⟨hasProver, hasVerifier⟩ := touches_some definition.body touched
                    cases prover with
                    | none => cases hasProver
                    | some prover =>
                        cases verifier with
                        | none => cases hasVerifier
                        | some verifier =>
                            exact absurd ⟨⟨prover, verifier⟩, rfl, rfl, images prover verifier rfl rfl⟩
                              notThreaded

end Program

end Zkc.Core
