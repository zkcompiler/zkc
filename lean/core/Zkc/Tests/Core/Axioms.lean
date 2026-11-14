import Zkc.Core.ThreadFiatShamir
import Zkc.Core.ThreadCompose
import Zkc.Core.ThreadEntryRules
import Zkc.Core.VocabularyModel
import Zkc.Core.VocabularyExecute
import Zkc.Core.ProjectProgramMeaning
import Zkc.Core.EndpointsCompleteness
import Zkc.Core.DerivedCompleteness
import Zkc.Core.DerivedScheme
import Zkc.Core.VocabularyScheme
import Zkc.Core.LegalProject
import Zkc.Core.LegalExpand
import Zkc.Core.LegalStep
import Zkc.Core.LegalSites
import Zkc.Core.Link
import Zkc.Core.FactsSound
import Zkc.Core.ProtocolFactsProject

/-! The axioms of the theorems of the package: the round trip and the links, expansion,
flattening and projection, the structural theorem of the threading steps and their
whole-program theorem, the endpoint lemma, completeness of the scheme that the construction
steps derive, the statements that a legal program is not refused, the domain laws of the
model of the vocabulary, the laws of the formats and of the canonical layout, and the
statements of the limit on the work of reading.

Every theorem listed depends on `propext`, `Quot.sound` and `Classical.choice` at most; the
build prints the set of each. Every theorem of the completeness of a derived scheme is
listed in `Tests/Core/ThreadTogether.lean`, `Tests/Core/SerializeReplay.lean`,
`Tests/Core/DerivedScheme.lean` and `Tests/Core/VocabularyScheme.lean`; the principal ones
are also here. -/

open Zkc.Source Zkc.Core

-- Elaboration and the links.
#print axioms elaborate_unelaborate
#print axioms LinkedPackage.unelaborates
#print axioms LinkedPackage.elaborates
#print axioms LinkedPackage.elaboratesWritten

-- The iterations of a loop.
#print axioms loopIterations_carried
#print axioms loopProcess_within
#print axioms loopProcess_beyond
#print axioms loopIterations_quiet

-- A function that passes the check of facts never stops `undefined`.
#print axioms Model.unit_domainLaws
#print axioms Builtin.sound
#print axioms LocalOp.sound
#print axioms sum_bounded
#print axioms LocalOp.branch_returns
#print axioms justifyRegion_sound
#print axioms Functions.never_undefined
#print axioms Functions.all_never_undefined
#print axioms Program.never_undefined

-- A protocol that passes the check of facts never stops `undefined`, for any side, and
-- neither does the program of any of its roles.
#print axioms ProtocolOp.sound
#print axioms justifyProtocol_sound
#print axioms Protocols.never_undefined
#print axioms Program.protocols_never_undefined
#print axioms Program.roles_never_undefined
#print axioms Program.role_never_undefined

-- Expansion, flattening and projection.
#print axioms instantiateRegion_meaning
#print axioms expandRegion_meaning
#print axioms expandProtocols_sound
#print axioms Region.flatten_denote
#print axioms projectRegion_meaning
#print axioms projectProtocol_meaning
#print axioms projectEntry_meaning
#print axioms projectProtocols_sound
#print axioms expansion_agrees_with_calls
#print axioms ReturnTogether.of_done

-- The threading steps.
#print axioms PIR.Process.interpret_bind
#print axioms PIR.Process.interpretWith_bind
#print axioms PIR.Process.interpretWith_stateless
#print axioms PIR.interpretWith_repeatN
#print axioms PIR.interpretWith_iterateN
#print axioms Mapping.apply_extend
#print axioms Renaming.Agrees.operands
#print axioms Renaming.Agrees.extend
#print axioms Renaming.Agrees.to
#print axioms Renaming.Agrees.keepAll
#print axioms Emitted.operation_runs
#print axioms Emitted.andThen_runs
#print axioms Emitted.Silent.andThen
#print axioms at_outside_silent
#print axioms Absorber.emit_outside
#print axioms Deriver.emit_outside
#print axioms at_pure_runs

-- Expansion as an equality of meanings.
#print axioms expandEntry_equal

-- The structural theorem of threading.
#print axioms Functions.table_quiet
#print axioms plainRegion_meaning
#print axioms repeat_threads
#print axioms threadRegion_meaning
#print axioms threadRegions_meaning
#print axioms definition_threads
#print axioms definition_plain
#print axioms serializeRule_sound
#print axioms fiatShamirRule_sound

-- The whole-program theorem of a threading step: a handler that follows the marks fits,
-- the images of the protocols thread, and the image of the entry is the entry under the
-- handler of the marks, between the start and the finish of the rule's entry.
#print axioms ProtocolDefinition.regionSites_nodup
#print axioms Protocols.table_passes
#print axioms region_fits
#print axioms rewriteProtocols_plain
#print axioms rewriteProtocols_threads
#print axioms stepProtocols_rewritten
#print axioms serializeEntry_sound
#print axioms fiatShamirEntry_sound
#print axioms stepProtocols_entry
#print axioms stepProtocols_plain_entry

-- Two steps, one after the other.
#print axioms PIR.Process.interpretWith_interpretWith
#print axioms stepProtocols_twice_entry
#print axioms stepProtocols_plain_then_entry

-- The endpoint lemma: a draw by one part that the other part hears, the listeners of a
-- region whose sites are pairwise different, the listeners of a protocol of a program, the
-- restriction law and the endpoint lemma.
#print axioms Together.draw
#print axioms receiverReplies_hears
#print axioms region_listens_part
#print axioms Protocols.listened
#print axioms Protocols.entry_listened
#print axioms region_together
#print axioms program_together
#print axioms program_endpoints_return

-- Completeness of the scheme that the construction steps derive: completeness for every
-- sampler is the condition that every run returns; the Fiat–Shamir image of an entry
-- returns on every run on which the entry does, and for the prover alone sends what the
-- entry sends; the layout carries the messages of a program that the serialize step
-- accepted; the serialize step replays; and the role programs of the result are a complete
-- scheme.
#print axioms groupedComplete_iff_everyRun
#print axioms fiatShamir_together
#print axioms fiatShamir_sends
#print axioms rewriteProtocols_newest_carries
#print axioms Layout.Lawful.round_trip
#print axioms serialize_entry_replays
#print axioms fiatShamir_serialize_replays
#print axioms SerializedReplaysOn.derivedComplete
#print axioms serialize_complete
#print axioms fiatShamir_serialize_complete
#print axioms serializeProtocols_complete
#print axioms construct_complete

-- The same in the model of the vocabulary, for a declaration that names the rows of the
-- canonical layout: the laws of the layout are derived, and a catalogue suite returns.
#print axioms Vocabulary.canonicalLaws
#print axioms Vocabulary.model_arithmetic_writes
#print axioms Vocabulary.model_scale_writes_of_group
#print axioms Raw.Declaration.suiteReturns_of_rows
#print axioms Vocabulary.serializeProtocols_complete
#print axioms Vocabulary.construct_complete

-- A threading step that the construction item accepts and whose rows are present returns:
-- it refuses no program of well-formed definitions for a missing image or for a residual
-- condition of an image.
#print axioms step_returns_or_internal
#print axioms threadRegion_returns
#print axioms stepProtocols_not_image
#print axioms stepProtocols_returns_or_residual
#print axioms fiatShamirRule_external
#print axioms serializeRule_external
#print axioms threadRegion_passes
#print axioms fiatShamirRule_legal
#print axioms serializeRule_legal
#print axioms stepProtocols_external
#print axioms stepProtocols_returns
#print axioms fiatShamir_returns
#print axioms serializeProtocols_returns
#print axioms construct_returns

-- The model of the vocabulary satisfies the domain laws of a package it admits.
#print axioms Vocabulary.mismatches_of_admitted
#print axioms Vocabulary.model_domainLaws_of_filled
#print axioms Vocabulary.model_domainLaws

-- A legal program is not refused.
#print axioms projectProtocols_never_refuses
#print axioms expandProtocols_limit
#print axioms expandProtocols_deployed
#print axioms choose_states_held
#print axioms unusedSites_spec
#print axioms ProtocolDefinition.sites_nodup

-- The formats: the laws of every combinator and of the formats of numbers.
#print axioms Format.Lawful.prefix_free
#print axioms Format.Lawful.write_injective
#print axioms Format.pair_lawful
#print axioms Format.through_lawful
#print axioms Format.refine_lawful
#print axioms Format.each_lawful
#print axioms Format.repeated_lawful
#print axioms Format.counted_lawful
#print axioms Format.number_lawful
#print axioms Format.below_lawful
#print axioms Format.below_domain
#print axioms Format.natural_lawful
#print axioms le_pow_byteWidth
#print axioms byteWidth_le
#print axioms Format.pair_agrees
#print axioms Format.each_agrees
#print axioms Format.repeated_agrees
#print axioms Format.counted_agrees

-- The canonical layout: the laws of the format of a type, and the rows that are made of it.
#print axioms Vocabulary.decompressPoint_canonical
#print axioms Vocabulary.pointFormat_lawful
#print axioms Vocabulary.formatOf_lawful
#print axioms Vocabulary.formatOf_lawful_of_no_point
#print axioms Vocabulary.formatOf_agrees
#print axioms Vocabulary.putRow_written
#print axioms Vocabulary.takeRow_written
#print axioms Vocabulary.takeRow_canonical
#print axioms Vocabulary.takeRow_within
#print axioms Vocabulary.absorbRow_written
#print axioms Vocabulary.applyRow_within
#print axioms Vocabulary.applyOperation_within
#print axioms Concrete.ofDatum_toDatum
#print axioms Concrete.ofData_toData
#print axioms Vocabulary.model_pure_applied
#print axioms Vocabulary.model_open
#print axioms Vocabulary.model_put
#print axioms Vocabulary.model_close
#print axioms Vocabulary.model_read
#print axioms Vocabulary.model_take
#print axioms Vocabulary.model_exhausted

-- The limit on the work of reading.
#print axioms limitReached_bind
#print axioms Within.bind
#print axioms Within.returned
#print axioms Within.stopped
#print axioms limitedOperation_within
#print axioms limitedRegion_within
#print axioms Functions.limitedTable_within
#print axioms Vocabulary.limitedFunctions_within
#print axioms limitOf?_limitReached
#print axioms limitOf?_other
#print axioms identity_lt_reservedDefinition
#print axioms limitedRoleOperation_within
#print axioms limitedRoleRegion_within
#print axioms RolePrograms.limitedTable_within
#print axioms Vocabulary.limitedRoles_within

-- The executor: its runs end, and they are runs of the relations of the endpoint statements.
#print axioms Execute.oneContinues_wellFounded
#print axioms Execute.move_continues
#print axioms Execute.runAlone_returned
#print axioms Execute.runAlone_stopped
#print axioms Execute.move_performs
#print axioms Execute.run_together
#print axioms ReturnsAlone.of_within
#print axioms Execute.StopsAlone.of_within
#print axioms ReturnTogether.of_within
#print axioms Execute.limitedRoleEntry_within
#print axioms Vocabulary.validInput_bytes
#print axioms Vocabulary.runRole_returned
#print axioms Vocabulary.runRole_stopped
#print axioms Vocabulary.runRoles_together
