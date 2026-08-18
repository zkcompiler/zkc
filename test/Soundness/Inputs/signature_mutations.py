"""Both implementations must refuse the same broken signatures.

A differential over inputs that are *accepted* is weak here: the canonical
declaration document is close to the file, so two readers can agree on it
while understanding nothing.  A differential over inputs that must be
*refused* is not, because refusing requires knowing what the field meant.

Each case below breaks one thing.  The carrier and the reference are run over
the result and must reach the same verdict.  Diagnostic prose is not compared:
the specification makes ids the contract and leaves message text unstable, and
the reference has no diagnostic ids to offer.

Usage: signature_mutations.py <signature.json> <zkc-registry-lint>
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..",
                                "reference"))

from oracle import wellformed
from oracle.model import Refusal

SUMCHECK = ("rules", "zkc.rbr.sumcheck")
FROM_SS = ("rules", "zkc.rbr.from_ss")
TO_SR = ("rules", "zkc.sr.from_rbr_knowledge")
TO_FS = ("rules", "zkc.fs.duplex_knowledge")
KZG = ("rules", "zkc.pcs.kzg_batch_arsdh")
SIGMA = ("rules", "zkc.ss.sigma")
CHAIN = ("rules", "zkc.rbr.gkr-width2-chain")
BIND_SUMCHECK = ("bindings", "zkc.rbr.sumcheck@reduction:sumcheck")
BIND_FS = ("bindings",
           "zkc.fs.duplex_knowledge@path:sr_to_fs_duplex:knowledge:straightline")

PATH_FIELD = {
    "kind": "sealed_artifact_projection",
    "sort": "integer",
    "artifact_projection": {"kind": "path_binding_field",
                            "result_sort": "integer",
                            "field": "sponge.capacity"},
}


def _string_literal_outside_ascii(document) -> None:
    """The one string position that reaches a digest as a value rather than
    as a name."""
    pin = "zkc.rbr.fri.johnson"
    document["schemas"]["propositions"]["probe.prop"] = {
        "ref": {"id": "probe.prop", "source_revision": "r"},
        "argument_types": ["string"]}
    document["rules"][pin]["external_hypotheses"].append(
        {"slot": "probe_slot", "proposition_ref": "probe.prop",
         "argument_types": ["string"]})
    document["annotations"][pin].setdefault("formalization", [])
    for identifier, binding in document["bindings"].items():
        if binding["rule"] == pin:
            binding["hypothesis_argument_bindings"]["probe_slot"] = [
                {"kind": "literal", "sort": "string",
                 "literal": "cl\u00e9ass"}]


def _at(document, path):
    """The node the path names."""
    node = document
    for key in path:
        node = node[key]
    return node


def _set(document, path, value):
    _at(document, path[:-1])[path[-1]] = value


def _drop(document, path):
    del _at(document, path[:-1])[path[-1]]


# Each entry is (what it breaks, mutation).  The comment on a group says what
# the group is evidence for.
MUTATIONS: list[tuple[str, object]] = [
    # The deferred computational restrictions are pinned, not assumed: an
    # unexercised refusal goes false silently, which is how the interleaving
    # diagnostic did.  A bound reaching resource x primitive advantage is
    # outside the admitted normal form, and no body takes a computational
    # premise -- the sink that keeps every KZG-terminated protocol out of the
    # Fiat-Shamir track under the current admitted rule set
    # (docs/spec/soundness.md section 4.3).
    ("a bound scales a primitive advantage by a resource",
     lambda d: _set(d, [*KZG, "body", "conclusion_failure_bound", "operands", 0],
                    {"kind": "scale",
                     "scale": {"kind": "resource_variable", "name": "tau_arsdh"},
                     "operands": [copy.deepcopy(_at(d, [*KZG, "body",
                                  "conclusion_failure_bound", "operands", 0]))]})),
    ("a premise arrives at a computational index",
     lambda d: _set(d, [*TO_SR, "premises", 0, "expected_index", "notion"],
                    "computational_special_soundness")),

    # The composition body's own law: one premise, at the conclusion's exact
    # index, with round labels a declaration can actually spell.
    ("a chain body loses its premise port",
     lambda d: _set(d, [*CHAIN, "premises"], [])),
    ("a chain premise arrives at another track",
     lambda d: _set(d, [*CHAIN, "premises", 0, "expected_index", "track"],
                    "knowledge")),
    ("an appended round names an unknown label projection",
     lambda d: _set(d, [*CHAIN, "body", "appended_rounds", "cases", 0,
                        "index_projection"], "site_qualified")),
    # A rule the signature offers only as a record must stay unreachable.
    ("a declared rule is still bound",
     lambda d: _set(d, [*SUMCHECK, "status"], "declared")),

    # The body-signature table is stronger than result-schema compatibility.
    ("a state-restoration body reads a Fiat-Shamir premise",
     lambda d: _set(d, [*TO_SR, "premises", 0, "expected_index", "notion"],
                    "fiat_shamir")),
    ("a premise expects a result schema its index does not carry",
     lambda d: _set(d, [*TO_SR, "premises", 0, "expected_result"], "scalar")),
    ("a round-by-round conclusion carries no variant",
     lambda d: _set(d, [*SUMCHECK, "conclusion_index", "variant"], "")),
    ("a Fiat-Shamir conclusion carries no model",
     lambda d: _set(d, [*TO_FS, "conclusion_index", "model"], "")),
    ("the premise a body reads does not exist",
     lambda d: _set(d, [*TO_SR, "body", "round_by_round_port"], "absent")),
    ("round-by-round to state restoration drops a premise constraint",
     lambda d: _set(d, [*TO_SR, "premises", 0, "result_constraints"],
                    ["requires_empty_game_support"])),

    # A quantity may only read a name its enclosing body bound.
    ("a contract-round fact escapes its lexical case",
     lambda d: _set(d, [*SUMCHECK, "body", "rounds", "cases", 0, "bound",
                        "quantity", "operands", 0, "case_name"], "elsewhere")),
    ("a bound coordinate escapes the binder that introduces it",
     lambda d: _set(d, [*FROM_SS, "body", "per_coordinate_bound", "quantity",
                        "operands", 1, "port"], "absent")),
    ("a catch-all case shares the list with another case",
     lambda d: _at(d, [*SUMCHECK, "body", "rounds", "cases"]).append(
         {"bound": {"kind": "quantity",
                    "quantity": {"kind": "rational_literal", "literal": "1"}},
          "case_name": "second",
          "challenge_space": {"kind": "rational_literal", "literal": "2"},
          "index_projection": "round_index",
          "selector": {"kind": "all_contract_rounds"}})),

    # Exact arithmetic has explicit domains; nothing is approximated.
    ("a move budget is statically negative",
     lambda d: _set(d, [*TO_SR, "body", "move_budget"],
                    {"kind": "rational_literal", "literal": "-1"})),
    ("a power has a fractional exponent",
     lambda d: _set(d, [*TO_FS, "body", "local_duplex_bound", "operands", 0,
                        "quantity", "operands", 0, "operands", 1],
                    {"kind": "pow",
                     "operands": [{"kind": "resource_variable", "name": "t"},
                                  {"kind": "rational_literal",
                                   "literal": "1/2"}]})),
    ("a rule declares a non-numeric resource",
     lambda d: _set(d, [*TO_SR, "resources", 0, "sort"], "string")),

    # A protocol fact has one source; a value of the same sort is not it.
    ("a reduction contract is asserted as a literal",
     lambda d: _set(d, [*BIND_SUMCHECK, "fact_bindings", "contract"],
                    {"kind": "literal", "sort": "reduction_contract",
                     "literal": "contract"})),
    ("a path field is read at a reduction occurrence",
     lambda d: _set(d, [*BIND_SUMCHECK, "parameter_bindings", "field_order"],
                    copy.deepcopy(PATH_FIELD))),

    # A binding covers its rule's templates exactly.
    ("a parameter binding is missing",
     lambda d: _drop(d, [*BIND_SUMCHECK, "parameter_bindings", "field_class"])),
    ("a parameter binding is invented",
     lambda d: _set(d, [*BIND_SUMCHECK, "parameter_bindings", "ghost"],
                    {"kind": "resolved_parameter", "reference": "field_order",
                     "sort": "integer"})),
    ("a machine-condition slot is unbound",
     lambda d: _drop(d, [*BIND_SUMCHECK, "condition_argument_bindings", "S3"])),
    ("a hypothesis is bound with the wrong arity",
     lambda d: _at(d, [*BIND_SUMCHECK, "hypothesis_argument_bindings",
                       "S5"]).pop()),
    ("a premise relation is missing",
     lambda d: _drop(d, [*BIND_FS, "premise_relations", "source_sr"])),
    ("a binding names a rule the signature does not declare",
     lambda d: _set(d, [*BIND_SUMCHECK, "rule"], "zkc.absent")),

    # A rule fixes the decider and proposition identities a binding may fill.
    ("a rule restates a decider's argument signature",
     lambda d: _set(d, [*SUMCHECK, "machine_conditions", 1, "argument_types"],
                    ["reduction_contract", "string"])),
    ("a primitive game is instantiated with the wrong arity",
     lambda d: _at(d, [*KZG, "body", "conclusion_failure_bound", "operands", 0,
                       "game", "instance_arguments"]).pop()),
    ("a primitive game's resources are not substituted totally",
     lambda d: _at(d, [*KZG, "body", "conclusion_failure_bound", "operands", 0,
                       "resource_substitution"]).clear()),
    ("an exact parameter pin names no declared parameter",
     lambda d: _set(d, [*KZG, "exact_parameter_pins", 0, "parameter"], "ghost")),

    # The encoding domain admits no float and no non-ASCII string, and a
    # signature is named by its digest: two spellings of one declaration would
    # be two files with one content address.
    ("a round position is outside the encoding domain",
     lambda d: _set(d, [*SUMCHECK, "body", "rounds", "cases", 0, "selector"],
                    {"kind": "round_position", "position": 2 ** 63})),
    ("a case name leaves printable ASCII",
     lambda d: (_set(d, [*SIGMA, "body", "coordinates", "cases", 0,
                         "case_name"], "sigma_r\u00f8und"),
                _set(d, [*SIGMA, "body", "coordinates", "cases", 0,
                         "challenge_space", "case_name"], "sigma_r\u00f8und"))),

    # A contract-derived coordinate resolves against a round that has a
    # challenge space, and a rule that turns coordinates into rounds needs
    # every one of them to carry it.
    ("a contract coordinate case has no challenge space",
     lambda d: _set(d, [*SIGMA, "body", "coordinates", "cases", 0,
                        "challenge_space"], None)),

    # The anchor law reaches every value, including the ones a rule body types
    # without an occurrence in hand.
    ("a reduction-anchored rule reads a path field in a game argument",
     lambda d: _set(d, [*KZG, "body", "conclusion_failure_bound", "operands", 0,
                        "game", "instance_arguments", 1],
                    {"kind": "sealed_artifact_projection", "sort": "integer",
                     "artifact_projection": {"kind": "path_binding_field",
                                             "result_sort": "integer",
                                             "field": "sponge.capacity"}})),

    # A table entry is a declaration in its own right: it becomes reachable
    # the moment a rule cites it, so it is checked whether or not one does.
    ("an unreferenced decider names a kind the binary does not implement",
     lambda d: _set(d, ["schemas", "machine_deciders", "zkc.side.unused"],
                    {"argument_types": ["integer"], "kind": "not_a_kind",
                     "ref": {"id": "zkc.side.unused",
                             "source_revision": "zkc.soundness"}})),
    ("an unreferenced decider is filed under the wrong identity",
     lambda d: _set(d, ["schemas", "machine_deciders", "zkc.side.unused"],
                    {"argument_types": ["integer"], "kind": "batch_arity",
                     "ref": {"id": "zkc.side.unused",
                             "source_revision": "zkc.soundness"}})),
    ("an unreferenced proposition does not carry its own reference",
     lambda d: _set(d, ["schemas", "propositions", "zkc.hyp.unused"],
                    {"argument_types": ["integer"],
                     "ref": {"id": "zkc.hyp.elsewhere",
                             "source_revision": "r"}})),
    ("an unreferenced game declares a non-numeric resource",
     lambda d: _set(d, ["schemas", "primitive_games", "zkc.assume.unused"],
                    {"instance_argument_types": [],
                     "resources": [{"name": "t", "sort": "string"}],
                     "ref": {"id": "zkc.assume.unused",
                             "source_revision": "r"}})),
    ("a protocol-claim subject schema is filed under another identifier",
     lambda d: _set(d, ["schemas", "subject_schemas", "zkc.subject.other"],
                    {"argument_types": [], "kind": "protocol_claim",
                     "ref": "zkc.subject.other"})),
    ("an external-instance subject schema takes no arguments",
     lambda d: _set(d, ["schemas", "subject_schemas",
                        "zkc.subject.external_instance", "argument_types"],
                    [])),
    ("an admitted index carries a variant its notion has no room for",
     lambda d: _at(d, ["schemas", "security_indices"]).append(
         {"model": "", "notion": "special_soundness",
          "quantification": "static", "track": "soundness",
          "variant": "v"})),
    ("an admitted round-by-round index names a model",
     lambda d: _at(d, ["schemas", "security_indices"]).append(
         {"model": "duplex", "notion": "round_by_round",
          "quantification": "static", "track": "soundness",
          "variant": "standard"})),

    # The quantification variable is a rule-pattern device. An admitted
    # index states values; a conclusion's variable restates what a
    # premise bound, so with no premise naming it there is nothing to
    # restate; and a premise pattern some admitted index satisfies is
    # the least a rule needs to ever fire.
    ("an admitted index carries a quantification variable",
     lambda d: _at(d, ["schemas", "security_indices"]).append(
         {"model": "", "notion": "special_soundness",
          "quantification": "$q", "track": "soundness", "variant": ""})),
    ("a conclusion carries an index variable no premise binds",
     lambda d: _set(d, [*SIGMA, "conclusion_index", "quantification"], "$q")),
    ("a premise pattern no admitted index satisfies",
     lambda d: _set(d, [*TO_SR, "premises", 0, "expected_index", "variant"],
                    "nonexistent")),
    ("a premise binds a variable the conclusion does not restate",
     lambda d: _set(d, [*TO_SR, "premises", 0, "expected_index",
                        "quantification"], "$r")),
    ("a premise binds a variable while the conclusion states a value",
     lambda d: _set(d, [*TO_SR, "conclusion_index", "quantification"],
                    "static")),

    # The completeness notion and track come together or not at all: a
    # judgment that prices honest-prover acceptance must not read as a
    # soundness claim, and no soundness notion may borrow the spelling.
    ("a completeness index borrows the soundness track",
     lambda d: _set(d, ["rules", "zkc.completeness.sigma",
                        "conclusion_index", "track"], "soundness")),
    ("a soundness notion borrows the completeness track",
     lambda d: _set(d, [*SUMCHECK, "conclusion_index", "track"],
                    "completeness")),
    ("a completeness body concludes a soundness index",
     lambda d: _set(d, ["rules", "zkc.completeness.sigma",
                        "conclusion_index"],
                    {"model": "", "notion": "round_by_round",
                     "track": "soundness", "variant": "standard"})),

    # A rule whose statement cannot be located is one nobody can check, and a
    # receipt that overstates what it carries is worse than none.
    ("a rule carries no annotation",
     lambda d: _drop(d, ["annotations", "zkc.fs.duplex"])),
    ("a rule names no source anchor",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex", "statement_basis"],
                    [])),
    ("a source anchor names no location inside its source",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex", "statement_basis"],
                    [{"source": "s", "revision": "r", "anchor": ""}])),
    ("a rule that is not admitted does not say why",
     lambda d: _drop(d, ["annotations", "zkc.rbr.fri.capacity",
                         "status_rationale"])),
    ("an annotation names nothing the signature declares",
     lambda d: _set(d, ["annotations", "zkc.nothing.declared"],
                    {"statement": "x"})),
    ("a receipt is recorded as mechanized over a reachable hole",
     lambda d: _set(d, ["annotations", "zkc.rbr.evalopen", "formalization",
                        0, "state"], "mechanized")),
    ("a receipt names an obligation slot its rule does not declare",
     lambda d: _set(d, ["annotations", "zkc.rbr.evalopen", "formalization",
                        0, "unmatched_obligations"], ["NoSuchSlot"])),
    ("a receipt records no admitted-axiom list at all",
     lambda d: _drop(d, ["annotations", "zkc.rbr.evalopen", "formalization",
                         0, "axioms"])),
    ("a receipt records a state the format does not admit",
     lambda d: _set(d, ["annotations", "zkc.rbr.evalopen", "formalization",
                        0, "state"], "believed")),
    ("an admitted index declares a variant that is not a string",
     lambda d: _set(d, ["schemas", "security_indices", 3, "variant"], 5)),
    ("an annotation field that should be prose is a number",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex", "statement"], 5)),
    ("annotation prose leaves printable ASCII",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex", "statement"],
                    "Fiat-Shamir caf\u00e9")),
    ("an annotation carries a field the format does not declare",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex", "unknown"], "x")),

    # An absence record exists to say what was looked for and where the
    # demand is written down; a record that says neither, or something the
    # format does not declare, is not that record.
    ("an absence record carries a field the format does not declare",
     lambda d: _set(d, ["annotations", "zkc.rbr.grinding",
                        "formalization_absence", "found"], "x")),
    ("an absence record does not say what was wanted",
     lambda d: _drop(d, ["annotations", "zkc.rbr.grinding",
                         "formalization_absence", "wanted"])),
    ("an absence record's demand pointer is empty",
     lambda d: _set(d, ["annotations", "zkc.rbr.grinding",
                        "formalization_absence", "demand"], "")),
    ("an absence record is written as a list",
     lambda d: _set(d, ["annotations", "zkc.rbr.grinding",
                        "formalization_absence"], [])),
    ("a rule is silent about its mechanization state",
     lambda d: _drop(d, ["annotations", "zkc.rbr.ordered_rlc",
                         "formalization_absence"])),
    # A present field of the wrong shape must refuse even when an absence
    # record would otherwise satisfy the totality gate: treating prose as an
    # absent list is a lenient read of an authority input.
    ("a receipt list is written as prose beside an absence record",
     lambda d: (_set(d, ["annotations", "zkc.rbr.evalopen",
                         "formalization"], "see notes"),
                _set(d, ["annotations", "zkc.rbr.evalopen",
                         "formalization_absence"],
                     copy.deepcopy(d["annotations"]["zkc.rbr.grinding"]
                                   ["formalization_absence"])))),
    ("an annotation's anchors are written as prose",
     lambda d: _set(d, ["annotations", "zkc.fs.duplex",
                        "statement_basis"], "see notes")),

    # An authority input has one reading. A section written as the wrong
    # shape, a duplicate key, a float, or nesting a recursive reader cannot
    # survive are all ways of having more than one, or none.
    ("the binding section is written as a list",
     lambda d: _set(d, ["bindings"],
                    [d["bindings"][k] for k in sorted(d["bindings"])])),
    ("the binding section is omitted",
     lambda d: _drop(d, ["bindings"])),
    ("the annotation section is omitted",
     lambda d: _drop(d, ["annotations"])),
    ("the annotation section is written as a string",
     lambda d: _set(d, ["annotations"], "none")),
    ("a round position is written as a float",
     lambda d: _set(d, [*SUMCHECK, "body", "rounds", "cases", 0, "selector"],
                    {"kind": "round_position", "position": 3.0})),
    ("an operand index is written as a float",
     lambda d: _set(d, ["bindings", "zkc.rbr.grinding@reduction:grinding",
                        "premise_relations", "source_rbr", "input_indices"],
                    [0.0])),
    ("an operand index leaves the encoding domain",
     lambda d: _set(d, ["bindings", "zkc.rbr.grinding@reduction:grinding",
                        "premise_relations", "source_rbr", "input_indices"],
                    [2 ** 63])),
    ("the version is written as a boolean",
     lambda d: _set(d, ["version"], True)),
    ("the signature declares no rules at all",
     lambda d: (_set(d, ["rules"], {}), _set(d, ["bindings"], {}),
                _set(d, ["annotations"], {}))),
    ("a string literal leaves printable ASCII",
     lambda d: _string_literal_outside_ascii(d)),
    ("an admitted index carries a variant outside printable ASCII",
     lambda d: _set(d, ["schemas", "security_indices", 3, "variant"],
                    "with\ttab")),
    ("a premise coordinate names a coordinate by a free label",
     lambda d: _set(d, [*FROM_SS, "body", "per_coordinate_bound", "quantity",
                        "operands", 1, "selector"],
                    {"kind": "exact_label", "label": "extraction"})),

    # The format is closed at every depth.
    ("a rule carries a field the format does not declare",
     lambda d: _set(d, [*SUMCHECK, "extra"], 1)),
    ("a quantity names a constructor the grammar does not admit",
     lambda d: _set(d, [*TO_SR, "body", "move_budget"],
                    {"kind": "sqrt", "operands": []})),
]


def main() -> int:
    signature_path, lint = sys.argv[1], sys.argv[2]
    base = json.loads(open(signature_path).read())

    disagreements = 0
    with tempfile.TemporaryDirectory() as work:
        probe = os.path.join(work, "signature.json")

        # Positive control. Every case below reads "refused" off a non-zero
        # exit, which a tool that rejects everything satisfies just as well as
        # a tool that rejects the right thing — a renamed flag, a broken
        # loader, or a wrong argument order would leave the whole battery
        # passing. Admitting the unmutated signature first is what makes the
        # non-zero exits mean something.
        with open(probe, "w") as handle:
            json.dump(base, handle)
        control = subprocess.run([lint, probe], capture_output=True, text=True)
        if control.returncode != 0:
            print("the unmutated signature does not admit; every refusal "
                  "below would be vacuous")
            print(control.stderr.strip()[:400])
            return 1
        print("control: the unmutated signature admits")

        for name, mutate in MUTATIONS:
            document = copy.deepcopy(base)
            mutate(document)
            with open(probe, "w") as handle:
                json.dump(document, handle)
            carrier = subprocess.run([lint, probe], capture_output=True,
                                     text=True).returncode != 0
            try:
                wellformed.load(document)
                reference = False
            except Refusal:
                reference = True
            if carrier and reference:
                print(f"both refuse: {name}")
                continue
            disagreements += 1
            print(f"DISAGREE ({'carrier only' if carrier else 'reference only'}"
                  f" refuses): {name}")

    print(f"{len(MUTATIONS) - disagreements}/{len(MUTATIONS)} refused by both")
    return 1 if disagreements else 0


if __name__ == "__main__":
    raise SystemExit(main())
