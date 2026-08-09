#!/usr/bin/env python3
"""Generate focused ProtocolVocabulary admission fixtures from the seed."""

import argparse
import hashlib
import json
from pathlib import Path


def reverse_objects(value):
    if isinstance(value, dict):
        return {
            key: reverse_objects(value[key])
            for key in reversed(list(value))
        }
    if isinstance(value, list):
        return [reverse_objects(item) for item in value]
    return value


def predicate_spec_digest(body: dict) -> str:
    canonical = json.dumps(
        body, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("ascii")
    return "sha256:" + hashlib.sha256(
        b"zkc/check-predicate-spec\n" + canonical
    ).hexdigest()


def rekey_predicate_spec(vocabulary: dict, old_digest: str) -> str:
    body = vocabulary["predicate_specs"].pop(old_digest)
    new_digest = predicate_spec_digest(body)
    vocabulary["predicate_specs"][new_digest] = body
    for contract in vocabulary["check_contracts"].values():
        predicate = contract.get("predicate", {})
        if predicate.get("content_digest") == old_digest:
            predicate["content_digest"] = new_digest
    return new_digest


def mutate(case: str, vocabulary: dict) -> dict:
    if case == "reordered":
        return reverse_objects(vocabulary)
    if case == "anchor_reordered":
        anchors = vocabulary["claim_profiles"]["opaque_relation"]["anchors"]
        anchors.reverse()
        return vocabulary
    if case == "unknown_top_level":
        vocabulary["unexpected_section"] = {}
    elif case == "unknown_entry_field":
        vocabulary["claim_profiles"]["opaque_relation"]["required"] = True
    elif case == "bad_cross_reference":
        vocabulary["reduction_contracts"]["sumcheck"]["consumes"][0] = "missing_profile"
    elif case == "duplicate_anchor":
        anchors = vocabulary["claim_profiles"]["opaque_relation"]["anchors"]
        anchors.append(anchors[0])
    elif case == "two_outputs":
        # A second output is reachable by authoring alone: nothing in the
        # shipped vocabulary has one, and a derivation site names one output
        # position, so two would offer two sites over the same reduction.
        outputs = vocabulary["reduction_contracts"]["sumcheck"]["outputs"]
        outputs.append(json.loads(json.dumps(outputs[0])))
    elif case == "anchorless_output":
        # The faithfulness gate: a produced claim descriptor must say what it
        # is about.  An anchorless output profile is one constant descriptor
        # in every artifact, which is what let a discrete-log conclusion fuse
        # with a sumcheck source at the link boundary.
        vocabulary["claim_profiles"]["bare_evaluation"] = {
            "kind": "evaluation",
            "anchors": [],
        }
        vocabulary["reduction_contracts"]["sumcheck"]["outputs"] = [
            {"profile": "bare_evaluation", "anchors": {}}
        ]
    elif case == "second_producer":
        # The positive the gate must keep admitting: two contracts producing
        # one anchored profile is ordinary authoring -- a Circom-shaped and a
        # Noir-shaped arithmetizer producing one entry profile is exactly what
        # the relation programme wants.  A later session must not "strengthen"
        # the anchorless ban into a producer-count clause; that clause goes
        # permanently vacuous after the repair and refuses this legitimate
        # shape (docs/spec/vocabularies.md section 3).
        contract = vocabulary["reduction_contracts"]["sigma_dleq"]
        contract["outputs"] = json.loads(json.dumps(
            vocabulary["reduction_contracts"]["sigma"]["outputs"]))
    elif case == "dead_relaxations":
        vocabulary["reduction_contracts"]["sumcheck"]["relaxations"] = [
            "zkc.relax.example"
        ]
    elif case == "duplicate_operand_role":
        operands = vocabulary["check_contracts"]["zkc.check.kzg-opening"]["operands"]
        operands[1]["role"] = operands[0]["role"]
    elif case == "ambiguous_multiplicity":
        operands = vocabulary["check_contracts"]["zkc.check.kzg-batch-opening"]["operands"]
        operands[1]["multiplicity"] = {"capture": "m", "min": 1}
    elif case == "legacy_operand_class":
        vocabulary["check_contracts"]["zkc.check.kzg-opening"]["operands"][
            0
        ]["class"] = "chal"
    elif case == "missing_check_predicate":
        del vocabulary["check_contracts"]["zkc.check.relation-predicate"][
            "predicate"
        ]
    elif case == "unknown_check_predicate_format":
        vocabulary["check_contracts"]["zkc.check.schnorr-equation"][
            "predicate"
        ]["format"] = "zkc-unadmitted-expression"
    elif case == "opaque_with_transparent_predicate":
        vocabulary["check_contracts"]["zkc.check.relation-predicate"][
            "predicate"
        ] = {"format": "zkc-transparent-expression"}
    elif case == "transparent_with_opaque_predicate":
        vocabulary["check_contracts"]["zkc.check.schnorr-equation"][
            "predicate"
        ] = dict(
            vocabulary["check_contracts"]["zkc.check.relation-predicate"][
                "predicate"
            ]
        )
    elif case == "bad_check_predicate_digest":
        vocabulary["check_contracts"]["zkc.check.relation-predicate"][
            "predicate"
        ]["content_digest"] = "sha256:not-a-digest"
    elif case == "bad_check_predicate_entrypoint":
        vocabulary["check_contracts"]["zkc.check.relation-predicate"][
            "predicate"
        ]["entrypoint"] = ""
    elif case == "unknown_check_predicate_field":
        vocabulary["check_contracts"]["zkc.check.schnorr-equation"][
            "predicate"
        ]["content_digest"] = "sha256:" + "0" * 64
    elif case == "missing_predicate_specs_section":
        del vocabulary["predicate_specs"]
    elif case == "random_predicate_spec_digest":
        digest, body = vocabulary["predicate_specs"].popitem()
        vocabulary["predicate_specs"]["sha256:" + "0" * 64] = body
    elif case == "missing_predicate_spec":
        digest = vocabulary["check_contracts"][
            "zkc.check.relation-predicate"
        ]["predicate"]["content_digest"]
        del vocabulary["predicate_specs"][digest]
    elif case == "extra_predicate_spec":
        body = {
            "format": "zkc-check-predicate-spec",
            "title": "Uncited closed predicate",
            "entrypoints": {
                "accept": {
                    "acceptance": ["Accept exactly when true."],
                    "parameters": [],
                    "semantic_parameters": [],
                    "operands": [],
                }
            },
        }
        vocabulary["predicate_specs"][predicate_spec_digest(body)] = body
    elif case == "bad_predicate_spec_entrypoint":
        vocabulary["check_contracts"]["zkc.check.relation-predicate"][
            "predicate"
        ]["entrypoint"] = "missing"
    elif case == "bad_predicate_spec_body":
        digest = vocabulary["check_contracts"][
            "zkc.check.relation-predicate"
        ]["predicate"]["content_digest"]
        del vocabulary["predicate_specs"][digest]["entrypoints"]["accept"][
            "operands"
        ]
    elif case == "empty_rounds":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"] = []
    elif case == "duplicate_acceptance":
        digest = vocabulary["check_contracts"][
            "zkc.check.relation-predicate"
        ]["predicate"]["content_digest"]
        acceptance = vocabulary["predicate_specs"][digest]["entrypoints"][
            "accept"
        ]["acceptance"]
        acceptance.append(acceptance[0])
        rekey_predicate_spec(vocabulary, digest)
    elif case == "non_ascii_title":
        digest = vocabulary["check_contracts"][
            "zkc.check.relation-predicate"
        ]["predicate"]["content_digest"]
        vocabulary["predicate_specs"][digest]["title"] = "café predicate"
        rekey_predicate_spec(vocabulary, digest)
    elif case == "predicate_spec_abi_mismatch":
        digest = vocabulary["check_contracts"]["zkc.check.kzg-opening"][
            "predicate"
        ]["content_digest"]
        vocabulary["predicate_specs"][digest]["entrypoints"]["accept"][
            "operands"
        ][0]["class"] = "tg"
        rekey_predicate_spec(vocabulary, digest)
    elif case == "bad_attachment":
        rule = vocabulary["terminal_rules"]["zkc.terminal.relation-direct"]
        rule["attachments"][0]["role"] = "missing_semantic_parameter"
    elif case == "bad_coverage":
        rule = vocabulary["terminal_rules"]["zkc.terminal.relation-direct"]
        rule["attachments"].pop()
    elif case == "version_key":
        vocabulary["version"] = 0
    elif case == "legacy_schema_section":
        vocabulary["reduction_schemas"] = vocabulary.pop("reduction_contracts")
    elif case == "legacy_dep_kind":
        slot = vocabulary["reduction_contracts"]["sumcheck"]["dep_slots"][0]
        del slot["source"]
        slot["kind"] = "challenge"
    elif case == "legacy_dep_count":
        vocabulary["reduction_contracts"]["sumcheck"]["dep_slots"][0][
            "count"
        ] = 2
    elif case == "bad_dep_source":
        vocabulary["reduction_contracts"]["sumcheck"]["dep_slots"][0][
            "source"
        ] = "challenge"
    elif case == "legacy_dep_class":
        vocabulary["reduction_contracts"]["sumcheck"]["dep_slots"][0][
            "class"
        ] = "chal"
    elif case == "legacy_round_challenge":
        round_ = vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0]
        round_["challenge"] = round_.pop("challenge_use")["role"]
    elif case == "bad_challenge_use_role":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "challenge_use"
        ]["role"] = "missing_dependency"
    elif case == "duplicate_challenge_use":
        rounds = vocabulary["reduction_contracts"]["sumcheck"]["rounds"]
        rounds[1]["challenge_use"]["role"] = rounds[0]["challenge_use"]["role"]
    elif case == "scalar_challenge_use_count":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "challenge_use"
        ]["count"] = 1
    elif case == "zero_challenge_use_count":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "challenge_use"
        ]["count"] = 0
    elif case == "vector_challenge_use_count":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "challenge_use"
        ]["count"] = 2
    elif case == "unpriced_challenge_dependency":
        # Provenance and theorem pricing are deliberately orthogonal.  This
        # response is constrained to a challenge-capability producer, but no
        # round names it as a priced challenge use.
        vocabulary["reduction_contracts"]["sigma_dleq"]["dep_slots"][1][
            "source"
        ] = "challenge_capability"
    elif case == "bad_parameter_sort":
        vocabulary["reduction_contracts"]["sigma_dleq"]["parameters"][
            "left_statement"
        ] = "field_element"
    elif case == "relation_contracts_section":
        vocabulary["relation_contracts"] = {}
    elif case == "overlapping_hole_parameter":
        contract = vocabulary["hole_contracts"]["zkc.hole.sigma-commit"]
        contract["parameters"] = ["shared"]
        contract["semantic_parameters"] = ["shared"]
    elif case == "overlapping_reduction_role":
        vocabulary["reduction_contracts"]["sumcheck"]["parameters"]["c1"] = "atom"
    elif case == "missing_check_parameter":
        vocabulary["reduction_contracts"]["kzg_batch"]["checks"]["opening"][
            "parameters"
        ] = {}
    elif case == "missing_transparent_predicate":
        del vocabulary["reduction_contracts"]["sumcheck"]["checks"]["round1"][
            "transparent_predicate"
        ]
    elif case == "predicate_on_opaque":
        vocabulary["reduction_contracts"]["kzg_batch"]["checks"]["opening"][
            "transparent_predicate"
        ] = ["eq", ["role", "point"], ["role", "point"]]
    elif case == "bad_reduction_attachment":
        source = vocabulary["reduction_contracts"]["sumcheck"]["checks"][
            "round2"
        ]["attachments"][0]["source"]
        source["role"] = "missing_dependency"
    elif case == "bad_output_coverage":
        del vocabulary["reduction_contracts"]["kzg_batch"]["outputs"][0][
            "anchors"
        ]["point"]
    elif case == "bad_output_sort":
        vocabulary["reduction_contracts"]["kzg_batch"]["outputs"][0][
            "anchors"
        ]["point"] = {"kind": "input_descriptors", "order": "operand"}
    elif case == "tautological_constraint":
        constraint = vocabulary["reduction_contracts"]["sigma_dleq"][
            "constraints"
        ][0]
        constraint["right"] = constraint["left"]
    elif case == "duplicate_reversed_constraint":
        constraint = vocabulary["reduction_contracts"]["sigma_dleq"][
            "constraints"
        ][0]
        vocabulary["reduction_contracts"]["sigma_dleq"]["constraints"].append(
            {
                "kind": "equal",
                "left": constraint["right"],
                "right": constraint["left"],
            }
        )
    elif case == "bad_common_target":
        attachments = vocabulary["reduction_contracts"]["kzg_batch"]["checks"][
            "opening"
        ]["attachments"]
        common = next(
            item
            for item in attachments
            if item["kind"] == "common_material_ref_equality"
        )
        attachments[:] = [
            item
            for item in attachments
            if not (
                item["kind"] == "material_ref_vector_equality"
                and item["target_role"] == "commitment"
            )
        ]
        common["target_role"] = "commitment"
    elif case == "scalar_message_count":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "messages"
        ][0]["count"] = 3
    elif case == "malformed_message_count":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "messages"
        ][0]["count"] = {"exact": 3, "same_as": "consumed_claims"}
    elif case == "dynamic_message_nonvariadic":
        vocabulary["reduction_contracts"]["sumcheck"]["rounds"][0][
            "messages"
        ][0]["count"] = {"same_as": "consumed_claims"}
    elif case in {
        "dynamic_message_count",
        "dynamic_message_selector",
        "dynamic_producer_message_selector",
    }:
        batch = vocabulary["reduction_contracts"]["kzg_batch"]
        batch["rounds"][0]["messages"] = [
            {
                "role": "values",
                "count": {"same_as": "consumed_claims"},
            }
        ]
        if case == "dynamic_message_selector":
            batch["checks"]["opening"]["attachments"][0]["source"] = {
                "kind": "message",
                "role": "values",
                "occurrence": 0,
            }
        elif case == "dynamic_producer_message_selector":
            rule = vocabulary["terminal_rules"]["zkc.terminal.kzg-batch-opening"]
            rule["attachments"][-1]["source"] = {
                "kind": "producer_message",
                "role": "values",
                "index": 0,
            }
    else:
        raise ValueError(f"unknown mutation: {case}")
    return vocabulary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("case")
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    source = args.source.read_text()
    if args.case == "duplicate_json_key":
        marker = '  "registry": "zkc.protocol_vocabulary",\n'
        if source.count(marker) != 1:
            raise ValueError("seed has no unique registry field to duplicate")
        args.destination.write_text(source.replace(marker, marker + marker))
        return
    if args.case in {"float_json_number", "nonfinite_json_number"}:
        marker = '  "registry": "zkc.protocol_vocabulary",\n'
        if source.count(marker) != 1:
            raise ValueError("seed has no unique registry field to anchor")
        probe = (
            '  "float_probe": 4.0,\n'
            if args.case == "float_json_number"
            else '  "float_probe": NaN,\n'
        )
        args.destination.write_text(source.replace(marker, marker + probe))
        return
    vocabulary = json.loads(source)
    result = mutate(args.case, vocabulary)
    args.destination.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
