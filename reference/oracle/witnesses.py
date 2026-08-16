"""Hand-built witnesses for the admitted PIR semantic surface.

Every PIR parity witness below passes the independent reduction and terminal matchers.
Families for which the shipped ProtocolVocabulary has no TerminalRule are not
represented as pretend closed proofs.
"""

from __future__ import annotations

import copy
import hashlib

from .model import (
    REGISTRY,
    Chal,
    Check,
    Discharge,
    ProtocolVocabulary,
    Reduce,
    Slot,
    bind,
    chal,
    check,
    discharge,
    material,
    material_construct,
    load_json,
    reduce_row,
    route,
    slot,
    source,
)


def ref_digest(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("ascii")).hexdigest()


EMPTY_DIGEST = ref_digest("")


TOY_KAPPA = {
    "codecs": {"scalar": "ts_be8", "tg": "tg_be8"},
    "constants": {"g": {"class": "tg", "value": "4"}},
    "iv": "artifact-id",
    "sponge": "toy_duplex",
}

KZG_KAPPA = {
    "codecs": {"fr": "fr_be32", "g1": "bls_g1_be48"},
    "iv": "artifact-id",
    "sponge": "toy_duplex",
}


RELATION_CONTRACT = ref_digest("relation.contract")
RELATION_STATEMENT = ref_digest("relation.statement")

RELATION_DIRECT = {
    "policy": "closed_proof",
    "kappa": {"codecs": {}, "iv": "artifact-id", "sponge": "toy_duplex"},
    "sources": [
        source(
            "relation",
            "opaque_relation",
            {"contract": RELATION_CONTRACT, "statement": RELATION_STATEMENT},
        )
    ],
    "events": [
        check(
            "predicate",
            "zkc.check.relation-predicate",
            semantic_args={
                "contract": RELATION_CONTRACT,
                "statement": RELATION_STATEMENT,
            },
        )
    ],
    "reduces": [],
    "material_bindings": [],
    "sinks": [
        discharge(
            "relation",
            "zkc.terminal.relation-direct",
            {"predicate": "predicate"},
        )
    ],
}


SCHNORR_STATEMENT = ref_digest("stmt.dlog")
SCHNORR = {
    "policy": "closed_proof",
    "kappa": TOY_KAPPA,
    "sources": [
        source(
            "dlog",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": SCHNORR_STATEMENT},
        )
    ],
    "events": [
        bind("y", "tg", "instance"),
        slot("commit_A", "tg", True, ("sig", "a", 0)),
        chal(
            "c",
            "scalar",
            "schnorr.c",
            "2305843009213693952",
            ["y", "commit_A"],
        ),
        slot("resp_z", "scalar", True),
        check(
            "verify",
            "zkc.check.schnorr-equation",
            ["y", "commit_A", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
    ],
    "reduces": [
        reduce_row(
            "sig",
            "sigma",
            ["dlog"],
            ["c"],
            [("evaluation", "schnorr_evaluation")],
            checks={"equation": "verify"},
            anchors=[{"statement": SCHNORR_STATEMENT}],
        )
    ],
    "material_bindings": [material("y", SCHNORR_STATEMENT)],
    "sinks": [
        discharge(
            "evaluation",
            "zkc.terminal.schnorr-evaluation",
            {"equation": "verify"},
        )
    ],
}



# Two independent sigma reductions, both ready at once. This is the only
# witness where the reduce normalization has a tie to break — every other
# corpus entry has at most one reduce ready at a time, so the ready-set order
# and its eight-field key were fixed by both implementations agreeing and by
# nothing else. `test/Encoding/normalization.mlir` is the carrier side.
NORMALIZATION_LEFT_CONTRACT = (
    "sha256:f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114"
)
NORMALIZATION_LEFT_STATEMENT = (
    "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"
)
NORMALIZATION_RIGHT_CONTRACT = (
    "sha256:7dc96f776c8423e57a2785489a3f9c43fb6e756876d6ad9a9cac4aa4e72ec193"
)
NORMALIZATION_RIGHT_STATEMENT = (
    "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"
)

TWO_READY_REDUCES = {
    "policy": "analysis_only_artifact",
    "kappa": TOY_KAPPA,
    "sources": [
        source("left", "opaque_relation",
               {"contract": NORMALIZATION_LEFT_CONTRACT,
                "statement": NORMALIZATION_LEFT_STATEMENT}),
        source("right", "opaque_relation",
               {"contract": NORMALIZATION_RIGHT_CONTRACT,
                "statement": NORMALIZATION_RIGHT_STATEMENT}),
    ],
    "events": [
        bind("ya", "tg", "instance"),
        bind("yb", "tg", "instance"),
        slot("ma", "tg", True, ("ra", "a", 0)),
        chal("ca", "scalar", "a.c", "2305843009213693952", ["ya", "ma"]),
        slot("za", "scalar", True),
        slot("mb", "tg", True, ("rb", "a", 0)),
        chal("cb", "scalar", "b.c", "2305843009213693952", ["yb", "mb"]),
        slot("zb", "scalar", True),
        check("verify_a", "zkc.check.schnorr-equation",
              ["ya", "ma", "ca", "za"],
              expr=["eq", ["g_exp", ["const", "g"], ["in", 3]],
                    ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]),
        check("verify_b", "zkc.check.schnorr-equation",
              ["yb", "mb", "cb", "zb"],
              expr=["eq", ["g_exp", ["const", "g"], ["in", 3]],
                    ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]),
    ],
    "reduces": [
        reduce_row("ra", "sigma", ["left"], ["ca"],
                   [("ea", "schnorr_evaluation")],
                   checks={"equation": "verify_a"},
                   anchors=[{"statement": NORMALIZATION_LEFT_STATEMENT}]),
        reduce_row("rb", "sigma", ["right"], ["cb"],
                   [("eb", "schnorr_evaluation")],
                   checks={"equation": "verify_b"},
                   anchors=[{"statement": NORMALIZATION_RIGHT_STATEMENT}]),
    ],
    "material_bindings": [material("ya", NORMALIZATION_LEFT_STATEMENT),
                          material("yb", NORMALIZATION_RIGHT_STATEMENT)],
    "sinks": [route("residual", "ea", "normalization.probe"),
              route("residual", "eb", "normalization.probe")],
}

# These witnesses deliberately preserve useful verifier-spine semantics while
# ending in an explicit analysis residual.  Their checks are admitted data,
# but the v0 vocabulary contains no TerminalRule that would justify calling
# the resulting protocol claim closed.

SUMCHECK = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {"scalar": "ts_be8"},
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [
        source(
            "sum",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": ref_digest("stmt.sum")},
        )
    ],
    "events": [
        bind("s", "scalar", "instance"),
        slot("g1_0", "scalar", True, ("sc", "g1", 0)),
        slot("g1_1", "scalar", True, ("sc", "g1", 1)),
        slot("g1_2", "scalar", True, ("sc", "g1", 2)),
        check(
            "round1",
            "zkc.check.sumcheck-round1",
            ["s", "g1_0", "g1_1", "g1_2"],
            expr=[
                "eq",
                [
                    "f_add",
                    ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]],
                    ["in", 3],
                ],
                ["in", 0],
            ],
        ),
        chal("c1", "scalar", "sumcheck.c1", "2305843009213693952"),
        slot("g2_0", "scalar", True, ("sc", "g2", 0)),
        slot("g2_1", "scalar", True, ("sc", "g2", 1)),
        slot("g2_2", "scalar", True, ("sc", "g2", 2)),
        check(
            "round2",
            "zkc.check.sumcheck-round2",
            ["g1_0", "g1_1", "g1_2", "c1", "g2_0", "g2_1", "g2_2"],
            expr=[
                "eq",
                [
                    "f_add",
                    ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]],
                    ["in", 6],
                ],
                [
                    "f_add",
                    ["in", 0],
                    [
                        "f_add",
                        ["f_mul", ["in", 1], ["in", 3]],
                        [
                            "f_mul",
                            ["in", 2],
                            ["f_mul", ["in", 3], ["in", 3]],
                        ],
                    ],
                ],
            ],
        ),
        chal("c2", "scalar", "sumcheck.c2", "2305843009213693952"),
        check(
            "final",
            "zkc.check.sumcheck-final",
            ["g2_0", "g2_1", "g2_2", "c1", "c2"],
            expr=[
                "eq",
                [
                    "f_add",
                    ["in", 0],
                    [
                        "f_add",
                        ["f_mul", ["in", 1], ["in", 4]],
                        [
                            "f_mul",
                            ["in", 2],
                            ["f_mul", ["in", 4], ["in", 4]],
                        ],
                    ],
                ],
                ["f_add", ["f_mul", ["in", 3], ["in", 4]], ["in", 3]],
            ],
        ),
    ],
    "reduces": [
        reduce_row(
            "sc",
            "sumcheck",
            ["sum"],
            ["c1", "c2"],
            [("evaluation", "sumcheck_evaluation")],
            anchors=[{"statement": ref_digest("stmt.sum")}],
            checks={
                "final": "final",
                "round1": "round1",
                "round2": "round2",
            },
        )
    ],
    "material_bindings": [material("s", ref_digest("stmt.sum"))],
    "sinks": [
        route("residual", "evaluation", "sumcheck-terminal-not-modeled")
    ],
}

SUMCHECK_FS = {
    **SUMCHECK,
}


CP_H = "2077728439817762110"
DLEQ_LEFT_STATEMENT = ref_digest("stmt.dleq.y1")
DLEQ_RIGHT_STATEMENT = ref_digest("stmt.dleq.y2")
DLEQ_STATEMENT = material_construct(
    "zkc.statement.dleq",
    [["ref", DLEQ_LEFT_STATEMENT], ["ref", DLEQ_RIGHT_STATEMENT]],
)
CHAUM_PEDERSEN = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {"scalar": "ts_be8", "tg": "tg_be8"},
        "constants": {
            "g": {"class": "tg", "value": "4"},
            "h": {"class": "tg", "value": CP_H},
        },
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [
        source(
            "dleq",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": DLEQ_STATEMENT},
        )
    ],
    "events": [
        bind("y1", "tg", "instance"),
        bind("y2", "tg", "instance"),
        slot("commit_A1", "tg", True, ("cp", "a", 0)),
        slot("commit_A2", "tg", True, ("cp", "a", 1)),
        chal(
            "c",
            "scalar",
            "cp.c",
            "2305843009213693952",
            ["y1", "y2", "commit_A1", "commit_A2"],
        ),
        slot("resp_z", "scalar", True),
        check(
            "verify1",
            "zkc.check.schnorr-equation",
            ["y1", "commit_A1", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
        check(
            "verify2",
            "zkc.check.schnorr-equation",
            ["y2", "commit_A2", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "h"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
    ],
    "reduces": [
        reduce_row(
            "cp",
            "sigma_dleq",
            ["dleq"],
            ["c", "resp_z"],
            [("evaluation", "dleq_evaluation")],
            anchors=[{"statement": DLEQ_STATEMENT}],
            checks={
                "left_equation": "verify1",
                "right_equation": "verify2",
            },
            params={
                "left_statement": DLEQ_LEFT_STATEMENT,
                "right_statement": DLEQ_RIGHT_STATEMENT,
            },
        )
    ],
    "material_bindings": [
        material("y1", DLEQ_LEFT_STATEMENT),
        material("y2", DLEQ_RIGHT_STATEMENT),
    ],
    "sinks": [route("residual", "evaluation", "dleq-terminal-not-modeled")],
}


OR_LEFT_STATEMENT = ref_digest("stmt.or.y1")
OR_RIGHT_STATEMENT = ref_digest("stmt.or.y2")
OR_STATEMENT = material_construct(
    "zkc.statement.or",
    [["ref", OR_LEFT_STATEMENT], ["ref", OR_RIGHT_STATEMENT]],
)
OR_SIGMA = {
    "policy": "analysis_only_artifact",
    "kappa": TOY_KAPPA,
    "sources": [
        source(
            "ordlog",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": OR_STATEMENT},
        )
    ],
    "events": [
        bind("y1", "tg", "instance"),
        bind("y2", "tg", "instance"),
        slot("commit_A1", "tg", True, ("or", "a", 0)),
        slot("commit_A2", "tg", True, ("or", "a", 1)),
        chal(
            "c",
            "scalar",
            "or.c",
            "2305843009213693952",
            ["y1", "y2", "commit_A1", "commit_A2"],
        ),
        slot("share_c1", "scalar", True),
        slot("share_c2", "scalar", True),
        slot("resp_z1", "scalar", True),
        slot("resp_z2", "scalar", True),
        check(
            "verify1",
            "zkc.check.sigma-equation-scalar-challenge",
            ["y1", "commit_A1", "share_c1", "resp_z1"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
        check(
            "verify2",
            "zkc.check.sigma-equation-scalar-challenge",
            ["y2", "commit_A2", "share_c2", "resp_z2"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
        check(
            "split",
            "zkc.check.scalar-split",
            ["share_c1", "share_c2", "c"],
            expr=["eq", ["f_add", ["in", 0], ["in", 1]], ["in", 2]],
        ),
    ],
    "reduces": [
        reduce_row(
            "or",
            "sigma_or",
            ["ordlog"],
            ["c", "share_c1", "share_c2"],
            [("evaluation", "or_evaluation")],
            anchors=[{"statement": OR_STATEMENT}],
            checks={
                "challenge_split": "split",
                "left_equation": "verify1",
                "right_equation": "verify2",
            },
            params={
                "left_statement": OR_LEFT_STATEMENT,
                "right_statement": OR_RIGHT_STATEMENT,
            },
        )
    ],
    "material_bindings": [
        material("y1", OR_LEFT_STATEMENT),
        material("y2", OR_RIGHT_STATEMENT),
    ],
    "sinks": [route("residual", "evaluation", "or-terminal-not-modeled")],
}


VECCHAL = {
    "policy": "analysis_only_artifact",
    "kappa": TOY_KAPPA,
    "sources": [
        source(
            "dlog",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": SCHNORR_STATEMENT},
        )
    ],
    "events": [
        bind("y", "tg", "instance"),
        slot("commit_A", "tg", True),
        chal(
            "q",
            "scalar",
            "vec.q",
            "1099511627776",
            ["y", "commit_A"],
            mode=["vector", "16", "uniform_independent"],
        ),
        # A count-16 value fills sixteen units of a check operand
        # segment, never a scalar one, so the schnorr equation consumes
        # its own scalar challenge. The counted unabsorbed slot is the
        # read_vec/slot_vec families' parity gate: response material
        # read after the last challenge.
        chal("c", "scalar", "vec.c", "1099511627776", ["y", "commit_A"]),
        slot("resp_z", "scalar", True),
        check(
            "verify",
            "zkc.check.schnorr-equation",
            ["y", "commit_A", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
        slot("resp_vec", "scalar", False, count="16"),
    ],
    "reduces": [],
    "material_bindings": [],
    "sinks": [route("residual", "dlog", "vector-challenge-analysis")],
}


BLS12_381_FR = (
    "52435875175126190479447740508185965837690552500527637822603658699938581184513"
)
KZG_SUITE = "bls12-381"
KZG_C1 = ref_digest("kzg.C1")
KZG_C2 = ref_digest("kzg.C2")
KZG_Z = ref_digest("kzg.z")
KZG_V1 = ref_digest("kzg.v1")
KZG_V2 = ref_digest("kzg.v2")

_KZG_SOURCES = [
    source(
        "open1",
        "single_opening",
        {"commitment": KZG_C1, "point": KZG_Z, "value": KZG_V1},
    ),
    source(
        "open2",
        "single_opening",
        {"commitment": KZG_C2, "point": KZG_Z, "value": KZG_V2},
    ),
]

_KZG_EVENTS = [
    bind("C1", "g1", "instance"),
    bind("C2", "g1", "instance"),
    bind("z", "fr", "instance"),
    bind("v1", "fr", "instance"),
    bind("v2", "fr", "instance"),
]

_KZG_MATERIAL = [
    material("C1", KZG_C1),
    material("C2", KZG_C2),
    material("z", KZG_Z),
    material("v1", KZG_V1),
    material("v2", KZG_V2),
]

KZG_SINGLE = {
    "policy": "closed_proof",
    "kappa": KZG_KAPPA,
    "sources": _KZG_SOURCES,
    "events": _KZG_EVENTS
    + [
        slot("W1", "g1", True),
        slot("W2", "g1", True),
        check(
            "open1_ok",
            "zkc.check.kzg-opening",
            ["C1", "z", "v1", "W1"],
            params={"suite": KZG_SUITE},
        ),
        check(
            "open2_ok",
            "zkc.check.kzg-opening",
            ["C2", "z", "v2", "W2"],
            params={"suite": KZG_SUITE},
        ),
    ],
    "reduces": [],
    "material_bindings": _KZG_MATERIAL,
    "sinks": [
        discharge(
            "open1",
            "zkc.terminal.kzg-opening",
            {"opening": "open1_ok"},
        ),
        discharge(
            "open2",
            "zkc.terminal.kzg-opening",
            {"opening": "open2_ok"},
        ),
    ],
}


def _canonical_opening_sources():
    return sorted(
        _KZG_SOURCES,
        key=lambda entry: __import__("json").dumps(
            [entry.profile, entry.anchors],
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ),
    )


_ORDERED_OPENINGS = _canonical_opening_sources()
_OPENING_VALUES = {
    "open1": ("C1", "v1"),
    "open2": ("C2", "v2"),
}
_BATCH_MEMBERS = material_construct(
    "zkc.opening-batch.members",
    [
        [
            "claims",
            [[entry.profile, entry.anchors] for entry in _ORDERED_OPENINGS],
        ]
    ],
)
_BATCH_TAG = _BATCH_MEMBERS.removeprefix("sha256:")[:16]

KZG_BATCH = {
    "policy": "closed_proof",
    "kappa": KZG_KAPPA,
    "sources": _KZG_SOURCES,
    "events": _KZG_EVENTS
    + [
        chal(
            "gamma",
            "fr",
            "batch_open." + _BATCH_TAG,
            BLS12_381_FR,
            ["C1", "C2", "z", "v1", "v2"],
        ),
        slot("W", "g1", True),
        check(
            "batch_ok",
            "zkc.check.kzg-batch-opening",
            [
                *[_OPENING_VALUES[entry.label][0] for entry in _ORDERED_OPENINGS],
                "z",
                *[_OPENING_VALUES[entry.label][1] for entry in _ORDERED_OPENINGS],
                "gamma",
                "W",
            ],
            params={"suite": KZG_SUITE},
        ),
    ],
    "reduces": [
        reduce_row(
            "batch",
            "kzg_batch",
            [entry.label for entry in _ORDERED_OPENINGS],
            ["gamma"],
            [("batch_opening", "batch_opening")],
            checks={"opening": "batch_ok"},
            anchors=[{"members": _BATCH_MEMBERS, "point": KZG_Z}],
        )
    ],
    "material_bindings": _KZG_MATERIAL,
    "sinks": [
        discharge(
            "batch_opening",
            "zkc.terminal.kzg-batch-opening",
            {"opening": "batch_ok"},
        )
    ],
}

# Generic, check-free ordered-RLC witnesses.  These mirror the semantic
# objects used by the source-mapped evidence fixtures without importing either
# upstream implementation into the oracle.  The reduction contract establishes
# transcript ordering and exact material correspondence; its theorem row prices
# only the local Schwartz--Zippel loss.  Downstream PCS judgments remain
# explicit residuals.
OPENING_VALUE_0 = "sha256:aeb2f59852dc774ec0bc96bbd26b2391759b9d3c59dbe350d283761513a8f53c"
OPENING_VALUE_1 = "sha256:b68a862a777bf0eb557d81bfc632a0e8c0cd18e63fb11ea0ad2f267759295bf2"
OPENING_VALUE_2 = "sha256:4cc19f4e3fb1e65c57904336df94478cbc73d6972f35bca180f495cc2c9e9ba9"
OPENING_RLC_COEFFICIENT = (
    "sha256:4429298bf4f75eadcda459d9d83cb5ea1e18cfed4f244abb4238d2c1565edd2b"
)
OPENING_RLC_MEMBERS = (
    "sha256:b2e2a88c5b0544c5d433de525b4cf65da01c2fc0b41b1d27962bd65d2a21834f"
)

OPENING_VALUE_RLC = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {
            "ext_field": "plonky3_bb31_ext4_tuple",
            "fr": "fr_be32",
        },
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [
        source(
            "open0",
            "single_opening",
            {
                "commitment": "sha256:f1f26eb6b69f225749921b8d0aba4a1b2f1a7dcbeb5b094888a80fc8758f1449",
                "point": "sha256:bb841dc4d43823795fe62eaa30c910cc3ea3c54b1afac2d91d7d7f44adb98bbf",
                "value": OPENING_VALUE_0,
            },
        ),
        source(
            "open1",
            "single_opening",
            {
                "commitment": "sha256:fa248e84204d634e1fcf3ba0bdb0abbf252cc19a4c30a5ecfa27a0042a655065",
                "point": "sha256:7aefa2d4a3ee7e2d1696cddf7f2532e01a5cc973ec766128ef183fea9b5ee34b",
                "value": OPENING_VALUE_1,
            },
        ),
        source(
            "open2",
            "single_opening",
            {
                "commitment": "sha256:8f5a18a2fce3bf9b8773cfae20e4d437505b6763a0800b78ca272a0cafadeb9a",
                "point": "sha256:2bd989aa5bbe41505c3df8448dd7304c17d33d9ec2873a308c40eafae232a73b",
                "value": OPENING_VALUE_2,
            },
        ),
    ],
    "events": [
        slot("value0", "ext_field", True, ("opening_rlc", "values", 0)),
        slot("value1", "ext_field", True, ("opening_rlc", "values", 1)),
        slot("value2", "ext_field", True, ("opening_rlc", "values", 2)),
        chal(
            "alpha",
            "ext_field",
            "sp1.opening-value-rlc.alpha",
            "16428751811598850197311699254593454081",
            ["value0", "value1", "value2"],
        ),
    ],
    "reduces": [
        reduce_row(
            "opening_rlc",
            "opening_value_rlc",
            ["open0", "open1", "open2"],
            ["alpha"],
            [("combined", "opening_value_rlc")],
            anchors=[
                {
                    "coefficient": OPENING_RLC_COEFFICIENT,
                    "members": OPENING_RLC_MEMBERS,
                }
            ],
        )
    ],
    "material_bindings": [
        material("value0", OPENING_VALUE_0),
        material("value1", OPENING_VALUE_1),
        material("value2", OPENING_VALUE_2),
        material("alpha", OPENING_RLC_COEFFICIENT),
    ],
    "sinks": [
        route("residual", "combined", "plonky3-fri-pcs-not-evaluated")
    ],
}


KZG_EQUATION_0 = "sha256:45a164347a1fdb1b2c0d42be4a93210f73b7c680a493b9cb27673515f6a1f50e"
KZG_EQUATION_1 = "sha256:319abfe29a80e14f52a92fcf12d02bc138667a9753c93e81d78daef009f45158"
KZG_EQUATION_RLC_COEFFICIENT = (
    "sha256:a06ad058694b50c2db9aa05bd248fe73db07687040e1b383907d4d94625c5ba2"
)
KZG_EQUATION_RLC_MEMBERS = (
    "sha256:5fdbc8f10d18e5944a92ca4588696bcfff08e75e0af64e28f6fe2d1b99cc5abf"
)

KZG_EQUATION_RLC = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {"equation": "fr_be32", "fr": "fr_be32"},
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [
        source(
            "equation0",
            "kzg_verification_equation",
            {"material": KZG_EQUATION_0},
        ),
        source(
            "equation1",
            "kzg_verification_equation",
            {"material": KZG_EQUATION_1},
        ),
    ],
    "events": [
        slot("equation0_material", "equation", True, ("equation_rlc", "equations", 0)),
        slot("equation1_material", "equation", True, ("equation_rlc", "equations", 1)),
        chal(
            "u",
            "fr",
            "linea.kzg-equation-rlc.u",
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            ["equation0_material", "equation1_material"],
        ),
    ],
    "reduces": [
        reduce_row(
            "equation_rlc",
            "kzg_equation_rlc",
            ["equation0", "equation1"],
            ["u"],
            [("combined", "kzg_equation_rlc")],
            anchors=[
                {
                    "coefficient": KZG_EQUATION_RLC_COEFFICIENT,
                    "members": KZG_EQUATION_RLC_MEMBERS,
                }
            ],
        )
    ],
    "material_bindings": [
        material("equation0_material", KZG_EQUATION_0),
        material("equation1_material", KZG_EQUATION_1),
        material("u", KZG_EQUATION_RLC_COEFFICIENT),
    ],
    "sinks": [
        route("residual", "combined", "kzg-equation-verification-not-evaluated")
    ],
}


def _challenge_first(protocol: dict, challenge_label: str) -> dict:
    """Construct the exact late-message negative used by the source twins."""

    result = copy.deepcopy(protocol)
    challenge_index = next(
        index
        for index, event in enumerate(result["events"])
        if isinstance(event, Chal) and event.label == challenge_label
    )
    challenge = result["events"].pop(challenge_index)._replace(deps=[])
    result["events"].insert(0, challenge)
    return result


OPENING_VALUE_RLC_VULNERABLE = _challenge_first(OPENING_VALUE_RLC, "alpha")
KZG_EQUATION_RLC_VULNERABLE = _challenge_first(KZG_EQUATION_RLC, "u")


# Fixed-width GKR stress witness.  This is intentionally generated from the
# protocol-level recurrence rather than copied from C++ canonical output: the
# independent model reconstructs all three local reductions, the nested oracle
# chain, and the final public-input discharge from authored semantic objects.
GKR_WIDTH2_FIELD = "2305843009213693951"
GKR_WIDTH2_INPUT_ORACLE = (
    "sha256:1fe543b3845ed3f7f475b6bf6cba1140d4444a5ab38d26d721889ab58fb41810"
)
GKR_WIDTH2_LAYER2_ORACLE = material_construct(
    "zkc.gkr.width2-addmul-layer-oracle",
    [["ref", GKR_WIDTH2_INPUT_ORACLE]],
)
GKR_WIDTH2_LAYER1_ORACLE = material_construct(
    "zkc.gkr.width2-addmul-layer-oracle",
    [["ref", GKR_WIDTH2_LAYER2_ORACLE]],
)
GKR_WIDTH2_ROOT_ORACLE = material_construct(
    "zkc.gkr.width2-addmul-layer-oracle",
    [["ref", GKR_WIDTH2_LAYER1_ORACLE]],
)

GKR_WIDTH2_POINTS = [
    "sha256:42b2b9246fd828c1512fe789ea645fb0ed2af780117574cf3bd3685633f509e7",
    "sha256:a06b870b513764aa38f7c299ab407a16b9cb25de3d077746b52b2178c7235a06",
    "sha256:f36af60d2c804b93542d4b3a965e7431c31b27bc09474a17d2016916d009549c",
    "sha256:3718687b5a6e049be4d07858abbca68ad5ab5487adc6b36c0806c9bede4c9ce9",
]
GKR_WIDTH2_VALUES = [
    "sha256:b803d6105862f82ba72107d14aea25fb684db905080323c09ab3019f255c1a24",
    "sha256:251db8954e587580b1d1db7da3108ad477bfdeef3ced5b2c1156ffef51604dee",
    "sha256:4b6937cbec332fd94b6a58484db86620aafc5332c11b0d92d1ceda91f579cc2f",
    "sha256:164eaba18d8aef08003e37b422f37150c80d1b587013d90a8f2dda112d4d0380",
]
GKR_WIDTH2_ORACLES = [
    GKR_WIDTH2_ROOT_ORACLE,
    GKR_WIDTH2_LAYER1_ORACLE,
    GKR_WIDTH2_LAYER2_ORACLE,
    GKR_WIDTH2_INPUT_ORACLE,
]


def _gkr_round1_expr() -> list:
    return [
        "eq",
        [
            "f_add",
            ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]],
            ["in", 3],
        ],
        ["in", 0],
    ]


def _gkr_round2_expr() -> list:
    return [
        "eq",
        [
            "f_add",
            ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]],
            ["in", 6],
        ],
        [
            "f_add",
            ["in", 0],
            [
                "f_add",
                ["f_mul", ["in", 1], ["in", 3]],
                [
                    "f_mul",
                    ["in", 2],
                    ["f_mul", ["in", 3], ["in", 3]],
                ],
            ],
        ],
    ]


def _gkr_endpoint_expr() -> list:
    return [
        "eq",
        [
            "f_add",
            ["in", 0],
            [
                "f_add",
                ["f_mul", ["in", 1], ["in", 4]],
                [
                    "f_mul",
                    ["in", 2],
                    ["f_mul", ["in", 4], ["in", 4]],
                ],
            ],
        ],
        [
            "f_mul",
            [
                "f_mul",
                [
                    "f_add",
                    ["const", "one"],
                    ["f_neg", ["in", 3]],
                ],
                ["in", 4],
            ],
            [
                "f_add",
                [
                    "f_mul",
                    [
                        "f_add",
                        ["const", "one"],
                        ["f_neg", ["in", 5]],
                    ],
                    ["f_add", ["in", 6], ["in", 7]],
                ],
                [
                    "f_mul",
                    ["in", 5],
                    ["f_mul", ["in", 6], ["in", 7]],
                ],
            ],
        ],
    ]


def _gkr_fold_expr() -> list:
    return [
        "eq",
        ["in", 3],
        [
            "f_add",
            ["in", 0],
            [
                "f_mul",
                ["in", 2],
                ["f_add", ["in", 1], ["f_neg", ["in", 0]]],
            ],
        ],
    ]


def _gkr_width2_layer_events(
    layer: int, parent_point: str, parent_value: str, next_point: str, next_value: str
) -> list:
    prefix = f"l{layer}"
    instance = f"layer{layer}"
    rho = f"{prefix}_rho"
    sigma = f"{prefix}_sigma"
    tau = f"{prefix}_tau"
    first = [f"{prefix}_a{index}" for index in range(3)]
    second = [f"{prefix}_b{index}" for index in range(3)]
    children = [f"{prefix}_left", f"{prefix}_right"]
    return [
        *[
            slot(label, "scalar", True, (instance, "first_poly", index))
            for index, label in enumerate(first)
        ],
        chal(rho, "scalar", f"gkr.layer{layer}.rho", GKR_WIDTH2_FIELD),
        *[
            slot(label, "scalar", True, (instance, "second_poly", index))
            for index, label in enumerate(second)
        ],
        chal(sigma, "scalar", f"gkr.layer{layer}.sigma", GKR_WIDTH2_FIELD),
        *[
            slot(label, "scalar", True, (instance, "child_values", index))
            for index, label in enumerate(children)
        ],
        chal(tau, "scalar", f"gkr.layer{layer}.tau", GKR_WIDTH2_FIELD),
        slot(next_point, "scalar", True),
        slot(next_value, "scalar", True),
        check(
            f"{prefix}_round1",
            "zkc.check.sumcheck-round1",
            [parent_value, *first],
            expr=_gkr_round1_expr(),
        ),
        check(
            f"{prefix}_round2",
            "zkc.check.sumcheck-round2",
            [*first, rho, *second],
            expr=_gkr_round2_expr(),
        ),
        check(
            f"{prefix}_endpoint",
            "zkc.check.gkr-width2-addmul-endpoint",
            [*second, rho, sigma, parent_point, *children],
            expr=_gkr_endpoint_expr(),
        ),
        check(
            f"{prefix}_point_fold",
            "zkc.check.affine-fold-challenge-points",
            [rho, sigma, tau, next_point],
            expr=_gkr_fold_expr(),
        ),
        check(
            f"{prefix}_value_fold",
            "zkc.check.affine-fold-scalars",
            [*children, tau, next_value],
            expr=_gkr_fold_expr(),
        ),
    ]


def _gkr_width2_reduce(
    layer: int, consumed: str, produced: str
) -> Reduce:
    prefix = f"l{layer}"
    return reduce_row(
        f"layer{layer}",
        "gkr_width2_addmul_layer",
        [consumed],
        [
            f"{prefix}_rho",
            f"{prefix}_sigma",
            f"{prefix}_tau",
            "input_point" if layer == 2 else f"l{layer + 1}_point",
            "input_value" if layer == 2 else f"l{layer + 1}_value",
        ],
        [(produced, "mle_evaluation")],
        checks={
            "endpoint": f"{prefix}_endpoint",
            "point_fold": f"{prefix}_point_fold",
            "round1": f"{prefix}_round1",
            "round2": f"{prefix}_round2",
            "value_fold": f"{prefix}_value_fold",
        },
        params={"child_oracle": GKR_WIDTH2_ORACLES[layer + 1]},
        anchors=[
            {
                "oracle": GKR_WIDTH2_ORACLES[layer + 1],
                "point": GKR_WIDTH2_POINTS[layer + 1],
                "value": GKR_WIDTH2_VALUES[layer + 1],
            }
        ],
    )


GKR_WIDTH2_DEPTH3 = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {"scalar": "ts_be8"},
        "constants": {"one": {"class": "scalar", "value": "1"}},
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [
        source(
            "root",
            "mle_evaluation",
            {
                "oracle": GKR_WIDTH2_ROOT_ORACLE,
                "point": GKR_WIDTH2_POINTS[0],
                "value": GKR_WIDTH2_VALUES[0],
            },
        )
    ],
    "events": [
        bind("root_point", "scalar", "instance"),
        bind("root_value", "scalar", "instance"),
        bind("input0", "scalar", "instance"),
        bind("input1", "scalar", "instance"),
        *_gkr_width2_layer_events(
            0, "root_point", "root_value", "l1_point", "l1_value"
        ),
        *_gkr_width2_layer_events(
            1, "l1_point", "l1_value", "l2_point", "l2_value"
        ),
        *_gkr_width2_layer_events(
            2, "l2_point", "l2_value", "input_point", "input_value"
        ),
        check(
            "public_input_evaluation",
            "zkc.check.mle-width2-public-input",
            ["input_point", "input_value", "input0", "input1"],
            semantic_args={"oracle": GKR_WIDTH2_INPUT_ORACLE},
            expr=[
                "eq",
                ["in", 1],
                [
                    "f_add",
                    ["in", 2],
                    [
                        "f_mul",
                        ["in", 0],
                        ["f_add", ["in", 3], ["f_neg", ["in", 2]]],
                    ],
                ],
            ],
        ),
    ],
    "reduces": [
        _gkr_width2_reduce(0, "root", "layer1"),
        _gkr_width2_reduce(1, "layer1", "layer2"),
        _gkr_width2_reduce(2, "layer2", "input_eval"),
    ],
    "material_bindings": [
        material("root_point", GKR_WIDTH2_POINTS[0]),
        material("root_value", GKR_WIDTH2_VALUES[0]),
        material("l1_point", GKR_WIDTH2_POINTS[1]),
        material("l1_value", GKR_WIDTH2_VALUES[1]),
        material("l2_point", GKR_WIDTH2_POINTS[2]),
        material("l2_value", GKR_WIDTH2_VALUES[2]),
        material("input_point", GKR_WIDTH2_POINTS[3]),
        material("input_value", GKR_WIDTH2_VALUES[3]),
    ],
    "sinks": [
        discharge(
            "input_eval",
            "zkc.terminal.mle-width2-public-input",
            {"evaluation": "public_input_evaluation"},
        )
    ],
}


# The segmented link twin is intentionally an analysis artifact.  The link
# carrier and its segment-scoped transcript order are represented exactly, but
# the v0 vocabulary has no terminal theorem for the fused evaluation claim.
LINKED = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {"scalar": "ts_be8", "tg": "tg_be8"},
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "sources": [source("evaluation", "schnorr_evaluation", {"statement": EMPTY_DIGEST})],
    "events": [
        bind("X", "tg", "instance"),
        chal("c1", "scalar", "left.p.c", "2305843009213693952", ["X"]),
        bind("Y", "tg", "instance"),
        chal("c2", "scalar", "right.q.c", "2305843009213693952", ["Y"]),
    ],
    "reduces": [],
    "material_bindings": [],
    "sinks": [
        route(
            "residual",
            "evaluation",
            "evaluation-terminal-not-modeled",
        )
    ],
    "segments": [2],
}


RELATION_RESIDUAL = {
    "policy": "residual_artifact",
    "kappa": {"codecs": {}, "iv": "artifact-id", "sponge": "toy_duplex"},
    "sources": [
        source(
            "relation",
            "opaque_relation",
            {"contract": RELATION_CONTRACT, "statement": RELATION_STATEMENT},
        )
    ],
    "events": [],
    "reduces": [],
    "material_bindings": [],
    "sinks": [route("residual", "relation", "relation.validity")],
}


# The routed variant: the same Schnorr protocol carrying its
# construction routes (docs/spec/endpoints.md §6.2), so the
# prover endpoint becomes derivable. Identity moves — routes are
# declared protocol content — and nothing else changes: the events,
# checks, and sinks are byte-for-byte the unrouted ones.
SCHNORR_ROUTED = {
    **SCHNORR,
    "events": [
        bind("y", "tg", "instance"),
        slot("commit_A", "tg", True, ("sig", "a", 0), binding="commit.0"),
        chal(
            "c",
            "scalar",
            "schnorr.c",
            "2305843009213693952",
            ["y", "commit_A"],
        ),
        slot("resp_z", "scalar", True, binding="resp.0"),
        check(
            "verify",
            "zkc.check.schnorr-equation",
            ["y", "commit_A", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
    ],
    "routes": {
        "witnesses": [("w", "sigma-witness")],
        "instances": {
            "commit": {
                "contract": "zkc.hole.sigma-commit",
                "inputs": ["const:g", "witness:w"],
            },
            "resp": {
                "contract": "zkc.hole.sigma-response",
                "inputs": ["chal:c", "commit.1"],
            },
        },
    },
}

# The real-profile artifact is the same protocol the C++ family generator emits
# from test/Oir/Inputs/plonky3-fri-real.json, restated independently so the
# projected verifier executes under the twin's own supplier set.  The
# anchors are the family description's pinned digests, verbatim.
#
# The family instantiates the generic `fri` reduction contract at k rounds
# (roles fold1..k, messages g1..k, the analysis parameters as declared
# atoms), so the twin restates that instantiation rule rather than the
# registry's one-round shape; the sealed vocabulary-table digest is what
# holds the two instantiations to the same bytes.
def _fri_family_contract(k: int, query_count: int) -> dict:
    dep_slots = [
        {"role": f"fold{i}", "source": "challenge_capability",
         "class": "ext_field"}
        for i in range(1, k + 1)
    ]
    dep_slots.append(
        {"role": "query", "source": "challenge_capability",
         "class": "query_index"}
    )
    rounds: list[dict] = [
        {"challenge_use": {"role": "fold1"}, "messages": [], "kind": "fold"}
    ]
    for i in range(2, k + 1):
        rounds.append(
            {
                "challenge_use": {"role": f"fold{i}"},
                "messages": [{"role": f"g{i - 1}", "count": {"exact": 1}}],
                "kind": "fold",
            }
        )
    rounds.append(
        {
            "challenge_use": {"role": "query", "count": query_count},
            "messages": [{"role": f"g{k}", "count": {"exact": 1}}],
            "kind": "query",
        }
    )
    return {
        "consumes": ["opaque_relation"],
        "dep_slots": dep_slots,
        "rounds": rounds,
        "parameters": {
            "johnson_delta": "atom",
            "johnson_eta": "atom",
            "johnson_m": "atom",
        },
        "checks": {
            "consistency": {
                "contract": "zkc.check.rs-equality",
                "parameters": {},
                "transparent_predicate": [
                    "eq", ["role", "lhs"], ["role", "rhs"],
                ],
                "attachments": [
                    {
                        "kind": "material_ref_equality",
                        "source": {
                            "kind": "input_anchor",
                            "input": 0,
                            "anchor": "statement",
                        },
                        "target_role": "lhs",
                    },
                    {
                        "kind": "value_identity",
                        "source": {
                            "kind": "message",
                            "role": f"g{k}",
                            "occurrence": 0,
                        },
                        "target_role": "rhs",
                    },
                ],
            }
        },
        "constraints": [],
        "outputs": [
            {
                "profile": "fri_query_consistent",
                "anchors": {
                    "statement": {
                        "kind": "input_anchor",
                        "input": 0,
                        "anchor": "statement",
                    }
                },
            }
        ],
    }


def _plonky3_fri_vocabulary() -> ProtocolVocabulary:
    document = load_json(
        (REGISTRY / "protocol-vocabulary.json").read_text(encoding="utf-8")
    )
    document["reduction_contracts"]["fri"] = _fri_family_contract(3, 4)
    return ProtocolVocabulary(document)


PLONKY3_FRI_VOCABULARY = _plonky3_fri_vocabulary()
PLONKY3_FRI_STATEMENT = (
    "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"
)
PLONKY3_FRI_SPACE = "16428751811598850197311699254593454081"  # |BabyBear|^4
PLONKY3_FRI_REAL = {
    "policy": "analysis_only_artifact",
    "kappa": {
        "codecs": {
            "ext_field": "plonky3_bb31_ext4_tuple",
            "pow_value": "plonky3_bb31_low_bits",
            "query_index": "plonky3_bb31_low_bits",
            "rs": "plonky3_bb31_digest8",
        },
        "constants": {"zero": {"class": "pow_value", "value": "0"}},
        "iv": "artifact-id",
        "sponge": "plonky3_bb31_poseidon2_w16_r8_lenpad",
    },
    "sources": [
        source(
            "prox",
            "opaque_relation",
            {"contract": EMPTY_DIGEST, "statement": PLONKY3_FRI_STATEMENT},
        )
    ],
    "events": [
        bind("f_root", "rs", "instance"),
        chal("fold1", "ext_field", "fri.fold1", PLONKY3_FRI_SPACE, ["f_root"]),
        slot("g1_root", "rs", True, ("frij", "g1", 0)),
        chal("fold2", "ext_field", "fri.fold2", PLONKY3_FRI_SPACE, ["g1_root"]),
        slot("g2_root", "rs", True, ("frij", "g2", 0)),
        chal("fold3", "ext_field", "fri.fold3", PLONKY3_FRI_SPACE, ["g2_root"]),
        slot("g3_root", "rs", True, ("frij", "g3", 0)),
        slot("nonce", "rs", True, ("grind", "nonce", 0)),
        chal("pow", "pow_value", "grind.pow", "256", ["nonce"]),
        check(
            "pow_pin",
            "zkc.check.pow-zero",
            ["nonce", "pow"],
            expr=["eq", ["in", 1], ["const", "zero"]],
        ),
        chal(
            "query",
            "query_index",
            "fri.query",
            "16",
            ["g3_root"],
            mode=["vector", "4", "uniform_independent"],
        ),
        check(
            "consistency",
            "zkc.check.rs-equality",
            ["f_root", "g3_root"],
            expr=["eq", ["in", 0], ["in", 1]],
        ),
    ],
    "reduces": [
        reduce_row(
            "frij",
            "fri",
            ["prox"],
            ["fold1", "fold2", "fold3", "query"],
            [("folded", "fri_query_consistent")],
            anchors=[{"statement": PLONKY3_FRI_STATEMENT}],
            checks={"consistency": "consistency"},
            params={
                "johnson_delta": "1/4",
                "johnson_eta": "1/256",
                "johnson_m": "3",
            },
        ),
        reduce_row(
            "grind",
            "grinding",
            ["folded"],
            ["pow"],
            [("ground", "fri_query_consistent")],
            anchors=[{"statement": PLONKY3_FRI_STATEMENT}],
            checks={"pow_pin": "pow_pin"},
        ),
    ],
    "material_bindings": [material("f_root", PLONKY3_FRI_STATEMENT)],
    "sinks": [route("residual", "ground", "fri-terminal-not-modeled")],
}


# The routed witness with the commit's generator taken from the statement echo
# instead of a kappa constant, so the `bind:` reference form crosses the
# cross-implementation gate. `test/Encoding/bind-routed.mlir` is the carrier
# side.
BIND_ROUTED = copy.deepcopy(SCHNORR_ROUTED)
BIND_ROUTED["routes"]["instances"]["commit"]["inputs"] = ["bind:y", "witness:w"]


# Routed Schnorr with a grinding round: the nonce slot is supplied by a
# `pow_search` hole — the transcript peek (docs/spec/endpoints.md §6.2)
# — and the following proof-of-work challenge must derive to zero. The
# `rs`/`pow_value` class names are pinned by the shared pow-zero check
# contract; here they route to the toy codec.
# `test/Encoding/grind-schnorr.mlir` is the carrier side.
SCHNORR_GRIND = {
    **SCHNORR_ROUTED,
    "kappa": {
        "codecs": {
            "pow_value": "ts_be8",
            "rs": "ts_be8",
            "scalar": "ts_be8",
            "tg": "tg_be8",
        },
        "constants": {
            "g": {"class": "tg", "value": "4"},
            "zero": {"class": "pow_value", "value": "0"},
        },
        "iv": "artifact-id",
        "sponge": "toy_duplex",
    },
    "events": [
        bind("y", "tg", "instance"),
        slot("commit_A", "tg", True, ("sig", "a", 0), binding="commit.0"),
        chal(
            "c",
            "scalar",
            "schnorr.c",
            "2305843009213693952",
            ["y", "commit_A"],
        ),
        slot("resp_z", "scalar", True, binding="resp.0"),
        slot("nonce", "rs", True, ("grind", "nonce", 0), binding="grind.0"),
        chal("pow", "pow_value", "grind.pow", "256", ["nonce"]),
        check(
            "verify",
            "zkc.check.schnorr-equation",
            ["y", "commit_A", "c", "resp_z"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        ),
        check(
            "pow_pin",
            "zkc.check.pow-zero",
            ["nonce", "pow"],
            expr=["eq", ["in", 1], ["const", "zero"]],
        ),
    ],
    "routes": {
        "witnesses": [("w", "sigma-witness")],
        "instances": {
            "commit": {
                "contract": "zkc.hole.sigma-commit",
                "inputs": ["const:g", "witness:w"],
            },
            "grind": {
                "contract": "zkc.hole.toy-pow",
                "params": {"bits": "8"},
                "inputs": [],
            },
            "resp": {
                "contract": "zkc.hole.sigma-response",
                "inputs": ["chal:c", "commit.1"],
            },
        },
    },
    "reduces": [
        reduce_row(
            "sig",
            "sigma",
            ["dlog"],
            ["c"],
            [("evaluation", "schnorr_evaluation")],
            checks={"equation": "verify"},
            anchors=[{"statement": SCHNORR_STATEMENT}],
        ),
        reduce_row(
            "grind",
            "grinding_sigma",
            ["evaluation"],
            ["pow"],
            [("ground", "schnorr_evaluation")],
            checks={"pow_pin": "pow_pin"},
            anchors=[{"statement": SCHNORR_STATEMENT}],
        ),
    ],
    "sinks": [
        discharge(
            "ground",
            "zkc.terminal.schnorr-grinding",
            {"pow_pin": "pow_pin"},
        )
    ],
}

PIR_WITNESSES = {
    "relation-direct": RELATION_DIRECT,
    "relation-residual": RELATION_RESIDUAL,
    "schnorr": SCHNORR,
    "schnorr-routed": SCHNORR_ROUTED,
    "sumcheck": SUMCHECK,
    "sumcheck-fs": SUMCHECK_FS,
    "chaum-pedersen": CHAUM_PEDERSEN,
    "or-sigma": OR_SIGMA,
    "vecchal": VECCHAL,
    "kzg-single": KZG_SINGLE,
    "kzg-batch": KZG_BATCH,
    "opening-value-rlc": OPENING_VALUE_RLC,
    "kzg-equation-rlc": KZG_EQUATION_RLC,
    "gkr-width2-depth3": GKR_WIDTH2_DEPTH3,
    "linked": LINKED,
    "two-ready-reduces": TWO_READY_REDUCES,
    "bind-routed": BIND_ROUTED,
    "schnorr-grind": SCHNORR_GRIND,
}

PIR_REFUSAL_WITNESSES = {
    "opening-value-rlc-vulnerable": OPENING_VALUE_RLC_VULNERABLE,
    "kzg-equation-rlc-vulnerable": KZG_EQUATION_RLC_VULNERABLE,
}

OIR_WITNESSES = {
    "relation-direct": RELATION_DIRECT,
    "schnorr": SCHNORR,
    "schnorr-routed": SCHNORR_ROUTED,
    "schnorr-grind": SCHNORR_GRIND,
    "sumcheck": SUMCHECK,
    "sumcheck-fs": SUMCHECK_FS,
    "chaum-pedersen": CHAUM_PEDERSEN,
    "or-sigma": OR_SIGMA,
    "vecchal": VECCHAL,
}


def rename_protocol(protocol: dict, prefix: str) -> dict:
    """Consistently rename author handles; the PIR identity must not move."""

    result = copy.deepcopy(protocol)

    def renamed(label: str) -> str:
        return f"{prefix}_{label}"

    result["sources"] = [
        entry._replace(label=renamed(entry.label)) for entry in result["sources"]
    ]
    renamed_events = []
    for event in result["events"]:
        event = event._replace(label=renamed(event.label))
        if isinstance(event, Chal):
            event = event._replace(deps=[renamed(label) for label in event.deps])
        elif isinstance(event, Check):
            event = event._replace(inputs=[renamed(label) for label in event.inputs])
        elif isinstance(event, Slot) and event.membership:
            instance, role, index = event.membership
            event = event._replace(membership=(renamed(instance), role, index))
        renamed_events.append(event)
    result["events"] = renamed_events
    result["reduces"] = [
        reduce._replace(
            label=renamed(reduce.label),
            consumed=[renamed(label) for label in reduce.consumed],
            deps=[renamed(label) for label in reduce.deps],
            produced=[(renamed(label), profile) for label, profile in reduce.produced],
            checks={role: renamed(label) for role, label in reduce.checks.items()},
        )
        for reduce in result.get("reduces", [])
    ]
    result["material_bindings"] = [
        binding._replace(value=renamed(binding.value))
        for binding in result.get("material_bindings", [])
    ]
    result["sinks"] = [
        sink._replace(
            claim=renamed(sink.claim),
            **(
                {"checks": {role: renamed(label) for role, label in sink.checks.items()}}
                if isinstance(sink, Discharge)
                else {}
            ),
        )
        for sink in result["sinks"]
    ]
    return result
