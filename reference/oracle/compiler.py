"""Configured compiler reference digests — the provider's identity twin.

The provider binds every configured ``ExactRef`` to the exact environment it
was constructed over (vocabulary and construction authorities through
``compilerConfiguration``), so two compilers agree on identity exactly when
they agree on every definition either may consult. This module recomputes
those digests independently; byte agreement with the carrier is the parity
gate, and the carrier's golden values remain the change tripwire.
"""

from typing import Any

from . import model

PIR_ARTIFACT_SEMANTICS = ["pir_artifact", "zkc.compiler.artifact-semantics"]
PIR_SEALED_PAYLOAD = ["pir_sealed_module", "zkc.compiler.artifact-payload"]
SAME_POINT_KZG_FAMILY = ["same_point_kzg_batch", "zkc.compiler.transform-family"]
SAME_POINT_KZG_DOMAIN = [
    "same_point_kzg_batch_domain",
    "zkc.compiler.transform-domain",
]

# The BLS12-381 scalar-field order: the batch-challenge space the KZG domain
# provider is configured with.
BLS12_381_FR = (
    "52435875175126190479447740508185965837690552500527637822603658699938581184513"
)


def compiler_configuration(
    vocabulary: model.ProtocolVocabulary,
) -> dict[str, Any]:
    """Every definition a compiler provider may consult, canonically."""

    return {
        "protocol_vocabulary": vocabulary.document,
        "construction_profiles": {
            **model.construction_profiles_document(),
            "registry": "zkc.construction_profiles",
        },
    }


def configured_ref(impl: list[str], tag: str, configuration: Any) -> list[str]:
    preimage = {"configuration": configuration, "implementation": impl}
    return [impl[0], model.tagged_digest(tag, preimage)]


def configured_semantics_ref(vocabulary: model.ProtocolVocabulary) -> list[str]:
    return configured_ref(
        PIR_ARTIFACT_SEMANTICS,
        "zkc/compiler/pir-artifact-semantics-config\n",
        {
            "payload_type": PIR_SEALED_PAYLOAD,
            "registries": compiler_configuration(vocabulary),
        },
    )


def configured_family_ref(vocabulary: model.ProtocolVocabulary) -> list[str]:
    return configured_ref(
        SAME_POINT_KZG_FAMILY,
        "zkc/compiler/same-point-kzg-family-config\n",
        {"artifact_semantics": configured_semantics_ref(vocabulary)},
    )


def configured_domain_ref(vocabulary: model.ProtocolVocabulary) -> list[str]:
    return configured_ref(
        SAME_POINT_KZG_DOMAIN,
        "zkc/compiler/same-point-kzg-domain-config\n",
        {
            "family": configured_family_ref(vocabulary),
            "batch_space": BLS12_381_FR,
        },
    )
