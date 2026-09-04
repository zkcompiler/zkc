"""Independent classifiers for the composition-critical finite matrix."""

from __future__ import annotations

import reference_model as m


def check_run_grounding_basis(
    public: object | None,
    confidential: tuple[m.ConfidentialRunCapability, ...],
) -> m.Result:
    if type(confidential) is not tuple:
        return m.Result(m.Outcome.MALFORMED)
    coordinates: list[str] = []
    sources: list[object] = []
    if public is not None:
        basis = m._public_basis(public)
        if basis is None:
            return m.Result(m.Outcome.REFUSED)
        sources.append(basis)
    for item in confidential:
        if type(item) is not m.ConfidentialRunCapability:
            return m.Result(m.Outcome.REFUSED)
        coordinates.append(item.coordinate)
        basis = m._confidential_basis(item)
        if basis is None:
            return m.Result(m.Outcome.REFUSED)
        sources.append(basis)
    if tuple(coordinates) != tuple(sorted(set(coordinates))):
        return m.Result(m.Outcome.MALFORMED)
    if not sources:
        return m.Result(m.Outcome.CANNOT_ANSWER)
    if confidential and any(
        basis.qualification is not m.RunQualification.CAUSAL for basis in sources
    ):
        return m.Result(m.Outcome.REFUSED)
    first = sources[0]
    if any(candidate is not first for candidate in sources[1:]):
        return m.Result(m.Outcome.REFUSED)
    return m.Result(m.Outcome.AFFIRMATIVE)


def classify_endpoint_support(request: object) -> m.Result:
    if type(request) is not m.EndpointRequest:
        return m.Result(m.Outcome.MALFORMED)
    scalar_shape = (
        type(request.challenge_mode) is m.ChallengeMode
        and type(request.purpose) is m.EndpointPurpose
        and type(request.has_oracle) is bool
        and type(request.has_module_effect) is bool
        and type(request.plan_present) is bool
        and type(request.plan_realizes_present) is bool
        and type(request.plan_realizes) is bool
        and type(request.continuation_arm_count) is int
        and request.continuation_arm_count >= 0
    )
    construction_shape = (
        type(request.construction_family) is m.ConstructionFamily
        if request.challenge_mode is m.ChallengeMode.FIAT_SHAMIR
        else request.construction_family is None
    )
    if not scalar_shape or not construction_shape:
        return m.Result(m.Outcome.MALFORMED)

    predicates = {
        m.UnsupportedReason.FRESH: request.challenge_mode is m.ChallengeMode.FRESH,
        m.UnsupportedReason.GENERIC_PROVER: request.purpose
        is m.EndpointPurpose.GENERIC_PROVER,
        m.UnsupportedReason.ORACLE: request.has_oracle,
        m.UnsupportedReason.MODULE_EFFECT: request.has_module_effect,
        m.UnsupportedReason.OTHER_CONSTRUCTION: request.construction_family
        in (
            m.ConstructionFamily.DUPLEX_SPONGE,
            m.ConstructionFamily.OTHER_AUTHENTICATED,
        ),
    }
    reasons = tuple(
        reason.value for reason in m.UnsupportedReason if predicates.get(reason, False)
    )
    if reasons:
        return m.Result(m.Outcome.UNSUPPORTED, reasons)

    plan_purpose = request.purpose in {
        m.EndpointPurpose.PLAN_PROVER,
        m.EndpointPurpose.CONTINUATION_PROVER,
    }
    if plan_purpose:
        if not request.plan_present or not request.plan_realizes_present:
            return m.Result(m.Outcome.MISSING_DEPENDENCY)
        if not request.plan_realizes:
            return m.Result(m.Outcome.REFUSED)
    elif (
        request.plan_present
        or request.plan_realizes_present
        or request.plan_realizes
    ):
        return m.Result(m.Outcome.MALFORMED)
    if (
        request.purpose is m.EndpointPurpose.CONTINUATION_PROVER
        and request.continuation_arm_count == 0
    ):
        return m.Result(
            m.Outcome.UNSUPPORTED,
            (m.UnsupportedReason.NO_CONTINUATION_ARM.value,),
        )
    return m.Result(m.Outcome.SUPPORTED)


def encode_duplex_instance(
    bindings: object, public_inputs: object
) -> m.InstanceEncodingResult:
    if type(bindings) is not tuple or type(public_inputs) is not tuple:
        return m.InstanceEncodingResult(m.Outcome.MALFORMED)
    if any(type(binding) is not m.DuplexInstanceBinding for binding in bindings):
        return m.InstanceEncodingResult(m.Outcome.MALFORMED)
    if any(type(value) is not m.PublicInputDatum for value in public_inputs):
        return m.InstanceEncodingResult(m.Outcome.MALFORMED)
    refs = [binding.binding_ref for binding in bindings]
    if refs != sorted(set(refs)) or any(
        type(ref) is not int or ref < 0 for ref in refs
    ):
        return m.InstanceEncodingResult(m.Outcome.MALFORMED)

    encoded_records: list[bytes] = []
    for binding in bindings:
        if binding.origin is not m.InstanceValueOrigin.PUBLIC_INPUT:
            return m.InstanceEncodingResult(m.Outcome.REFUSED)
        input_ref = binding.public_input_ref
        if type(input_ref) is not int or not 0 <= input_ref < len(public_inputs):
            return m.InstanceEncodingResult(m.Outcome.MISSING_DEPENDENCY)
        value = public_inputs[input_ref]
        if value.value_type_body != binding.value_type_body:
            return m.InstanceEncodingResult(m.Outcome.KIND_MISMATCH)

        fields = (
            (0, b"N" + binding.binding_ref.to_bytes(8, "big")),
            (
                1,
                b"Y"
                + len(binding.value_type_body).to_bytes(4, "big")
                + binding.value_type_body,
            ),
            (2, b"Y" + len(value.datum).to_bytes(4, "big") + value.datum),
        )
        payload = b"".join(
            ordinal.to_bytes(4, "big") + len(field).to_bytes(4, "big") + field
            for ordinal, field in fields
        )
        encoded_records.append(b"R" + len(fields).to_bytes(4, "big") + payload)

    payload = b"".join(
        len(record).to_bytes(4, "big") + record for record in encoded_records
    )
    return m.InstanceEncodingResult(
        m.Outcome.AFFIRMATIVE,
        b"S" + len(encoded_records).to_bytes(4, "big") + payload,
    )
