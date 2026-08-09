"""Check that one explicit vocabulary owns validation, citations, and id."""

import copy

from oracle import derive, model, witnesses
from oracle.model import Refusal


protocol = copy.deepcopy(witnesses.PIR_WITNESSES["sumcheck-fs"])
document = copy.deepcopy(model.VOCABULARY.document)
# The discriminator is contract content (an added parameter), so the custom
# environment differs from the repository authority by digest — the only
# kind of difference v0 recognizes.
document["reduction_contracts"]["sumcheck"]["parameters"]["probe"] = (
    "material_ref"
)
custom = model.ProtocolVocabulary(document)
protocol["reduces"] = [
    reduction._replace(
        params={**reduction.params, "probe": witnesses.EMPTY_DIGEST}
    )
    if reduction.contract == "sumcheck"
    else reduction
    for reduction in protocol["reduces"]
]

try:
    model.validate_protocol(protocol, model.VOCABULARY)
except Refusal:
    pass
else:
    raise AssertionError("global vocabulary admitted a custom-version protocol")

model.validate_protocol(protocol, custom)
view = derive.sealed_view(protocol, custom)
expected_id = model.compute_id(protocol, custom)
if view.artifact_id != expected_id:
    raise AssertionError("sealed view identity did not use its vocabulary")
if expected_id == model.compute_id(
    witnesses.PIR_WITNESSES["sumcheck-fs"], model.VOCABULARY
):
    raise AssertionError("custom vocabulary did not change protocol identity")

sumcheck = next(
    reduction
    for reduction in view.reductions.values()
    if reduction.contract_ref.id == "sumcheck"
)
if sumcheck.contract_ref.source_revision != custom.reduction_digests["sumcheck"]:
    raise AssertionError("sealed view citation did not use its vocabulary")

print("reference environment: validation, citation, and identity exact")
