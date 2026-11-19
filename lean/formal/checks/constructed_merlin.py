"""Replay the frames emitted by the Lean verifier using the catalogue's reference Merlin."""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "compiler" / "scripts"))
from replay_derived_schnorr import Transcript, merlin_conformance


def squeeze(history, label):
    first, *rest = history
    operation, domain_label, domain = first
    if operation != 0 or bytes(domain_label) != b"dom-sep":
        raise ValueError("expected the Merlin transcript initialization")
    transcript = Transcript(bytes(domain), [])
    for operation, name, data in rest:
        if operation != 0:
            raise ValueError("the single-round verifier only appends before its squeeze")
        transcript.append_message(bytes(name), bytes(data))
    return transcript.challenge_bytes(bytes(label), 64)


if __name__ == "__main__":
    if not merlin_conformance():
        raise ValueError("Merlin conformance vector failed")
    print(" ".join(map(str, squeeze(*json.loads(sys.argv[1])))))
