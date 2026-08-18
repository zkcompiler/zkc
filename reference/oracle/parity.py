"""Command-line differential surface for the PIR/OIR twins.

The surface exposes only current semantic objects.  There are no enc2 or
split-registry modes: ProtocolVocabulary is the sole protocol registry, and
all named PIR witnesses use claim profiles, CheckContracts, and explicit
terminal rules or residual routes.
"""

from __future__ import annotations

import sys

from . import model, wellformed, witnesses


def _witness(table: dict[str, dict], name: str) -> dict:
    try:
        return table[name]
    except KeyError:
        choices = ", ".join(sorted(table))
        raise SystemExit(f"unknown witness {name!r}; choose one of: {choices}") from None


def main(argv: list[str] | None = None) -> None:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        raise SystemExit("usage: python -m oracle.parity MODE [WITNESS]")

    mode = args.pop(0)
    if mode == "protocol-vocabulary":
        if args:
            raise SystemExit("protocol-vocabulary takes no witness")
        sys.stdout.write(model.canon_json(model.VOCABULARY.document))
        return
    if mode == "vocabulary-file":
        # A family-emitted vocabulary, loaded through the same closed
        # parser as the main registry and re-emitted canonically — the
        # twin's fail-closed surface applied to generated vocabularies,
        # which otherwise seal on the C++ leg alone.
        if len(args) != 1:
            raise SystemExit("vocabulary-file requires a path")
        vocabulary = model.ProtocolVocabulary(model.load_json(open(args[0]).read()))
        sys.stdout.write(model.canon_json(vocabulary.document))
        return
    if mode == "compiler-config":
        if args:
            raise SystemExit("compiler-config takes no witness")
        from . import compiler as compiler_refs
        for label, ref in (
            ("semantics", compiler_refs.configured_semantics_ref),
            ("family", compiler_refs.configured_family_ref),
            ("domain", compiler_refs.configured_domain_ref),
        ):
            print(f"configured {label} ref: {ref(model.VOCABULARY)[1]}")
        return
    if mode == "construction-profiles":
        if args:
            raise SystemExit("construction-profiles takes no witness")
        sys.stdout.write(model.canon_json(model.construction_profiles_document()))
        return
    if mode == "relation-contracts":
        if args:
            raise SystemExit("relation-contracts takes no witness")
        sys.stdout.write(model.canon_json(model.relation_contracts_document()))
        return
    if mode == "duplex-kat":
        # The duplex framing rule as vectors (vocabularies.md §7): this
        # leg recomputes every case of the checked-in corpus and the
        # distinct pairs the length binding exists to separate. The
        # corpus was minted here, so this run is the freshness guard;
        # the C++ and Rust legs confirm the same values independently.
        if len(args) != 1:
            raise SystemExit("duplex-kat takes the corpus path")
        from .babybear import Duplex

        corpus = model.load_json(open(args[0], encoding="utf-8").read())
        first: dict[str, list[str]] = {}
        for case in corpus["cases"]:
            duplex = Duplex(case["iv"] if case["iv"] else None)
            outputs: list[str] = []
            for step in case["steps"]:
                if "absorb" in step:
                    for value in step["absorb"]:
                        duplex.absorb_word(int(value))
                else:
                    for _ in range(step["squeeze"]):
                        outputs.append(str(duplex.squeeze_word()))
            if outputs != case["outputs"]:
                raise SystemExit(
                    f"duplex framing case {case['name']!r}: this leg "
                    f"computes {outputs}, the corpus records "
                    f"{case['outputs']}")
            first[case["name"]] = outputs
        for left, right in corpus["distinct"]:
            if first[left] == first[right]:
                raise SystemExit(
                    f"duplex framing distinct pair {left!r}/{right!r} "
                    "collided: the length binding is not separating them")
        print(f"duplex framing corpus: {len(corpus['cases'])} cases agree, "
              f"{len(corpus['distinct'])} distinct pair(s) separate")
        return
    if mode == "soundness-signature":
        if args:
            raise SystemExit("soundness-signature takes no witness")
        signature = wellformed.load(
            model.load_json((model.REGISTRY / "soundness-signature.json").read_text())
        )
        sys.stdout.write(model.canon_json(signature.lint_document()))
        return
    if mode == "derive-skeleton":
        if len(args) != 2:
            raise SystemExit("derive-skeleton requires WITNESS REQUEST")
        from . import derive as derivation
        signature = wellformed.load(
            model.load_json((model.REGISTRY / "soundness-signature.json").read_text())
        )
        protocol = _witness(witnesses.PIR_WITNESSES, args[0])
        view = derivation.sealed_view(protocol, model.VOCABULARY)
        request = derivation.read_request(
            model.load_json(open(args[1]).read()), signature)
        sys.stdout.write(
            model.canon_json(derivation.derive(signature, view, request)))
        return
    if mode == "construction-bias":
        if len(args) != 3:
            raise SystemExit(
                "construction-bias requires SPONGE CODEC CHALLENGE_SPACE"
            )
        sys.stdout.write(model.canon_json(model.construction_codec_bias(*args)))
        return

    if len(args) != 1:
        raise SystemExit(f"{mode} requires exactly one witness name")
    name = args[0]

    if mode in {"oir-encode", "oir-id", "oir-semantic-id", "oir-prover-encode",
                "oir-prover-id", "oir-prover-semantic-id"}:
        protocol = _witness(witnesses.OIR_WITNESSES, name)
        kind = "prover_skeleton" if "prover" in mode else "verifier"
        if mode.endswith("-encode"):
            sys.stdout.buffer.write(
                model.canonical_oir_encoding(protocol, model.VOCABULARY, kind)
            )
        elif mode.endswith("-semantic-id"):
            print(model.compute_oir_semantic_id(protocol, model.VOCABULARY, kind))
        else:
            print(model.compute_oir_id(protocol, model.VOCABULARY, kind))
        return

    witness_table = witnesses.PIR_WITNESSES
    if mode == "validate" and name in witnesses.PIR_REFUSAL_WITNESSES:
        witness_table = witnesses.PIR_REFUSAL_WITNESSES
    protocol = _witness(witness_table, name)
    if mode == "encode":
        sys.stdout.buffer.write(
            model.canonical_encoding(protocol, model.VOCABULARY)
        )
    elif mode == "id":
        print(model.compute_id(protocol, model.VOCABULARY))
    elif mode == "validate":
        model.validate_protocol(protocol, model.VOCABULARY)
        print("ok")
    elif mode == "closure":
        records = {
            "reductions": model.reduction_closure(protocol, model.VOCABULARY),
            "terminals": model.terminal_closure(protocol, model.VOCABULARY),
        }
        sys.stdout.write(model.canon_json(records))
    elif mode == "resolved-vocabulary":
        resolved = model.resolved_vocabulary(protocol, model.VOCABULARY)
        sys.stdout.write(model.canon_json(resolved))
    else:
        raise SystemExit(f"unknown parity mode {mode!r}")


if __name__ == "__main__":
    main()
