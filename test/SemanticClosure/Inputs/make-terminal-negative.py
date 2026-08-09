#!/usr/bin/env python3
"""Derive one focused TerminalClosure negative from a positive fixture."""

import sys
from pathlib import Path


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise SystemExit(f"expected one mutation site, found {text.count(old)}")
    return text.replace(old, new)


def replace_first(text: str, old: str, new: str) -> str:
    if old not in text:
        raise SystemExit("expected a mutation site, found none")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: make-terminal-negative.py MODE INPUT OUTPUT")
    mode, source, output = sys.argv[1:]
    text = Path(source).read_text(encoding="utf-8")

    if mode == "operand-layout":
        text = replace_first(
            text,
            '(%commitment, %point, %value, %proof : !pir.val<"g1">, '
            '!pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)',
            '(%commitment, %point, %value : !pir.val<"g1">, '
            '!pir.val<"fr">, !pir.val<"fr">)',
        )
    elif mode == "malformed-expression":
        text = replace_once(text, '["in", 3]', '["in", 99]')
    elif mode == "duplicate-producer-descriptor":
        text = replace_first(
            text,
            "sha256:75136a554c8ccd7a0780bbe87fb34ae8ef8d34eefb2509bc719f7b3160a3244b",
            "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4",
        )
        text = replace_first(
            text,
            "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba",
            "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379",
        )
    elif mode == "missing-material-binding":
        line = (
            '  pir.material_bind %commitment to '
            '"sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4" '
            ': !pir.val<"g1">\n'
        )
        text = replace_once(text, line, "")
    elif mode == "wrong-transparent-predicate":
        text = replace_once(text, '["in", 3]', '["in", 2]')
    elif mode == "unused-material-binding":
        marker = (
            '  pir.discharge %opening : !pir.claim<"single_opening"> '
            'rule "zkc.terminal.kzg-opening" checks '
            '{opening = "opening_check"}\n'
        )
        extra = (
            '  pir.material_bind %proof to '
            '"sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" '
            ': !pir.val<"g1">\n'
        )
        text = replace_once(text, marker, extra + marker)
    else:
        raise SystemExit(f"unknown mode: {mode}")

    Path(output).write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
