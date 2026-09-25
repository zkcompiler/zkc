"""Canonical public matrix wire helper; this performs encoding, not arithmetic.

Use encode_matrix_json(field, [rows, columns, [[row, column, coefficient], ...]])
with canonical decimal strings, or encode_matrix with integer dimensions/entries.
Place the returned bytes.hex() in the existing typed host ``["wire", hex]`` input.
Entries must already be strictly sorted, unique, in bounds and nonzero.
"""

FIELDS = {
    "bls12-381.fr": (23, 32, 52435875175126190479447740508185965837690552500527637822603658699938581184513),
    "ristretto255.scalar": (24, 32, 2**252 + 27742317777372353535851937790883648493),
    "koala-bear": (25, 4, 2130706433),
}
DIMENSION_LIMIT = 65536
NONZERO_LIMIT = 1 << 20
WIRE_BYTE_LIMIT = 16 << 20


def _natural(value):
    if (not isinstance(value, str) or not value or len(value) > 78
            or not value.isascii() or not value.isdigit()
            or (len(value) > 1 and value[0] == "0")):
        raise ValueError("matrix-noncanonical-natural")
    return int(value)


def encode_matrix(field, rows, columns, entries, *, max_wire_bytes=WIRE_BYTE_LIMIT):
    """Return canonical ZKCV bytes from integer dimensions and COO triples."""
    if field not in FIELDS:
        raise ValueError("matrix-field")
    tag, width, modulus = FIELDS[field]
    if any(type(n) is not int or not 0 <= n <= DIMENSION_LIMIT for n in (rows, columns)):
        raise ValueError("matrix-dimension-limit")
    if len(entries) > NONZERO_LIMIT or len(entries) > rows * columns:
        raise ValueError("matrix-nonzero-limit")
    length = 18 + (8 + width) * len(entries)
    if length > min(max_wire_bytes, WIRE_BYTE_LIMIT):
        raise ValueError("matrix-wire-limit")
    previous = None
    for entry in entries:
        if len(entry) != 3 or any(type(n) is not int for n in entry):
            raise ValueError("matrix-entry")
        row, column, coefficient = entry
        if not 0 <= row < rows or not 0 <= column < columns:
            raise ValueError("matrix-index")
        if previous is not None and previous >= (row, column):
            raise ValueError("matrix-order")
        if not 0 < coefficient < modulus:
            raise ValueError("matrix-coefficient")
        previous = row, column
    out = bytearray(b"ZKCV\x01" + bytes([tag]))
    for n in (rows, columns, len(entries)):
        out.extend(n.to_bytes(4, "little"))
    for row, column, coefficient in entries:
        out.extend(row.to_bytes(4, "little"))
        out.extend(column.to_bytes(4, "little"))
        out.extend(coefficient.to_bytes(width, "little"))
    return bytes(out)


def encode_matrix_json(field, payload, *, max_wire_bytes=WIRE_BYTE_LIMIT):
    """Encode [rows, columns, COO triples] containing canonical decimal strings."""
    if not isinstance(payload, list) or len(payload) != 3 or not isinstance(payload[2], list):
        raise ValueError("matrix-record")
    rows, columns, entries = payload
    if len(entries) > NONZERO_LIMIT:
        raise ValueError("matrix-nonzero-limit")
    # A repeatable view avoids allocating a second full entry list. The integer
    # encoder validates a complete pass before allocating its wire buffer.
    class JsonEntries:
        def __len__(self):
            return len(entries)

        def __iter__(self):
            for e in entries:
                if not isinstance(e, list) or len(e) != 3:
                    raise ValueError("matrix-entry")
                yield tuple(map(_natural, e))

    return encode_matrix(field, _natural(rows), _natural(columns), JsonEntries(),
                         max_wire_bytes=max_wire_bytes)
