"""Separately coded literal transition relation for finite comparison.

This module intentionally does not call ``transition.start``, ``absorb``, or
``squeeze``.  It shares only the frozen alphabet dimensions and provider
functions, so agreement is implementation-diversity evidence rather than a
second semantic authority.
"""

from __future__ import annotations

from typing import Iterable

from .diagnostics import MalformedInput
from .transition import (
    ALPHABET_SIZE,
    BASELINE_PERMUTATION_MATRIX,
    BASELINE_PERMUTATION_OFFSET,
    BASELINE_START_MATRIX,
    BASELINE_START_OFFSET,
    CAPACITY,
    RATE,
    STATE_WIDTH,
)


ReferenceState = tuple[tuple[int, ...], int, int]


def _check_cells(cells: Iterable[int]) -> tuple[int, ...]:
    result = tuple(cells)
    if len(result) != STATE_WIDTH or any(
        type(value) is not int or not 0 <= value < ALPHABET_SIZE for value in result
    ):
        raise MalformedInput("independent state cells are malformed")
    return result


def independent_hash(
    instance: bytes,
    matrix: tuple[tuple[int, ...], ...] = BASELINE_START_MATRIX,
    offset: tuple[int, ...] = BASELINE_START_OFFSET,
) -> tuple[int, ...]:
    if type(instance) is not bytes or len(instance) != 2:
        raise MalformedInput("independent hash input is malformed")
    output: list[int] = []
    for row_index in range(CAPACITY):
        accumulated = offset[row_index]
        for column_index in range(2):
            accumulated += matrix[row_index][column_index] * instance[column_index]
        output.append(accumulated % ALPHABET_SIZE)
    return tuple(output)


def independent_permutation(
    cells: tuple[int, ...],
    matrix: tuple[tuple[int, ...], ...] = BASELINE_PERMUTATION_MATRIX,
    offset: tuple[int, ...] = BASELINE_PERMUTATION_OFFSET,
) -> tuple[int, ...]:
    values = _check_cells(cells)
    output: list[int] = []
    for row_index in range(STATE_WIDTH):
        accumulated = offset[row_index]
        for column_index in range(STATE_WIDTH):
            accumulated += matrix[row_index][column_index] * values[column_index]
        output.append(accumulated % ALPHABET_SIZE)
    return tuple(output)


def independent_start(
    instance: bytes,
    start_matrix: tuple[tuple[int, ...], ...] = BASELINE_START_MATRIX,
    start_offset: tuple[int, ...] = BASELINE_START_OFFSET,
) -> ReferenceState:
    capacity = independent_hash(instance, start_matrix, start_offset)
    return ((0, 0, 0, capacity[0], capacity[1]), 0, RATE)


def independent_absorb(
    state: ReferenceState,
    input_symbols: tuple[int, ...],
    permutation_matrix: tuple[tuple[int, ...], ...] = BASELINE_PERMUTATION_MATRIX,
    permutation_offset: tuple[int, ...] = BASELINE_PERMUTATION_OFFSET,
) -> tuple[ReferenceState, int]:
    cells, absorb_index, _ = state
    cells = _check_cells(cells)
    if type(input_symbols) is not tuple or any(
        type(value) is not int or not 0 <= value < ALPHABET_SIZE
        for value in input_symbols
    ):
        raise MalformedInput("independent absorb input is malformed")
    squeeze_index = RATE
    calls = 0
    cursor = 0
    while cursor < len(input_symbols):
        if absorb_index == RATE:
            cells = independent_permutation(
                cells, permutation_matrix, permutation_offset
            )
            absorb_index = 0
            squeeze_index = RATE
            calls += 1
            continue
        mutable = list(cells)
        mutable[absorb_index] = input_symbols[cursor]
        cells = tuple(mutable)
        absorb_index += 1
        cursor += 1
    return (cells, absorb_index, squeeze_index), calls


def independent_squeeze(
    state: ReferenceState,
    length: int,
    permutation_matrix: tuple[tuple[int, ...], ...] = BASELINE_PERMUTATION_MATRIX,
    permutation_offset: tuple[int, ...] = BASELINE_PERMUTATION_OFFSET,
) -> tuple[ReferenceState, tuple[int, ...], int]:
    cells, absorb_index, squeeze_index = state
    cells = _check_cells(cells)
    if type(length) is not int or not 0 <= length <= 16:
        raise MalformedInput("independent squeeze length is malformed")
    if length == 0:
        return (cells, absorb_index, squeeze_index), (), 0
    absorb_index = 0
    output: list[int] = []
    calls = 0
    while len(output) < length:
        if squeeze_index == RATE:
            cells = independent_permutation(
                cells, permutation_matrix, permutation_offset
            )
            squeeze_index = 0
            absorb_index = 0
            calls += 1
            continue
        output.append(cells[squeeze_index])
        squeeze_index += 1
    return (cells, absorb_index, squeeze_index), tuple(output), calls
