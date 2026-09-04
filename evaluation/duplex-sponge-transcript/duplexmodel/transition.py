"""Literal finite model of the reviewed duplex transition pseudocode.

The alphabet and provider below are intentionally tiny.  The provider is a
deterministic transition oracle used to expose state edges; it is not a random
function, random permutation, sponge instantiation, or security parameter.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable

from .diagnostics import MalformedInput


ALPHABET_SIZE = 5
RATE = 3
CAPACITY = 2
STATE_WIDTH = RATE + CAPACITY

BASELINE_START_MATRIX = ((1, 1), (1, 2))
BASELINE_START_OFFSET = (0, 0)
BASELINE_PERMUTATION_MATRIX = (
    (1, 1, 0, 0, 0),
    (0, 1, 1, 0, 0),
    (0, 0, 1, 1, 0),
    (0, 0, 0, 1, 1),
    (1, 0, 0, 0, 1),
)
BASELINE_PERMUTATION_OFFSET = (1, 2, 3, 4, 0)


def _symbol(value: object, *, where: str) -> int:
    if type(value) is not int or not 0 <= value < ALPHABET_SIZE:
        raise MalformedInput(f"{where} is not a Sigma5 symbol")
    return value


def symbols(values: Iterable[object], *, where: str) -> tuple[int, ...]:
    if type(values) not in {tuple, list}:
        raise MalformedInput(f"{where} must be a finite symbol sequence")
    return tuple(_symbol(value, where=f"{where}[{index}]") for index, value in enumerate(values))


@dataclass(frozen=True)
class DuplexState:
    cells: tuple[int, ...]
    absorb_index: int
    squeeze_index: int

    def __post_init__(self) -> None:
        if type(self.cells) is not tuple or len(self.cells) != STATE_WIDTH:
            raise MalformedInput("duplex state has the wrong exact carrier")
        for index, value in enumerate(self.cells):
            _symbol(value, where=f"state[{index}]")
        if type(self.absorb_index) is not int or not 0 <= self.absorb_index <= RATE:
            raise MalformedInput("absorb index is outside 0..rate")
        if type(self.squeeze_index) is not int or not 0 <= self.squeeze_index <= RATE:
            raise MalformedInput("squeeze index is outside 0..rate")

    def to_term(self) -> dict[str, object]:
        return {
            "cells": list(self.cells),
            "absorb_index": self.absorb_index,
            "squeeze_index": self.squeeze_index,
        }


@dataclass(frozen=True)
class ForwardOracle:
    start_hash: Callable[[bytes], tuple[int, ...]]
    permutation: Callable[[tuple[int, ...]], tuple[int, ...]]


@dataclass(frozen=True)
class TransitionResult:
    state: DuplexState
    permutation_calls: int


@dataclass(frozen=True)
class SqueezeResult:
    state: DuplexState
    output: tuple[int, ...]
    permutation_calls: int


def affine_forward_oracle(
    start_matrix: tuple[tuple[int, ...], ...],
    start_offset: tuple[int, ...],
    permutation_matrix: tuple[tuple[int, ...], ...],
    permutation_offset: tuple[int, ...],
) -> ForwardOracle:
    """Construct the exact finite affine provider declared by a construction."""

    def start_hash(instance: bytes) -> tuple[int, ...]:
        if type(instance) is not bytes or len(instance) != 2:
            raise MalformedInput("affine Start hash requires exactly two octets")
        return tuple(
            (
                sum(
                    coefficient * value
                    for coefficient, value in zip(row, instance, strict=True)
                )
                + constant
            )
            % ALPHABET_SIZE
            for row, constant in zip(start_matrix, start_offset, strict=True)
        )

    def permutation(state: tuple[int, ...]) -> tuple[int, ...]:
        checked = symbols(state, where="affine permutation input")
        return tuple(
            (
                sum(
                    coefficient * value
                    for coefficient, value in zip(row, checked, strict=True)
                )
                + constant
            )
            % ALPHABET_SIZE
            for row, constant in zip(
                permutation_matrix, permutation_offset, strict=True
            )
        )

    return ForwardOracle(start_hash, permutation)


def toy_start_hash(instance: bytes) -> tuple[int, ...]:
    return affine_forward_oracle(
        BASELINE_START_MATRIX,
        BASELINE_START_OFFSET,
        BASELINE_PERMUTATION_MATRIX,
        BASELINE_PERMUTATION_OFFSET,
    ).start_hash(instance)


def toy_permutation(state: tuple[int, ...]) -> tuple[int, ...]:
    # One fixed affine bijection with visible cross-cell diffusion.  The
    # arithmetic is only a convenient finite permutation definition; Sigma5
    # is not claimed to be a protocol field or cryptographic state space.
    return affine_forward_oracle(
        BASELINE_START_MATRIX,
        BASELINE_START_OFFSET,
        BASELINE_PERMUTATION_MATRIX,
        BASELINE_PERMUTATION_OFFSET,
    ).permutation(state)


def toy_inverse_permutation(state: tuple[int, ...]) -> tuple[int, ...]:
    if type(state) is not tuple or len(state) != STATE_WIDTH:
        raise MalformedInput("toy inverse input has the wrong width")
    y = symbols(state, where="toy inverse input")
    adjusted = (
        (y[0] - 1) % ALPHABET_SIZE,
        (y[1] - 2) % ALPHABET_SIZE,
        (y[2] - 3) % ALPHABET_SIZE,
        (y[3] - 4) % ALPHABET_SIZE,
        y[4],
    )
    inverse_matrix = (
        (3, 2, 3, 2, 3),
        (3, 3, 2, 3, 2),
        (2, 3, 3, 2, 3),
        (3, 2, 3, 3, 2),
        (2, 3, 2, 3, 3),
    )
    return tuple(
        sum(coefficient * value for coefficient, value in zip(row, adjusted, strict=True))
        % ALPHABET_SIZE
        for row in inverse_matrix
    )


TOY_FORWARD_ORACLE = ForwardOracle(toy_start_hash, toy_permutation)


def all_states() -> Iterable[tuple[int, ...]]:
    return product(range(ALPHABET_SIZE), repeat=STATE_WIDTH)


def start(oracle: ForwardOracle, instance: bytes) -> DuplexState:
    capacity = oracle.start_hash(instance)
    if type(capacity) is not tuple or len(capacity) != CAPACITY:
        raise MalformedInput("Start hash returned the wrong capacity width")
    capacity = symbols(capacity, where="Start hash output")
    return DuplexState((0,) * RATE + capacity, 0, RATE)


def _apply_permutation(oracle: ForwardOracle, state: tuple[int, ...]) -> tuple[int, ...]:
    output = oracle.permutation(state)
    if type(output) is not tuple or len(output) != STATE_WIDTH:
        raise MalformedInput("permutation returned the wrong state width")
    return symbols(output, where="permutation output")


def absorb(
    oracle: ForwardOracle,
    state: DuplexState,
    input_symbols: tuple[int, ...] | list[int],
) -> TransitionResult:
    data = symbols(input_symbols, where="absorb input")
    cells = state.cells
    absorb_index = state.absorb_index
    # Construction 3.3 resets i_S once at the beginning of every Absorb call,
    # including the empty call.
    squeeze_index = RATE
    permutation_calls = 0
    for value in data:
        if absorb_index == RATE:
            cells = _apply_permutation(oracle, cells)
            permutation_calls += 1
            absorb_index = 0
            squeeze_index = RATE
        mutable = list(cells)
        mutable[absorb_index] = value
        cells = tuple(mutable)
        absorb_index += 1
    return TransitionResult(
        DuplexState(cells, absorb_index, squeeze_index), permutation_calls
    )


def squeeze(oracle: ForwardOracle, state: DuplexState, length: int) -> SqueezeResult:
    if type(length) is not int or not 0 <= length <= 16:
        raise MalformedInput("squeeze length is outside the finite validation bound")
    # A zero-length squeeze is the exact identity, including both indices.
    if length == 0:
        return SqueezeResult(state, (), 0)
    cells = state.cells
    absorb_index = 0
    squeeze_index = state.squeeze_index
    output: list[int] = []
    permutation_calls = 0
    for _ in range(length):
        if squeeze_index == RATE:
            cells = _apply_permutation(oracle, cells)
            permutation_calls += 1
            absorb_index = 0
            squeeze_index = 0
        output.append(cells[squeeze_index])
        squeeze_index += 1
    return SqueezeResult(
        DuplexState(cells, absorb_index, squeeze_index),
        tuple(output),
        permutation_calls,
    )
