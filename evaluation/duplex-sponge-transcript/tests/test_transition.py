from __future__ import annotations

from itertools import product
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.independent import (  # noqa: E402
    independent_absorb,
    independent_squeeze,
)
from duplexmodel.transition import (  # noqa: E402
    ALPHABET_SIZE,
    RATE,
    TOY_FORWARD_ORACLE,
    DuplexState,
    absorb,
    all_states,
    squeeze,
    start,
    toy_inverse_permutation,
    toy_permutation,
)


class TransitionTest(unittest.TestCase):
    def test_start_and_complete_source_schedule_have_exact_vectors(self) -> None:
        state = start(TOY_FORWARD_ORACLE, bytes((4, 9)))
        self.assertEqual(state, DuplexState((0, 0, 0, 3, 2), 0, 3))

        state = absorb(TOY_FORWARD_ORACLE, state, (2, 4)).state
        self.assertEqual(state, DuplexState((2, 4, 0, 3, 2), 2, 3))
        state = absorb(TOY_FORWARD_ORACLE, state, (3, 1)).state
        self.assertEqual(state, DuplexState((1, 4, 4, 4, 4), 1, 3))
        first = squeeze(TOY_FORWARD_ORACLE, state, 2)
        self.assertEqual(first.output, (1, 0))
        self.assertEqual(first.state, DuplexState((1, 0, 1, 2, 0), 0, 2))
        state = absorb(TOY_FORWARD_ORACLE, first.state, ()).state
        self.assertEqual(state, DuplexState((1, 0, 1, 2, 0), 0, 3))
        second = squeeze(TOY_FORWARD_ORACLE, state, 1)
        self.assertEqual(second.output, (2,))
        self.assertEqual(second.state, DuplexState((2, 3, 1, 1, 1), 0, 1))
        state = absorb(TOY_FORWARD_ORACLE, second.state, (1, 2, 3)).state
        self.assertEqual(state, DuplexState((1, 2, 3, 1, 1), 3, 3))
        third = squeeze(TOY_FORWARD_ORACLE, state, 4)
        self.assertEqual(third.output, (4, 2, 2, 2))
        self.assertEqual(third.state, DuplexState((2, 1, 1, 2, 1), 0, 1))

    def test_toy_permutation_is_exhaustively_bijective(self) -> None:
        checked = 0
        for cells in all_states():
            state = tuple(cells)
            self.assertEqual(toy_inverse_permutation(toy_permutation(state)), state)
            self.assertEqual(toy_permutation(toy_inverse_permutation(state)), state)
            checked += 1
        self.assertEqual(checked, ALPHABET_SIZE**5)

    def test_zero_squeeze_is_exact_identity(self) -> None:
        state = DuplexState((1, 0, 1, 2, 0), 0, 2)
        result = squeeze(TOY_FORWARD_ORACLE, state, 0)
        self.assertIs(result.state, state)
        self.assertEqual(result.output, ())
        self.assertEqual(result.permutation_calls, 0)

    def test_empty_absorb_resets_only_squeeze_index(self) -> None:
        state = DuplexState((1, 0, 1, 2, 0), 0, 2)
        result = absorb(TOY_FORWARD_ORACLE, state, ())
        self.assertEqual(result.state, DuplexState((1, 0, 1, 2, 0), 0, 3))
        self.assertEqual(result.permutation_calls, 0)
        following = squeeze(TOY_FORWARD_ORACLE, result.state, 1)
        self.assertEqual(following.output, (2,))
        self.assertEqual(following.permutation_calls, 1)

    def test_adjacent_squeezes_continue_one_stream(self) -> None:
        state = DuplexState((1, 4, 4, 4, 4), 1, 3)
        first = squeeze(TOY_FORWARD_ORACLE, state, 1)
        second = squeeze(TOY_FORWARD_ORACLE, first.state, 3)
        combined = squeeze(TOY_FORWARD_ORACLE, state, 4)
        self.assertEqual(first.output + second.output, (1, 0, 1, 2))
        self.assertEqual(first.output + second.output, combined.output)
        self.assertEqual(second.state, combined.state)
        self.assertEqual(
            first.permutation_calls + second.permutation_calls,
            combined.permutation_calls,
        )

    def test_partial_squeeze_then_absorb_overwrites_from_rate_zero(self) -> None:
        state = DuplexState((1, 0, 1, 2, 0), 0, 2)
        result = absorb(TOY_FORWARD_ORACLE, state, (4,))
        self.assertEqual(result.state, DuplexState((4, 0, 1, 2, 0), 1, 3))
        self.assertNotEqual(result.state.cells[0], (state.cells[0] + 4) % 5)
        self.assertEqual(result.permutation_calls, 0)

    def test_filled_rate_segment_is_lazy_until_the_next_symbol(self) -> None:
        state = start(TOY_FORWARD_ORACLE, bytes((4, 9)))
        state = absorb(TOY_FORWARD_ORACLE, state, (1, 2)).state
        filled = absorb(TOY_FORWARD_ORACLE, state, (3,))
        self.assertEqual(filled.state, DuplexState((1, 2, 3, 3, 2), 3, 3))
        self.assertEqual(filled.permutation_calls, 0)
        following = absorb(TOY_FORWARD_ORACLE, filled.state, (4,))
        self.assertEqual(following.state, DuplexState((4, 2, 4, 4, 3), 1, 3))
        self.assertEqual(following.permutation_calls, 1)

    def test_absorb_matches_independent_relation_exhaustively(self) -> None:
        checked = 0
        for cells in all_states():
            for absorb_index in range(RATE + 1):
                for squeeze_index in range(RATE + 1):
                    state = DuplexState(tuple(cells), absorb_index, squeeze_index)
                    raw = (state.cells, absorb_index, squeeze_index)
                    for data in ((), (0,), (4,)):
                        actual = absorb(TOY_FORWARD_ORACLE, state, data)
                        expected_state, expected_calls = independent_absorb(raw, data)
                        self.assertEqual(
                            (
                                actual.state.cells,
                                actual.state.absorb_index,
                                actual.state.squeeze_index,
                            ),
                            expected_state,
                        )
                        self.assertEqual(actual.permutation_calls, expected_calls)
                        checked += 1
        self.assertEqual(checked, (ALPHABET_SIZE**5) * 16 * 3)

    def test_squeeze_matches_independent_relation_exhaustively(self) -> None:
        checked = 0
        for cells in all_states():
            for absorb_index, squeeze_index in product(range(RATE + 1), repeat=2):
                state = DuplexState(tuple(cells), absorb_index, squeeze_index)
                raw = (state.cells, absorb_index, squeeze_index)
                for length in range(5):
                    actual = squeeze(TOY_FORWARD_ORACLE, state, length)
                    expected_state, expected_output, expected_calls = independent_squeeze(
                        raw, length
                    )
                    self.assertEqual(
                        (actual.state.cells, actual.state.absorb_index, actual.state.squeeze_index),
                        expected_state,
                    )
                    self.assertEqual(actual.output, expected_output)
                    self.assertEqual(actual.permutation_calls, expected_calls)
                    checked += 1
        self.assertEqual(checked, (ALPHABET_SIZE**5) * 16 * 5)
