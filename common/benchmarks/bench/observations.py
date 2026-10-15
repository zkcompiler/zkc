"""Deterministic execution observations; these do not attribute elapsed time."""
from collections import Counter
import json

from .io import require

EVENTS = frozenset('''charged_instructions replayed_instructions created_frames
backend_enter_calls backend_leave_calls value_validation_calls backend_validation_calls
retention_plan_calls retention_planned_values retention_commit_values retention_release_values retention_unpin_values
computation_reuse_hits native_operand_values local_bool local_variant local_match local_stop
local_conditional local_for local_yield local_release local_op local_return'''.split())


def validate_counts(counts):
    require(isinstance(counts, dict) and set(counts) == {'events', 'operations'}, 'invalid execution counts')
    events, operations = counts['events'], counts['operations']
    require(isinstance(events, dict) and set(events) == EVENTS, 'invalid execution event names')
    require(isinstance(operations, dict) and all(isinstance(k, str) and k for k in operations),
            'invalid execution operation names')
    require(all(type(v) is int and 0 <= v < 2**64 for group in (events, operations) for v in group.values()),
            'invalid execution count value')
    # Workers publish successful calls only. Every native local instruction
    # reaches one backend invocation; successful frames are balanced.
    require(sum(operations.values()) == events['local_op'], 'native call histogram mismatch')
    require(events['backend_enter_calls'] == events['backend_leave_calls'], 'unbalanced execution frames')


def summarize_counts(results):
    """Keep first visits distinct; deduplicate repeated equal vectors only."""
    rows = []
    for result in results:
        seen, groups = set(), Counter()
        for call in result['worker']['lifecycle']['calls']:
            index = call['input_index']
            key = (index, index not in seen, json.dumps(call['execution_counts'], sort_keys=True))
            seen.add(index)
            groups[key] += 1
        rows.extend({'repetition': result['repetition'], 'input_index': index,
                     'first_visit': first, 'calls': count, 'counts': json.loads(encoded)}
                    for (index, first, encoded), count in groups.items())
    return rows
