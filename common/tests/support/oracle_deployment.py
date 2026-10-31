"""Explicit physical oracle choices for compiler/Host integration tests."""

import json


def table_realization(scheme, *, grouping='individual', table_order='natural',
                      order='after-final-draw', authentication='atomic-blocks'):
    """Select a table interpretation independently of the authored protocol.

    The empty scheme is the clear-table interpretation. Callers testing
    authentication name an installed commitment scheme explicitly.
    """
    return '--oracle-realization=' + json.dumps({
        'format': 'zkc.oracle-selection/0',
        'roots': {'kind': 'uniform', 'table': {
            'scheme': scheme, 'grouping': grouping, 'order': table_order}},
        'order': order, 'authentication': authentication,
    }, separators=(',', ':'))
