"""Export an explicitly selected closed protocol subject.

The compiler owns name resolution and static argument checking. A subject is
independent of any Host Entry that invokes it; no wrapper correspondence or
execution count is inferred from a deployment inventory.
"""

import hashlib
import json


def native_subject(execute, compiler, flags):
    """Return original bytes, exact CLI interface bytes, and its parsed view."""
    if sum(flag.startswith('--subject=') for flag in flags) != 1 or any(
            flag.startswith(('--entry=', '--entry-kind=')) for flag in flags):
        raise ValueError('a protocol bridge requires one explicit --subject')
    source = execute([compiler, 'language-emit', *flags])
    interface_text = execute([compiler, 'language-interface', *flags])
    interface = json.loads(interface_text)
    if (interface.get('format') != 'zkc.language-interface/0'
            or interface.get('job', {}).get('kind') != 'run'):
        raise ValueError('the selected subject is not an interactive protocol')
    if interface['original'] != hashlib.sha256(source.encode()).hexdigest():
        raise ValueError('subject source and interface identities disagree')
    return source, interface_text, interface
