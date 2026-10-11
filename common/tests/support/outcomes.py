"""Read the runtime outcome being asserted, without searching unrelated fields."""

def stopped(report):
    (role,) = report['execution']['roles']
    state, detail = role['after']
    assert state == 'stopped' and detail['cause'][0] == 'backend'
    assert detail['cause'][1]['omitted_bytes'] == 0, detail
    return detail['cause'][1]['text']


def explicit_stop(report, role='role00000000'):
    """The selected participant's explicit cause, before host cleanup."""
    (participant,) = [item for item in report['execution']['roles'] if item['role'] == role]
    state, detail = participant['before']
    assert state == 'stopped', participant
    kind, message = detail['cause']
    assert kind == 'explicit' and message['omitted_bytes'] == 0, detail
    return message['text']
