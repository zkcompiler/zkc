"""CPU placement and worker observations, independent of workload selection."""
from pathlib import Path
import re

from .io import require


def cpu_list(text):
    """Parse Linux CPU-list notation, including a singleton, into sorted CPUs."""
    if not isinstance(text, str) or not re.fullmatch(r'[0-9]+(?:-[0-9]+)?(?:,[0-9]+(?:-[0-9]+)?)*', text):
        raise ValueError('expected a CPU list such as 2,4-7')
    cpus = set()
    for part in text.split(','):
        first, _, last = part.partition('-')
        first, last = int(first), int(last or first)
        # Linux CPU ids are bounded, and malformed input must not allocate an
        # arbitrary-size range before the current-affinity check.
        if not 0 <= first <= last < (1 << 20):
            raise ValueError('invalid CPU range')
        cpus.update(range(first, last + 1))
    return sorted(cpus)


def cpu_features(text, cpus):
    """ISA common to selected CPUs, without assuming a homogeneous machine."""
    records = {}
    for block in text.split('\n\n'):
        fields = {name.strip(): values.strip() for line in block.splitlines()
                  for name, separator, values in [line.partition(':')] if separator}
        identifier = fields.get('processor', '')
        if identifier.isascii() and identifier.isdigit():
            records[int(identifier)] = set(fields.get('flags', fields.get('Features', '')).split())
    selected = list(records) if cpus is None else cpus
    return sorted(set.intersection(*(records.get(cpu, set()) for cpu in selected))) if selected else []


def cpu_facts(cpus):
    topology = {}
    for cpu in cpus or []:
        root = Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
        topology[str(cpu)] = {name: (root/name).read_text().strip()
                              for name in ('core_id', 'physical_package_id', 'thread_siblings_list')
                              if (root/name).is_file()}
    info = Path('/proc/cpuinfo')
    features = cpu_features(info.read_text(), cpus) if info.is_file() else []
    return {'topology': topology, 'runtime_cpu_features': features,
            'runtime_cpu_features_scope': 'intersection over selected CPUs; unavailable observations contribute no features'}


def validate_condition(host, threads):
    require(type(threads) is int and threads > 0, 'invalid thread setting')
    require(isinstance(host, dict) and {'requested_cpus', 'affinity'} <= host.keys(), 'missing CPU placement policy')
    for name in ('affinity', 'requested_cpus'):
        value = host[name]
        require(value is None or isinstance(value, list) and value
                and all(type(cpu) is int and cpu >= 0 for cpu in value)
                and value == sorted(set(value)), 'invalid CPU placement policy')
    require(host['requested_cpus'] is None or host['requested_cpus'] == host['affinity'],
            'recorded host affinity differs from CPU selection')


def validate_process(process, host, threads):
    require(process.get('rayon_num_threads') == str(threads), 'worker thread setting differs')
    requested = host.get('requested_cpus')
    if requested is None:
        return
    require(isinstance(process.get('affinity'), str), 'worker affinity differs')
    require(cpu_list(process.get('affinity')) == requested, 'worker affinity differs')
    records = process.get('thread_affinities')
    require(isinstance(records, list) and records, 'missing worker thread affinities')
    require(process.get('thread_observation_errors') == [], 'incomplete worker thread observation')
    tids = set()
    for record in records:
        require(isinstance(record, dict) and set(record) == {'tid', 'cpus'}
                and type(record['tid']) is int and record['tid'] > 0
                and record['tid'] not in tids, 'invalid worker thread affinity')
        tids.add(record['tid'])
        require(set(cpu_list(record['cpus'])) <= set(requested), 'worker thread escaped CPU set')
