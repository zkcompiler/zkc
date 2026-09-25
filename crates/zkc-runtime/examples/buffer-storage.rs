//! Reproducible retained-capacity measurements, not a runtime speed benchmark.
use serde_json::json;
use zkc_runtime::buffer::{BufferStore, PackedBuffers, SegmentedBuffers};

fn measure<S: BufferStore<u8>>(
    name: &str,
    scenario: &str,
    mut store: S,
    batches: &[(usize, usize)],
) -> serde_json::Value {
    let mut aliases = Vec::new();
    let mut snapshots = Vec::new();
    for (step, &(reserved, published)) in batches.iter().enumerate() {
        store.reserve(reserved, 1).unwrap();
        let capacity = store.usage().reserved_bytes;
        let values = vec![(step % 7) as u8; published];
        let reference = store.publish(&values).unwrap();
        assert_eq!(store.usage().reserved_bytes, capacity);
        aliases.push((reference, values));
        for (reference, values) in &aliases {
            assert_eq!(store.read(reference).unwrap(), values);
        }
        let usage = store.usage();
        snapshots.push(json!({"step": step, "elements": usage.elements,
            "buffers": usage.buffers, "reserved_bytes": usage.reserved_bytes}));
    }
    json!({"layout": name, "scenario": scenario, "reservations": batches, "snapshots": snapshots})
}

fn main() {
    let scenarios = [
        ("full-reservations", vec![(64, 64); 8]),
        (
            "retained-spare",
            vec![(100, 1), (200, 1), (400, 1), (800, 1)],
        ),
        (
            "table-and-prefixes",
            vec![(4096, 4096), (64, 3), (128, 5), (256, 8)],
        ),
    ];
    let mut results = Vec::new();
    for (name, batches) in scenarios {
        results.push(measure(
            "packed",
            name,
            PackedBuffers::new().unwrap(),
            &batches,
        ));
        results.push(measure(
            "segmented",
            name,
            SegmentedBuffers::new().unwrap(),
            &batches,
        ));
    }
    println!("{}", serde_json::to_string_pretty(&json!({
        "scope": "Retained payload and descriptor capacities; excludes allocator bookkeeping and probe allocations. No latency or speedup claim.",
        "results": results
    })).unwrap());
}
