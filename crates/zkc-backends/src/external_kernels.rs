//! Bounded explicit external data-state contracts. See the owning specification
//! docs/spec/realization/external-constructions.md. These are not affine internal
//! transcript resources, and do not advertise automatic Fiat-Shamir rules.
use crate::external::{Work, monero, openvm};
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Type,
};

const MAGIC: u64 = 1_514_881_876;
const VERSION: u64 = 1;

pub(crate) struct Budget {
    pub limit: u64,
    pub spent: u64,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            limit: 16_777_216,
            spent: 0,
        }
    }
}
impl Budget {
    // Deliberately a logical work metric, not cycles or cryptographic security.
    fn charge(&mut self, work: Work) -> Result<()> {
        let cost = work.units().map_err(primitive)?;
        // A sum past u64 is past any limit.
        let next = self
            .spent
            .checked_add(cost)
            .filter(|next| *next <= self.limit)
            .ok_or_else(|| exhausted("external-work-limit"))?;
        self.spent = next;
        Ok(())
    }
}

pub(crate) fn signature(b: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Index, Indices};
    if !b.arguments.is_empty() || b.implementation != format!("native/{}", b.contract) {
        return None;
    }
    // Independent of the compiler and runtime admission tables.
    let (ins, outs): (&[Type], &[Type]) = match b.contract.as_str() {
        "external.monero.init" | "external.monero.hash" => (&[Indices], &[Indices]),
        "external.monero.update" => (&[Indices, Indices], &[Indices, Indices]),
        "external.openvm.init" => (&[], &[Indices]),
        "external.openvm.observe" => (&[Indices, Indices], &[Indices]),
        "external.openvm.sample" => (&[Indices], &[Indices, Index]),
        "external.openvm.sample_ext" => (&[Indices], &[Indices, Indices]),
        "external.openvm.sample_bits" => (&[Indices, Index], &[Indices, Index]),
        "external.openvm.check_witness" => (&[Indices, Index, Index], &[Indices, Bool]),
        _ => return None,
    };
    let port = |kind| {
        PhysicalType::default_for(LogicalType::new(kind, Identity::None).expect("data state port"))
    };
    Some(KernelSignature {
        inputs: ins.iter().copied().map(port).collect(),
        outputs: outs.iter().copied().map(port).collect(),
        attributes: AttributeRule::None,
    })
}
fn vector(v: &Value) -> Result<&[u64]> {
    if let Value::Indices(v) = v {
        Ok(v)
    } else {
        Err(refused("external-operands"))
    }
}
fn index(v: &Value) -> Result<u32> {
    if let Value::Index(v) = v {
        u32::try_from(*v).map_err(|_| refused("external-u32"))
    } else {
        Err(refused("external-operands"))
    }
}
fn bytes(v: &[u64]) -> Result<Vec<u8>> {
    v.iter()
        .map(|x| u8::try_from(*x).map_err(|_| refused("external-byte")))
        .collect()
}
fn words(v: &[u64]) -> Result<Vec<monero::Word>> {
    if !v.len().is_multiple_of(32) {
        return Err(refused("external-word-width"));
    }
    Ok(bytes(v)?.as_chunks::<32>().0.to_vec())
}
fn payload(v: &[u64], suite: u64, width: usize) -> Result<&[u64]> {
    if v.len() != width + 3 {
        return Err(refused("external-state-width"));
    }
    if v[..3] != [MAGIC, VERSION, suite] {
        return Err(refused("external-state-suite"));
    }
    Ok(&v[3..])
}
fn encoded(suite: u64, data: impl IntoIterator<Item = u64>) -> Value {
    Value::Indices(
        [MAGIC, VERSION, suite]
            .into_iter()
            .chain(data)
            .collect::<Vec<_>>()
            .into(),
    )
}
fn raw(word: monero::Word) -> Value {
    Value::Indices(word.into_iter().map(u64::from).collect::<Vec<_>>().into())
}
fn duplex(v: &Value) -> Result<openvm::Duplex> {
    let v = payload(vector(v)?, 2, 18)?;
    let state: Vec<u32> = v[..16]
        .iter()
        .map(|x| u32::try_from(*x).map_err(|_| refused("external-noncanonical-field")))
        .collect::<Result<_>>()?;
    if state.iter().any(|x| *x >= openvm::MODULUS) {
        return Err(refused("external-noncanonical-field"));
    }
    if v[16] >= 8 || v[17] > 8 {
        return Err(refused("external-state-index"));
    }
    openvm::Duplex::from_snapshot(openvm::Snapshot {
        state: state.try_into().expect("state width"),
        absorb_index: v[16] as usize,
        sample_index: v[17] as usize,
    })
    .map_err(primitive)
}
fn packed(d: &openvm::Duplex) -> Value {
    let s = d.snapshot();
    encoded(
        2,
        s.state
            .into_iter()
            .map(u64::from)
            .chain([s.absorb_index as u64, s.sample_index as u64]),
    )
}
fn primitive(e: crate::external::Error) -> zkc_runtime::interactive::BackendError {
    let code = e.code().replacen("external:", "external-", 1);
    // A size past u64 exhausts the work that could be done; it is one form
    // wherever it arises, as the runtime's own size overflows are.
    if e == crate::external::Error::SizeOverflow {
        exhausted(&code)
    } else {
        refused(&code)
    }
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attrs: &[String],
    p: &Policy,
    available: usize,
    budget: &mut Budget,
) -> Option<Result<Vec<Value>>> {
    if !name.starts_with("external.") {
        return None;
    }
    Some((|| {
        if !attrs.is_empty() {
            return Err(refused("external-attributes"));
        }
        // All input and output allocation bounds precede cryptographic work.
        for arg in args {
            if let Value::Indices(xs) = arg {
                p.vector_width(xs.len(), 8)?;
            }
        }
        let widths: &[usize] = match name {
            "external.monero.init" => &[35],
            "external.monero.hash" => &[32],
            "external.monero.update" => &[35, 32],
            "external.openvm.init" | "external.openvm.observe" => &[21],
            "external.openvm.sample_ext" => &[21, 4],
            "external.openvm.sample"
            | "external.openvm.sample_bits"
            | "external.openvm.check_witness" => &[21, 0],
            _ => return Err(refused("external-contract")),
        };
        let mut total = 0usize;
        for &width in widths {
            // Zero denotes a scalar port: the native value carrier charges
            // 512 bytes for an index/bool, not one eight-byte vector element.
            let bytes = if width == 0 {
                512
            } else {
                p.vector_width(width, 8)?;
                size(width, 8)?
            };
            total = total
                .checked_add(bytes)
                .ok_or_else(|| exhausted("size-overflow"))?;
        }
        p.output(total, available)?;
        match (name, args) {
            ("external.monero.init", [v]) => {
                let v = vector(v)?;
                if v.len() != 32 {
                    return Err(refused("external-word-width"));
                }
                bytes(v)?;
                Ok(vec![encoded(1, v.iter().copied())])
            }
            ("external.monero.hash", [v]) => {
                let words = words(vector(v)?)?;
                budget.charge(monero::hash_work(words.len(), false).map_err(primitive)?)?;
                Ok(vec![raw(monero::hash_to_scalar(&words))])
            }
            ("external.monero.update", [s, v]) => {
                let state = bytes(payload(vector(s)?, 1, 32)?)?
                    .try_into()
                    .expect("state width");
                let words = words(vector(v)?)?;
                budget.charge(monero::hash_work(words.len(), true).map_err(primitive)?)?;
                let next = monero::HashChain::new(state).update(&words);
                Ok(vec![encoded(1, next.into_iter().map(u64::from)), raw(next)])
            }
            ("external.openvm.init", []) => Ok(vec![packed(&openvm::Duplex::new())]),
            ("external.openvm.observe", [s, v]) => {
                let mut d = duplex(s)?;
                let values = vector(v)?
                    .iter()
                    .map(|x| {
                        u32::try_from(*x)
                            .ok()
                            .filter(|x| *x < openvm::MODULUS)
                            .ok_or_else(|| refused("external-noncanonical-field"))
                    })
                    .collect::<Result<Vec<_>>>()?;
                budget.charge(d.observe_work(values.len()).map_err(primitive)?)?;
                d.observe(&values).map_err(primitive)?;
                Ok(vec![packed(&d)])
            }
            ("external.openvm.sample", [s]) => {
                let mut d = duplex(s)?;
                budget.charge(d.sample_work(1).map_err(primitive)?)?;
                let v = d.sample().value;
                Ok(vec![packed(&d), Value::Index(v.into())])
            }
            ("external.openvm.sample_ext", [s]) => {
                let mut d = duplex(s)?;
                budget.charge(d.sample_work(4).map_err(primitive)?)?;
                let v = d.sample_ext().value;
                Ok(vec![
                    packed(&d),
                    Value::Indices(v.into_iter().map(u64::from).collect::<Vec<_>>().into()),
                ])
            }
            ("external.openvm.sample_bits", [s, b]) => {
                let mut d = duplex(s)?;
                let bits = index(b)?;
                openvm::validate_bits(bits).map_err(primitive)?;
                budget.charge(d.sample_work(1).map_err(primitive)?)?;
                let v = d.sample_bits(bits).map_err(primitive)?.value;
                Ok(vec![packed(&d), Value::Index(v.into())])
            }
            ("external.openvm.check_witness", [s, b, w]) => {
                let mut d = duplex(s)?;
                let bits = index(b)?;
                openvm::validate_bits(bits).map_err(primitive)?;
                let witness = index(w)?;
                openvm::validate_field(witness).map_err(primitive)?;
                budget.charge(d.witness_work(bits).map_err(primitive)?)?;
                let v = d.check_witness(bits, witness).map_err(primitive)?.value;
                Ok(vec![packed(&d), Value::Bool(v)])
            }
            _ => Err(refused("external-operands")),
        }
    })())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn run(name: &str, args: &[Value], budget: &mut Budget) -> Result<Vec<Value>> {
        apply(name, args, &[], &Policy::default(), usize::MAX, budget).expect("external contract")
    }
    fn ns(xs: Vec<u64>) -> Value {
        Value::Indices(xs.into())
    }
    #[test]
    fn exact_work_precharge_and_output_failure() {
        let mut budget = Budget {
            limit: 32,
            spent: 0,
        };
        let state = encoded(1, [0; 32]);
        let args = [state, ns(vec![])];
        // Empty update hashes 32 state bytes and performs one hash call.
        assert_eq!(
            run("external.monero.update", &args, &mut budget)
                .unwrap_err()
                .code,
            "exhausted:external-work-limit"
        );
        assert_eq!(budget.spent, 0);
        budget.limit = 33;
        let out = run("external.monero.update", &args, &mut budget).unwrap();
        assert_eq!(budget.spent, 33);
        assert_ne!(vector(&out[0]).unwrap(), vector(&args[0]).unwrap());
        assert_eq!(
            run("external.monero.update", &args, &mut budget)
                .unwrap_err()
                .code,
            "exhausted:external-work-limit"
        );
        assert_eq!(budget.spent, 33); // copied states do not refund work
        let mut fresh = Budget::default();
        assert_eq!(
            apply(
                "external.monero.update",
                &args,
                &[],
                &Policy::default(),
                0,
                &mut fresh
            )
            .unwrap()
            .unwrap_err()
            .code,
            "exhausted:output-bytes"
        );
        assert_eq!(fresh.spent, 0);
        // State = 424 bytes, scalar = 512. An intermediate cap must fail
        // before the permutation, not only during adapter output validation.
        let state = packed(&openvm::Duplex::new());
        assert_eq!(
            apply(
                "external.openvm.sample",
                &[state],
                &[],
                &Policy::default(),
                800,
                &mut fresh
            )
            .unwrap()
            .unwrap_err()
            .code,
            "exhausted:output-bytes"
        );
        assert_eq!(fresh.spent, 0);
    }
    // Admission and the adapter's signature check refuse these shapes before a
    // kernel runs; the kernel still refuses them on its own.
    #[test]
    fn malformed_invocations_are_refused_by_the_kernel_itself() {
        let mut budget = Budget::default();
        let state = packed(&openvm::Duplex::new());
        let refusal = |name: &str, args: &[Value], attrs: &[String], budget: &mut Budget| {
            apply(name, args, attrs, &Policy::default(), usize::MAX, budget)
                .expect("external contract")
                .unwrap_err()
                .code
        };
        assert_eq!(
            refusal("external.openvm.init", &[], &["x".into()], &mut budget),
            "refused:external-attributes"
        );
        assert_eq!(
            refusal("external.nope", &[], &[], &mut budget),
            "refused:external-contract"
        );
        for (name, args) in [
            // An operand count no contract row accepts.
            ("external.openvm.init", vec![ns(vec![])]),
            // A scalar where the hash expects bytes.
            ("external.monero.hash", vec![Value::Bool(true)]),
            // A vector where the bit count is a scalar.
            (
                "external.openvm.sample_bits",
                vec![state.clone(), ns(vec![])],
            ),
        ] {
            assert_eq!(
                refusal(name, &args, &[], &mut budget),
                "refused:external-operands",
                "{name}"
            );
        }
        assert_eq!(budget.spent, 0);
    }
    #[test]
    fn indices_outside_u32_are_refused_before_bit_width_or_field_checks() {
        let mut budget = Budget::default();
        let state = packed(&openvm::Duplex::new());
        for (name, args) in [
            (
                "external.openvm.sample_bits",
                vec![state.clone(), Value::Index(1 << 32)],
            ),
            (
                "external.openvm.check_witness",
                vec![state.clone(), Value::Index(3), Value::Index(1 << 32)],
            ),
        ] {
            assert_eq!(
                run(name, &args, &mut budget).unwrap_err().code,
                "refused:external-u32",
                "{name}"
            );
        }
        assert_eq!(budget.spent, 0);
    }
    #[test]
    fn work_metric_overflow_is_exhaustion_and_charges_nothing() {
        let mut budget = Budget::default();
        let overflowing = Work {
            hash_calls: u64::MAX,
            hash_bytes: 1,
            ..Work::default()
        };
        assert_eq!(
            budget.charge(overflowing).unwrap_err().code,
            "exhausted:external-size-overflow"
        );
        assert_eq!(
            primitive(crate::external::Error::SizeOverflow).code,
            "exhausted:external-size-overflow"
        );
        assert_eq!(budget.spent, 0);
        let mut saturated = Budget {
            limit: u64::MAX,
            spent: u64::MAX,
        };
        let one = Work {
            hash_calls: 1,
            ..Work::default()
        };
        assert_eq!(
            saturated.charge(one).unwrap_err().code,
            "exhausted:external-work-limit"
        );
        assert_eq!(saturated.spent, u64::MAX);
    }
    #[test]
    fn stateless_empty_hash_and_reachable_snapshot_roundtrip() {
        let mut budget = Budget::default();
        let out = run("external.monero.hash", &[ns(vec![])], &mut budget).unwrap();
        assert_eq!(
            vector(&out[0]).unwrap(),
            monero::hash_to_scalar(&[]).map(u64::from)
        );
        assert_eq!(budget.spent, 1);
        let mut expected = openvm::Duplex::new();
        expected.observe(&[1, 2, 3]).unwrap();
        let input = packed(&expected);
        let actual = run("external.openvm.sample", &[input], &mut budget).unwrap();
        let sampled = expected.sample().value;
        assert_eq!(
            vector(&actual[0]).unwrap(),
            vector(&packed(&expected)).unwrap()
        );
        assert!(matches!(actual[1],Value::Index(x) if x==u64::from(sampled)));
    }
    #[test]
    fn zero_difficulty_and_failed_direct_witness_state() {
        let mut budget = Budget::default();
        let state = packed(&openvm::Duplex::new());
        let out = run(
            "external.openvm.check_witness",
            &[state.clone(), Value::Index(0), Value::Index(5)],
            &mut budget,
        )
        .unwrap();
        assert_eq!(vector(&out[0]).unwrap(), vector(&state).unwrap());
        assert!(matches!(out[1], Value::Bool(true)));
        assert_eq!(budget.spent, 0);
        let failed = run(
            "external.openvm.check_witness",
            &[state.clone(), Value::Index(30), Value::Index(5)],
            &mut budget,
        )
        .unwrap();
        assert!(matches!(failed[1], Value::Bool(false)));
        assert_ne!(vector(&failed[0]).unwrap(), vector(&state).unwrap());
        assert_eq!(budget.spent, 3);
        // The input's immutable value still denotes a legitimate trial copy.
        let trial = run(
            "external.openvm.check_witness",
            &[state, Value::Index(30), Value::Index(5)],
            &mut budget,
        )
        .unwrap();
        assert_eq!(vector(&trial[0]).unwrap(), vector(&failed[0]).unwrap());
        assert_eq!(budget.spent, 6);
    }
}
