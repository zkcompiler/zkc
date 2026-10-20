//! Static attribute validation at the reached invocation's original check point.
use crate::{Result, ark, refused};
use zkc_runtime::vm::{AttributeRule, BoundSignature, Invocation, OperationBinding};

/// Backend-owned static call facts, including immutable decoded scalar literals.
/// Typed payloads require equal declarations, signatures and attributes. Actual
/// operands, policy, domain, setup, custody and budgets remain invocation facts.
pub struct NativeCall {
    rule: AttributeRule,
    attributes: Box<[String]>,
    // A decoded payload only; the reached invocation still checks its binding.
    unsigned64: Option<u64>,
    expression: Option<Box<ExpressionCall>>,
    literal: Option<Box<LiteralCall>>,
}
struct LiteralCall {
    binding: OperationBinding,
    signature: BoundSignature,
    value: crate::Value,
}
struct ExpressionCall {
    binding: OperationBinding,
    signature: BoundSignature,
    plan: crate::numerical::expression::Prepared,
}

impl NativeCall {
    pub(super) fn prepare_invocation(slot: &mut Option<Self>, i: &Invocation<'_>) -> Result<()> {
        let rule = i.binding.signature().attributes;
        // The linked signature already fixes attribute interpretation. Keep
        // attribute-free operations on the ordinary preparation fast path.
        if rule == AttributeRule::None {
            return Self::prepare(slot, rule, i.attributes);
        }
        if i.binding.declaration().contract == "field.constant" {
            return Self::prepare_literal(
                slot,
                i.binding.declaration(),
                i.binding.signature(),
                i.attributes,
            );
        }
        if rule != AttributeRule::NumericalExpression {
            return Self::prepare(slot, rule, i.attributes);
        }
        Self::prepare_expression(
            slot,
            i.binding.declaration(),
            i.binding.signature(),
            i.attributes,
        )
    }

    fn prepare_literal(
        slot: &mut Option<Self>,
        binding: &OperationBinding,
        signature: &BoundSignature,
        attributes: &[String],
    ) -> Result<()> {
        if slot.as_ref().is_some_and(|call| {
            call.rule == signature.attributes
                && call.attributes.as_ref() == attributes
                && call.literal.as_ref().is_some_and(|literal| {
                    literal.binding == *binding && literal.signature == *signature
                })
        }) {
            return Ok(());
        }
        let field = signature
            .outputs
            .first()
            .ok_or_else(|| refused("kernel-operands"))?
            .logical()
            .identity();
        let value = crate::kernels::field::decode_literal(field, attributes)?;
        // Failed decoding must neither publish a partial replacement nor use
        // the previous successful scalar for this invocation.
        *slot = Some(Self {
            rule: signature.attributes,
            attributes: attributes.into(),
            unsigned64: None,
            expression: None,
            literal: Some(Box::new(LiteralCall {
                binding: binding.clone(),
                signature: signature.clone(),
                value,
            })),
        });
        Ok(())
    }

    pub(super) fn literal(&self) -> Result<&crate::Value> {
        self.literal
            .as_ref()
            .map(|literal| &literal.value)
            .ok_or_else(|| refused("kernel-preparation"))
    }

    fn prepare_expression(
        slot: &mut Option<Self>,
        binding: &OperationBinding,
        signature: &BoundSignature,
        attributes: &[String],
    ) -> Result<()> {
        let rule = AttributeRule::NumericalExpression;
        if slot.as_ref().is_some_and(|call| {
            call.rule == rule
                && call.attributes.as_ref() == attributes
                && call.expression.as_ref().is_some_and(|expression| {
                    expression.binding == *binding && expression.signature == *signature
                })
        }) {
            return Ok(());
        }
        let plan = crate::numerical::expression::prepare(binding, signature, attributes)?;
        *slot = Some(Self {
            rule,
            attributes: attributes.into(),
            unsigned64: None,
            expression: Some(Box::new(ExpressionCall {
                binding: binding.clone(),
                signature: signature.clone(),
                plan,
            })),
            literal: None,
        });
        Ok(())
    }

    pub(super) fn expression(&self) -> Result<&crate::numerical::expression::Prepared> {
        self.expression
            .as_ref()
            .map(|expression| &expression.plan)
            .ok_or_else(|| refused("kernel-preparation"))
    }

    pub(super) fn unsigned64(&self) -> Result<u64> {
        self.unsigned64.ok_or_else(|| refused("kernel-preparation"))
    }

    pub(super) fn prepare(
        slot: &mut Option<Self>,
        rule: AttributeRule,
        attributes: &[String],
    ) -> Result<()> {
        // No storage or interpretation is needed for an empty attribute list.
        if rule == AttributeRule::None && attributes.is_empty() {
            return Ok(());
        }
        if slot
            .as_ref()
            .is_some_and(|call| call.rule == rule && call.attributes.as_ref() == attributes)
        {
            return Ok(());
        }
        let unsigned64 = if rule == AttributeRule::Unsigned64 {
            Some(
                crate::kernels::indices::decode_unsigned64(attributes)
                    .ok_or_else(|| refused("kernel-attributes"))?,
            )
        } else {
            Self::check(rule, attributes)?;
            None
        };
        *slot = Some(Self {
            rule,
            attributes: attributes.into(),
            unsigned64,
            expression: None,
            literal: None,
        });
        Ok(())
    }
    pub(super) fn check(rule: AttributeRule, attributes: &[String]) -> Result<()> {
        use zkc_runtime::vm::Identity;
        let field = match rule {
            AttributeRule::FieldDecimal => Some(Identity::Bls12381Fr),
            AttributeRule::Bn254Decimal => Some(Identity::Bn254Fr),
            AttributeRule::RistrettoDecimal => Some(Identity::Ristretto255Scalar),
            AttributeRule::KoalaBearDecimal => Some(Identity::KoalaBear),
            AttributeRule::Binary64Literal => Some(Identity::Binary64),
            AttributeRule::Binary64Ext3Literal => Some(Identity::Binary64Ext3),
            _ => None,
        };
        if let Some(field) = field {
            return crate::kernels::field::decode_literal(field, attributes).map(|_| ());
        }
        match rule {
            AttributeRule::None if attributes.is_empty() => (),
            AttributeRule::Unsigned64 => {
                crate::kernels::indices::decode_unsigned64(attributes)
                    .ok_or_else(|| refused("kernel-attributes"))?;
            }
            AttributeRule::NaturalIndex if attributes.len() == 1 => {
                zkc_runtime::logical::natural_index(&attributes[0])
                    .map_err(|_| refused("kernel-attributes"))?;
            }
            AttributeRule::NaturalIndices
                if attributes
                    .iter()
                    .all(|a| zkc_runtime::logical::natural_index(a).is_ok()) => {}
            AttributeRule::ScatterShape
                if !attributes.is_empty()
                    && attributes
                        .iter()
                        .all(|a| zkc_runtime::logical::natural_index(a).is_ok()) => {}
            AttributeRule::Bn254Decimals => {
                for literal in attributes {
                    crate::parse_bn254_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::FieldDecimals => {
                for literal in attributes {
                    zkc_arkworks::parse_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::RistrettoDecimals => {
                for literal in attributes {
                    crate::parse_ristretto_decimal(literal)?;
                }
            }
            AttributeRule::KoalaBearDecimals => {
                for literal in attributes {
                    let _ = crate::plonky3::parse_decimal(literal)?;
                }
            }
            AttributeRule::MatrixIdentity | AttributeRule::AssetIdentity
                if attributes.len() == 1
                    && attributes[0].len() == 64
                    && attributes[0]
                        .bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) => {}
            AttributeRule::MatrixDimensions
                if attributes.len() == 2
                    && attributes.iter().all(|a| {
                        zkc_runtime::logical::natural_index(a).is_ok_and(|n| n <= 65536)
                    }) => {}
            AttributeRule::MatrixShape
                if attributes.len() == 3
                    && attributes
                        .iter()
                        .all(|a| zkc_runtime::logical::natural_index(a).is_ok())
                    && matches!(attributes[2].as_str(), "0" | "1") => {}
            AttributeRule::Binary64Literals => {
                for literal in attributes {
                    let _ = crate::plonky3::binary::parse_literal(literal)?;
                }
            }
            AttributeRule::Binary64Ext3Literals => {
                for literal in attributes {
                    let _ = crate::plonky3::binary::parse_ext3_literal(literal)?;
                }
            }
            AttributeRule::NativeMessageTemplate => {
                zkc_runtime::logical::native_origin_template(attributes, "message")
                    .map_err(|_| refused("kernel-attributes"))?;
            }
            // The query's source method separates field and index transitions.
            AttributeRule::NativeChallengeTemplate | AttributeRule::NativeIndexTemplate => {
                let method = if rule == AttributeRule::NativeIndexTemplate {
                    "index"
                } else {
                    "draw"
                };
                zkc_runtime::logical::native_query_template(attributes, method)
                    .map_err(|_| refused("kernel-attributes"))?;
            }

            _ => return Err(refused("kernel-attributes")),
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "literal_tests.rs"]
mod literal_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preparation_reuses_only_equal_static_facts() {
        let mut call = None;
        let attributes = vec!["12".into()];
        NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &attributes).unwrap();
        let storage = call.as_ref().unwrap().attributes.as_ptr();
        assert_eq!(call.as_ref().unwrap().unsigned64().unwrap(), 12);
        NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &attributes).unwrap();
        assert_eq!(storage, call.as_ref().unwrap().attributes.as_ptr());

        // A cache hit never licenses another spelling or another rule.
        for invalid in [
            vec!["012".into()],
            vec!["-1".into()],
            vec!["+12".into()],
            vec!["12 ".into()],
            vec!["18446744073709551616".into()],
            vec!["12".into(), "13".into()],
            vec![],
        ] {
            let direct = NativeCall::prepare(&mut None, AttributeRule::Unsigned64, &invalid);
            let prepared = NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &invalid);
            assert_eq!(direct, prepared);
            assert!(prepared.is_err());
            assert_eq!(storage, call.as_ref().unwrap().attributes.as_ptr());
            assert_eq!(call.as_ref().unwrap().unsigned64().unwrap(), 12);
        }
        assert!(NativeCall::prepare(&mut call, AttributeRule::None, &attributes).is_err());
        NativeCall::prepare(&mut call, AttributeRule::NaturalIndices, &attributes).unwrap();
        assert_eq!(call.as_ref().unwrap().rule, AttributeRule::NaturalIndices);
        assert_eq!(
            call.as_ref().unwrap().unsigned64(),
            Err(refused("kernel-preparation"))
        );
        for (literal, expected) in [("0", 0), ("19", 19), ("18446744073709551615", u64::MAX)] {
            NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &[literal.into()]).unwrap();
            assert_eq!(call.as_ref().unwrap().unsigned64().unwrap(), expected);
        }
    }

    #[test]
    fn no_attributes_need_no_preparation_storage() {
        let mut call = None;
        NativeCall::prepare(&mut call, AttributeRule::None, &[]).unwrap();
        assert!(call.is_none());
    }

    #[test]
    fn expression_preparation_refuses_representation_changes_and_preserves_warmed_plan() {
        use serde_json::json;
        use zkc_runtime::vm::{PhysicalType, Representation};

        let binding = OperationBinding {
            contract: "numerical.map".into(),
            arguments: vec!["bls12-381.fr".into(), "1".into()],
            implementation: "arkworks/numerical.map".into(),
        };
        let attributes =
            vec![json!(["zkc.ring/0", ["bls12-381.fr"], [["input", 0]], [0]]).to_string()];
        let ports = binding.signature().unwrap();
        let mut slot = None;
        NativeCall::prepare_expression(&mut slot, &binding, &ports, &attributes).unwrap();
        let storage = slot.as_ref().unwrap().attributes.as_ptr();
        let plan = std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap());
        NativeCall::prepare_expression(&mut slot, &binding, &ports, &attributes).unwrap();
        assert_eq!(
            plan,
            std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
        );

        for input in [true, false] {
            let mut wrong_ports = ports.clone();
            let port = if input {
                &mut wrong_ports.inputs[1]
            } else {
                &mut wrong_ports.outputs[0]
            };
            let original = port.clone();
            *port = PhysicalType::new(original.logical(), Representation::FrDiagonal).unwrap();
            assert_eq!(port.logical(), original.logical());
            assert_ne!(*port, original);
            assert_eq!(
                NativeCall::prepare_expression(&mut slot, &binding, &wrong_ports, &attributes),
                Err(refused("numerical-binding"))
            );
            let retained = slot.as_ref().unwrap();
            assert_eq!(storage, retained.attributes.as_ptr());
            assert_eq!(plan, std::ptr::from_ref(retained.expression().unwrap()));
            assert_eq!(retained.expression.as_ref().unwrap().signature, ports);

            NativeCall::prepare_expression(&mut slot, &binding, &ports, &attributes).unwrap();
            assert_eq!(
                plan,
                std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
            );
        }
    }

    #[test]
    fn expression_preparation_keys_exact_binding_body_and_representations() {
        use serde_json::json;
        let mut binding = OperationBinding {
            contract: "numerical.map".into(),
            arguments: vec!["koala-bear".into(), "1".into()],
            implementation: "plonky3/numerical.map".into(),
        };
        let attributes =
            vec![json!(["zkc.ring/0", ["koala-bear"], [["input", 0]], [0]]).to_string()];
        let ports = binding.signature().unwrap();
        let mut slot = None;
        NativeCall::prepare_expression(&mut slot, &binding, &ports, &attributes).unwrap();
        let storage = slot.as_ref().unwrap().attributes.as_ptr();
        NativeCall::prepare_expression(&mut slot, &binding, &ports, &attributes).unwrap();
        assert_eq!(storage, slot.as_ref().unwrap().attributes.as_ptr());
        let mut wrong_ports = ports.clone();
        wrong_ports.outputs[0] = ports.inputs[0].clone();
        assert!(
            NativeCall::prepare_expression(&mut slot, &binding, &wrong_ports, &attributes).is_err()
        );
        assert_eq!(storage, slot.as_ref().unwrap().attributes.as_ptr());
        let changed =
            vec![attributes[0].replace("[\"input\",0]", "[\"constant\",\"koala-bear\",\"1\"]")];
        NativeCall::prepare_expression(&mut slot, &binding, &ports, &changed).unwrap();
        assert_ne!(storage, slot.as_ref().unwrap().attributes.as_ptr());
        assert_eq!(
            slot.as_ref().unwrap().attributes.as_ref(),
            changed.as_slice()
        );

        // Equal body text and field do not identify the operand roles or sink.
        let previous = slot.as_ref().unwrap().attributes.as_ptr();
        binding.arguments[1] = "0".into();
        NativeCall::prepare_expression(
            &mut slot,
            &binding,
            &binding.signature().unwrap(),
            &changed,
        )
        .unwrap();
        assert_ne!(previous, slot.as_ref().unwrap().attributes.as_ptr());
        let previous = slot.as_ref().unwrap().attributes.as_ptr();
        binding.contract = "numerical.sum".into();
        binding.implementation = "plonky3/numerical.sum".into();
        NativeCall::prepare_expression(
            &mut slot,
            &binding,
            &binding.signature().unwrap(),
            &changed,
        )
        .unwrap();
        assert_ne!(previous, slot.as_ref().unwrap().attributes.as_ptr());

        let previous = slot.as_ref().unwrap().attributes.as_ptr();
        binding.arguments[0] = "koala-bear.ext4-binomial3".into();
        assert!(
            NativeCall::prepare_expression(
                &mut slot,
                &binding,
                &binding.signature().unwrap(),
                &changed
            )
            .is_err()
        );
        assert_eq!(previous, slot.as_ref().unwrap().attributes.as_ptr());
        assert_eq!(
            slot.as_ref()
                .unwrap()
                .expression
                .as_ref()
                .unwrap()
                .binding
                .arguments[0],
            "koala-bear"
        );
    }
}
