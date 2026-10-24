//! Static attribute validation at the reached invocation's original check point.
use super::CallBinding;
use crate::{Result, ark, refused};
use std::sync::Arc;
use zkc_runtime::vm::AttributeRule;

/// Backend-owned static call facts, including immutable decoded typed literals.
/// Typed payloads require equal declarations, signatures and attributes. Actual
/// operands, policy, domain, setup, custody and budgets remain invocation facts.
pub struct NativeCall {
    rule: AttributeRule,
    attributes: Box<[String]>,
    payload: CallPayload,
}
enum CallPayload {
    Attributes,
    // A decoded payload only; the reached invocation still checks its binding.
    Unsigned64(u64),
    Expression(Box<ExpressionCall>),
    Literal(Box<LiteralCall>),
}
struct LiteralCall {
    binding: Arc<CallBinding>,
    value: crate::Value,
}
struct ExpressionCall {
    binding: Arc<CallBinding>,
    plan: crate::numerical::expression::Prepared,
}

impl NativeCall {
    pub(super) fn prepare_invocation(
        slot: &mut Option<Self>,
        binding: &Arc<CallBinding>,
        attributes: &[String],
        policy: &crate::Policy,
        available: usize,
    ) -> Result<()> {
        let rule = binding.signature.attributes;
        // The linked signature already fixes attribute interpretation. Keep
        // attribute-free operations on the ordinary preparation fast path.
        if rule == AttributeRule::None {
            return Self::prepare(slot, rule, attributes);
        }
        if matches!(
            binding.declaration.contract.as_str(),
            "field.constant" | "vector.constant"
        ) {
            return Self::prepare_literal(slot, binding, attributes, policy, available);
        }
        if rule != AttributeRule::NumericalExpression {
            return Self::prepare(slot, rule, attributes);
        }
        Self::prepare_expression(slot, binding, attributes)
    }

    fn prepare_literal(
        slot: &mut Option<Self>,
        binding: &Arc<CallBinding>,
        attributes: &[String],
        policy: &crate::Policy,
        available: usize,
    ) -> Result<()> {
        let signature = &binding.signature;
        if slot.as_ref().is_some_and(|call| {
            call.rule == signature.attributes
                && call.attributes.as_ref() == attributes
                && matches!(&call.payload, CallPayload::Literal(literal)
                    if literal.binding == *binding)
        }) {
            return Ok(());
        }
        let output = signature
            .outputs
            .first()
            .ok_or_else(|| refused("kernel-operands"))?;
        let value = crate::operations::literal::prepare(output, attributes, policy, available)?;
        // Failed decoding must neither publish a partial replacement nor use
        // the previous successful literal for this invocation.
        *slot = Some(Self {
            rule: signature.attributes,
            attributes: attributes.into(),
            payload: CallPayload::Literal(Box::new(LiteralCall {
                binding: Arc::clone(binding),
                value,
            })),
        });
        Ok(())
    }

    pub(super) fn literal(&self) -> Result<&crate::Value> {
        match &self.payload {
            CallPayload::Literal(literal) => Ok(&literal.value),
            _ => Err(refused("kernel-preparation")),
        }
    }

    fn prepare_expression(
        slot: &mut Option<Self>,
        binding: &Arc<CallBinding>,
        attributes: &[String],
    ) -> Result<()> {
        let rule = AttributeRule::NumericalExpression;
        if slot.as_ref().is_some_and(|call| {
            call.rule == rule
                && call.attributes.as_ref() == attributes
                && matches!(&call.payload, CallPayload::Expression(expression)
                    if expression.binding == *binding)
        }) {
            return Ok(());
        }
        let plan = crate::numerical::expression::prepare(
            &binding.declaration,
            &binding.signature,
            attributes,
        )?;
        *slot = Some(Self {
            rule,
            attributes: attributes.into(),
            payload: CallPayload::Expression(Box::new(ExpressionCall {
                binding: Arc::clone(binding),
                plan,
            })),
        });
        Ok(())
    }

    pub(super) fn expression(&self) -> Result<&crate::numerical::expression::Prepared> {
        match &self.payload {
            CallPayload::Expression(expression) => Ok(&expression.plan),
            _ => Err(refused("kernel-preparation")),
        }
    }

    pub(super) fn unsigned64(&self) -> Result<u64> {
        match &self.payload {
            CallPayload::Unsigned64(value) => Ok(*value),
            _ => Err(refused("kernel-preparation")),
        }
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
        let payload = if rule == AttributeRule::Unsigned64 {
            CallPayload::Unsigned64(
                crate::operations::indices::decode_unsigned64(attributes)
                    .ok_or_else(|| refused("kernel-attributes"))?,
            )
        } else {
            Self::check(rule, attributes)?;
            CallPayload::Attributes
        };
        *slot = Some(Self {
            rule,
            attributes: attributes.into(),
            payload,
        });
        Ok(())
    }
    pub(super) fn check(rule: AttributeRule, attributes: &[String]) -> Result<()> {
        use zkc_runtime::vm::Identity;
        let field = match rule {
            AttributeRule::ResidueLiteral(field) => Some(field),
            AttributeRule::FieldDecimal => Some(Identity::Bls12381Fr),
            AttributeRule::Bn254Decimal => Some(Identity::Bn254Fr),
            AttributeRule::RistrettoDecimal => Some(Identity::Ristretto255Scalar),
            AttributeRule::KoalaBearDecimal => Some(Identity::KoalaBear),
            AttributeRule::Binary64Literal => Some(Identity::Binary64),
            AttributeRule::Binary64Ext3Literal => Some(Identity::Binary64Ext3),
            _ => None,
        };
        if let Some(field) = field {
            return crate::operations::field::decode_literal(field, attributes).map(|_| ());
        }
        match rule {
            AttributeRule::None if attributes.is_empty() => (),
            AttributeRule::Unsigned64 => {
                crate::operations::indices::decode_unsigned64(attributes)
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
            AttributeRule::ResidueLiterals(field) => {
                for literal in attributes {
                    crate::operations::field::decode_literal(field, std::slice::from_ref(literal))?;
                }
            }
            AttributeRule::Bn254Decimals => {
                for literal in attributes {
                    zkc_kernels::arkworks::bn254::parse_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::FieldDecimals => {
                for literal in attributes {
                    zkc_kernels::arkworks::bls12_381::parse_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::RistrettoDecimals => {
                for literal in attributes {
                    zkc_kernels::dalek::ristretto255::parse_decimal(literal)
                        .map_err(crate::field_error)?;
                }
            }
            AttributeRule::KoalaBearDecimals => {
                for literal in attributes {
                    let _ =
                        zkc_kernels::plonky3::parse_decimal(literal).map_err(crate::field_error)?;
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
                    let _ = zkc_kernels::plonky3::binary::parse_literal(literal)
                        .map_err(crate::field_error)?;
                }
            }
            AttributeRule::Binary64Ext3Literals => {
                for literal in attributes {
                    let _ = zkc_kernels::plonky3::binary::parse_ext3_literal(literal)
                        .map_err(crate::field_error)?;
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

    fn expression_binding(field: &str, provider: &str) -> Arc<CallBinding> {
        let declaration = zkc_runtime::vm::OperationBinding {
            physical_arguments: vec![],
            contract: "numerical.map".into(),
            arguments: vec![field.into(), "1".into()],
            implementation: format!("{provider}/numerical.map"),
        };
        Arc::new(CallBinding {
            signature: declaration.signature().unwrap(),
            declaration,
        })
    }

    fn expression_snapshot(call: &NativeCall) -> &Arc<CallBinding> {
        let CallPayload::Expression(expression) = &call.payload else {
            panic!("prepared expression");
        };
        &expression.binding
    }

    #[test]
    fn expression_preparation_refuses_representation_changes_and_preserves_warmed_plan() {
        use serde_json::json;
        use zkc_runtime::vm::{PhysicalType, Representation};

        let binding = expression_binding("bls12-381.fr", "arkworks");
        let attributes =
            vec![json!(["zkc.ring/0", ["bls12-381.fr"], [["input", 0]], [0]]).to_string()];
        let mut slot = None;
        NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
        let storage = slot.as_ref().unwrap().attributes.as_ptr();
        let plan = std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap());
        NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
        assert_eq!(
            plan,
            std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
        );

        for input in [true, false] {
            let mut wrong_binding = Arc::clone(&binding);
            let signature = &mut Arc::make_mut(&mut wrong_binding).signature;
            let port = if input {
                &mut signature.inputs[1]
            } else {
                &mut signature.outputs[0]
            };
            let original = port.clone();
            *port =
                PhysicalType::new(original.logical().clone(), Representation::FrDiagonal).unwrap();
            assert_eq!(port.logical(), original.logical());
            assert_ne!(*port, original);
            assert_eq!(
                NativeCall::prepare_expression(&mut slot, &wrong_binding, &attributes),
                Err(refused("numerical-binding"))
            );
            let retained = slot.as_ref().unwrap();
            assert_eq!(storage, retained.attributes.as_ptr());
            assert_eq!(plan, std::ptr::from_ref(retained.expression().unwrap()));
            assert!(Arc::ptr_eq(expression_snapshot(retained), &binding));

            NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
            assert_eq!(
                plan,
                std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
            );
        }
    }

    #[test]
    fn expression_preparation_keys_exact_binding_body_and_representations() {
        use serde_json::json;
        let binding = expression_binding("koala-bear", "plonky3");
        let attributes =
            vec![json!(["zkc.ring/0", ["koala-bear"], [["input", 0]], [0]]).to_string()];
        let mut slot = None;
        NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
        let storage = slot.as_ref().unwrap().attributes.as_ptr();
        let plan = std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap());
        let equal_owner = Arc::new((*binding).clone());
        assert!(!Arc::ptr_eq(&binding, &equal_owner));
        NativeCall::prepare_expression(&mut slot, &equal_owner, &attributes).unwrap();
        assert_eq!(storage, slot.as_ref().unwrap().attributes.as_ptr());
        assert_eq!(
            plan,
            std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
        );
        assert!(Arc::ptr_eq(
            expression_snapshot(slot.as_ref().unwrap()),
            &binding
        ));

        for changed in 0..6 {
            let mut wrong_binding = Arc::clone(&binding);
            let snapshot = Arc::make_mut(&mut wrong_binding);
            match changed {
                0 => snapshot.declaration.contract = "numerical.sum".into(),
                1 => snapshot.declaration.arguments[1] = "0".into(),
                2 => snapshot.declaration.implementation = "other/numerical.map".into(),
                3 => snapshot.signature.attributes = AttributeRule::None,
                4 => snapshot.signature.inputs[1] = snapshot.signature.inputs[0].clone(),
                5 => snapshot.signature.outputs[0] = snapshot.signature.inputs[0].clone(),
                _ => unreachable!(),
            }
            assert_eq!(
                NativeCall::prepare_expression(&mut slot, &wrong_binding, &attributes),
                Err(refused("numerical-binding"))
            );
            assert_eq!(storage, slot.as_ref().unwrap().attributes.as_ptr());
            assert_eq!(
                plan,
                std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
            );
            assert!(Arc::ptr_eq(
                expression_snapshot(slot.as_ref().unwrap()),
                &binding
            ));
        }

        let changed =
            vec![attributes[0].replace("[\"input\",0]", "[\"constant\",\"koala-bear\",\"1\"]")];
        NativeCall::prepare_expression(&mut slot, &binding, &changed).unwrap();
        assert_ne!(storage, slot.as_ref().unwrap().attributes.as_ptr());
        assert_eq!(
            slot.as_ref().unwrap().attributes.as_ref(),
            changed.as_slice()
        );

        // Equal body text and field do not identify the operand roles or sink.
        let mut binding = Arc::clone(&binding);
        for sum in [false, true] {
            let previous = slot.as_ref().unwrap().attributes.as_ptr();
            let snapshot = Arc::make_mut(&mut binding);
            if sum {
                snapshot.declaration.contract = "numerical.sum".into();
                snapshot.declaration.implementation = "plonky3/numerical.sum".into();
            } else {
                snapshot.declaration.arguments[1] = "0".into();
            }
            snapshot.signature = snapshot.declaration.signature().unwrap();
            NativeCall::prepare_expression(&mut slot, &binding, &changed).unwrap();
            assert_ne!(previous, slot.as_ref().unwrap().attributes.as_ptr());
            assert!(Arc::ptr_eq(
                expression_snapshot(slot.as_ref().unwrap()),
                &binding
            ));
        }

        let previous = slot.as_ref().unwrap().attributes.as_ptr();
        let snapshot = Arc::make_mut(&mut binding);
        snapshot.declaration.arguments[0] = "koala-bear.ext4-binomial3".into();
        snapshot.signature = snapshot.declaration.signature().unwrap();
        assert!(NativeCall::prepare_expression(&mut slot, &binding, &changed).is_err());
        assert_eq!(previous, slot.as_ref().unwrap().attributes.as_ptr());
        assert_eq!(
            expression_snapshot(slot.as_ref().unwrap())
                .declaration
                .arguments[0],
            "koala-bear"
        );
    }

    #[test]
    fn expression_preparation_rechecks_every_retained_metadata_field() {
        use serde_json::json;
        let binding = expression_binding("koala-bear", "plonky3");
        let attributes =
            vec![json!(["zkc.ring/0", ["koala-bear"], [["input", 0]], [0]]).to_string()];
        let mut slot = None;
        NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
        for changed in 0..6 {
            let CallPayload::Expression(expression) = &mut slot.as_mut().unwrap().payload else {
                panic!("prepared expression");
            };
            let snapshot = Arc::make_mut(&mut expression.binding);
            match changed {
                0 => snapshot.declaration.contract = "numerical.sum".into(),
                1 => snapshot.declaration.arguments[1] = "0".into(),
                2 => snapshot.declaration.implementation = "other/numerical.map".into(),
                3 => snapshot.signature.attributes = AttributeRule::None,
                4 => snapshot.signature.inputs[1] = snapshot.signature.inputs[0].clone(),
                5 => snapshot.signature.outputs[0] = snapshot.signature.inputs[0].clone(),
                _ => unreachable!(),
            }
            let plan = std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap());
            NativeCall::prepare_expression(&mut slot, &binding, &attributes).unwrap();
            assert_ne!(
                plan,
                std::ptr::from_ref(slot.as_ref().unwrap().expression().unwrap())
            );
            assert!(Arc::ptr_eq(
                expression_snapshot(slot.as_ref().unwrap()),
                &binding
            ));
        }
    }
}
