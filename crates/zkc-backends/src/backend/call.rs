//! Static attribute validation at the reached invocation's original check point.
use crate::{Result, ark, refused};
use zkc_runtime::interactive::AttributeRule;

/// Backend-owned static call facts. Values, custody, setup and budgets are never
/// cached here. A direct caller can reuse this only for equal rules/attributes;
/// the ordinary invocation checks still validate the exact current binding.
/// Validation must remain a pure function of the rule and attributes. Policy,
/// domain, setup and live values belong to the checked invocation path.
pub struct NativeCall {
    rule: AttributeRule,
    attributes: Box<[String]>,
}

impl NativeCall {
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
        Self::check(rule, attributes)?;
        *slot = Some(Self {
            rule,
            attributes: attributes.into(),
        });
        Ok(())
    }
    pub(super) fn check(rule: AttributeRule, attributes: &[String]) -> Result<()> {
        match rule {
            AttributeRule::None if attributes.is_empty() => (),
            AttributeRule::Unsigned64
                if attributes.len() == 1
                    && attributes[0]
                        .parse::<u64>()
                        .is_ok_and(|n| n.to_string() == attributes[0]) => {}
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
            AttributeRule::Bn254Decimal if attributes.len() == 1 => {
                crate::parse_bn254_decimal(&attributes[0]).map_err(ark)?;
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
            AttributeRule::KoalaBearDecimal if attributes.len() == 1 => {
                let _ = crate::plonky3::parse_decimal(&attributes[0])?;
            }
            AttributeRule::Binary64Literal if attributes.len() == 1 => {
                let _ = crate::plonky3::binary::parse_literal(&attributes[0])?;
            }
            AttributeRule::Binary64Ext3Literal if attributes.len() == 1 => {
                let _ = crate::plonky3::binary::parse_ext3_literal(&attributes[0])?;
            }
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
            AttributeRule::RistrettoDecimal if attributes.len() == 1 => {
                crate::parse_ristretto_decimal(&attributes[0])?;
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

            AttributeRule::FieldDecimal if attributes.len() == 1 => {
                zkc_arkworks::parse_decimal(&attributes[0]).map_err(ark)?;
            }
            _ => return Err(refused("kernel-attributes")),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preparation_reuses_only_equal_static_facts() {
        let mut call = None;
        let attributes = vec!["12".into()];
        NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &attributes).unwrap();
        let storage = call.as_ref().unwrap().attributes.as_ptr();
        NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &attributes).unwrap();
        assert_eq!(storage, call.as_ref().unwrap().attributes.as_ptr());

        // A cache hit never licenses another spelling or another rule.
        for invalid in [vec!["012".into()], vec!["-1".into()], vec![]] {
            let direct = NativeCall::prepare(&mut None, AttributeRule::Unsigned64, &invalid);
            let prepared = NativeCall::prepare(&mut call, AttributeRule::Unsigned64, &invalid);
            assert_eq!(direct, prepared);
            assert!(prepared.is_err());
            assert_eq!(storage, call.as_ref().unwrap().attributes.as_ptr());
        }
        assert!(NativeCall::prepare(&mut call, AttributeRule::None, &attributes).is_err());
        NativeCall::prepare(&mut call, AttributeRule::NaturalIndices, &attributes).unwrap();
        assert_eq!(call.as_ref().unwrap().rule, AttributeRule::NaturalIndices);
    }

    #[test]
    fn no_attributes_need_no_preparation_storage() {
        let mut call = None;
        NativeCall::prepare(&mut call, AttributeRule::None, &[]).unwrap();
        assert!(call.is_none());
    }
}
