//! Independent installed-kernel checks for the compiler's domain convention.
#[path = "domains/support.rs"]
mod support;
use p3_field::{PrimeCharacteristicRing, TwoAdicField};
use p3_koala_bear::KoalaBear;
use zkc_backends::{
    KoalaBearExt8, Policy, domains,
    plonky3::polynomial::{Domain, Error},
};
use zkc_runtime::interactive::{Backend, Identity, OperationBinding};

#[test]
fn installed_root_order_and_fold_domain() {
    let maximal = KoalaBear::new(1791270792);
    assert_eq!(KoalaBear::TWO_ADICITY, 24);
    assert_eq!(KoalaBear::two_adic_generator(24), maximal);
    assert_eq!(
        Domain::new(1, KoalaBear::ONE, 1).unwrap().generator(),
        KoalaBear::ONE
    );
    assert!(matches!(
        Domain::new(1 << 25, KoalaBear::ONE, 1 << 25),
        Err(Error::DomainSize)
    ));
    for log_size in 1..=8 {
        let n = 1 << log_size;
        let domain = Domain::new(n, KoalaBear::new(3), n).unwrap();
        let root = maximal.exp_u64((1 << 24) / n as u64);
        assert_eq!(domain.generator(), root);
        let next = domain.folded().unwrap();
        let independently_formed = Domain::new(n / 2, KoalaBear::new(9), n).unwrap();
        assert_eq!(next.size(), n / 2);
        assert_eq!(next.generator(), independently_formed.generator());
        for i in 0..n / 2 {
            assert_eq!(
                domain.point(i).unwrap(),
                KoalaBear::new(3) * root.exp_u64(i as u64)
            );
            assert_eq!(next.point(i).unwrap(), domain.point(i).unwrap().square());
            assert_eq!(
                next.point(i).unwrap(),
                independently_formed.point(i).unwrap()
            );
        }
        let shift = KoalaBearExt8::from([3, 1, 0, 0, 0, 0, 0, 0].map(KoalaBear::new));
        let extension = Domain::new(n, shift, n).unwrap();
        assert_eq!(extension.generator(), KoalaBearExt8::from(root));
        let folded_extension = extension.folded().unwrap();
        let formed_extension = Domain::new(n / 2, shift.square(), n).unwrap();
        for i in 0..n / 2 {
            assert_eq!(
                folded_extension.point(i).unwrap(),
                extension.point(i).unwrap().square()
            );
            assert_eq!(
                folded_extension.point(i).unwrap(),
                formed_extension.point(i).unwrap()
            );
        }
    }
    assert!(matches!(
        Domain::new(3, KoalaBear::ONE, 8),
        Err(Error::DomainSize)
    ));
    assert!(matches!(
        Domain::new(8, KoalaBear::ZERO, 8),
        Err(Error::ZeroShift)
    ));
    assert!(matches!(
        Domain::new(8, KoalaBear::ONE, 4),
        Err(Error::ElementLimit)
    ));
    assert!(matches!(
        Domain::new(1, KoalaBear::ONE, 1).unwrap().folded(),
        Err(Error::FoldSize)
    ));
}

#[test]
fn fold_bindings_require_installed_two_adic_odd_fields() {
    let backend = support::backend(Policy::default());
    for domain in domains::INSTALLED {
        let b = OperationBinding {
            contract: "poly.even_odd_fold".into(),
            arguments: vec![domain.field.name().into()],
            implementation: format!("{}/poly.even_odd_fold", domain.provider),
        };
        assert_eq!(
            b.signature().is_ok(),
            matches!(
                domain.field,
                Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8
            )
        );
        assert_eq!(
            backend.binding_signature(&b).is_some(),
            b.signature().is_ok()
        );
        assert!(domain.field.has_characteristic_not_two());
    }
    for identity in [
        Identity::None,
        Identity::Bls12381G1,
        Identity::MerkleKoalaBear,
    ] {
        assert!(!identity.has_characteristic_not_two());
    }
    // No characteristic-two installation is introduced to test a refusal.
    let unsupported = OperationBinding {
        contract: "poly.even_odd_fold".into(),
        arguments: vec!["uninstalled.binary".into()],
        implementation: "plonky3/poly.even_odd_fold".into(),
    };
    assert!(unsupported.signature().is_err());
    assert!(backend.binding_signature(&unsupported).is_none());
}
