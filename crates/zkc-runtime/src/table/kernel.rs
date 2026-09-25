use super::Domain;
/// The field adapter is separate from plan control, storage and providers.
/// Every returned representation code is validated by the caller.
pub trait FieldKernel {
    fn add(&self, domain: Domain, a: u8, b: u8) -> u8;
    fn sub(&self, domain: Domain, a: u8, b: u8) -> u8;
    fn mul(&self, domain: Domain, a: u8, b: u8) -> u8;
}
#[derive(Clone, Copy, Debug, Default)]
pub struct SmallPrimeKernel;
impl FieldKernel for SmallPrimeKernel {
    fn add(&self, d: Domain, a: u8, b: u8) -> u8 {
        (a + b) % d.modulus()
    }
    fn sub(&self, d: Domain, a: u8, b: u8) -> u8 {
        (a + d.modulus() - b) % d.modulus()
    }
    fn mul(&self, d: Domain, a: u8, b: u8) -> u8 {
        (a * b) % d.modulus()
    }
}
