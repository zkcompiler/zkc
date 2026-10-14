use crate::interactive::executable::Slot;

/// One frame's values. Slots are monotonic SSA definitions; release leaves a
/// vacant slot and never reuses its identity while the frame remains active.
pub(super) struct Values<V>(Vec<Option<V>>);
impl<V> Values<V> {
    pub fn new(inputs: Vec<V>) -> Self {
        // The Runner reserves retention before inserting values. Do not allocate
        // slots for declarations that have not executed or will exhaust a budget.
        Self(inputs.into_iter().map(Some).collect())
    }
    pub fn insert(&mut self, slot: Slot, value: V) {
        assert_eq!(slot, self.0.len(), "prepared SSA definition order");
        self.0.push(Some(value));
    }
    pub fn extend(&mut self, slots: &[Slot], values: impl ExactSizeIterator<Item = V>) {
        assert_eq!(slots.len(), values.len(), "admitted output arity");
        for (slot, value) in slots.iter().zip(values) {
            self.insert(*slot, value);
        }
    }
    pub fn remove(&mut self, slot: &Slot) -> Option<V> {
        self.0[*slot].take()
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.iter().filter_map(Option::as_ref)
    }
}
impl<V> std::ops::Index<&Slot> for Values<V> {
    type Output = V;
    fn index(&self, slot: &Slot) -> &V {
        self.0[*slot].as_ref().expect("admitted live operand")
    }
}
