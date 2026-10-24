//! The width-16 Poseidon2 permutation over KoalaBear with Plonky3 0.8.0's
//! default parameters: `p3_koala_bear::default_koalabear_poseidon2_16`, with
//! eight full rounds, twenty partial rounds, the cube S-box, the Grain-LFSR round
//! constants and the internal diagonal pinned by that release. The kernel
//! permutes each consecutive 16-element state of one vector. See
//! docs/spec/domains/permutations.md.
use super::KoalaBear;
use crate::interop::Work;
use p3_field::{Field, PackedValue};
use p3_koala_bear::{Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::Permutation;
use std::sync::OnceLock;

/// Invalid state width at the typed permutation boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Width,
}

/// Field elements in one permutation state.
pub const WIDTH: usize = 16;

/// The installed instance, constructed once from the pinned constants.
pub fn permutation() -> &'static Poseidon2KoalaBear<WIDTH> {
    static PERMUTATION: OnceLock<Poseidon2KoalaBear<WIDTH>> = OnceLock::new();
    PERMUTATION.get_or_init(default_koalabear_poseidon2_16)
}

/// Logical work of permuting `elements` values: one unit per state.
pub fn work(elements: usize) -> Result<Work, Error> {
    if !elements.is_multiple_of(WIDTH) {
        return Err(Error::Width);
    }
    Ok(Work {
        permutations: (elements / WIDTH) as u64,
        ..Work::default()
    })
}

/// Append every permuted consecutive state of `states` to `out`, in order.
/// Invalid widths leave `out` untouched. Callers may reserve destination space
/// before evaluation; this primitive imposes no allocation or work policy.
pub fn permute_states(states: &[KoalaBear], out: &mut Vec<KoalaBear>) -> Result<(), Error> {
    if !states.len().is_multiple_of(WIDTH) {
        return Err(Error::Width);
    }
    let start = out.len();
    out.extend_from_slice(states);
    crate::cpu::chunks_mut(&mut out[start..], 128 * WIDTH, |_, states| {
        type Packed = <KoalaBear as Field>::Packing;
        let packed_elements = WIDTH * Packed::WIDTH;
        let end = if Packed::WIDTH > 1 {
            states.len() / packed_elements * packed_elements
        } else {
            0
        };
        let (packed, tail) = states.split_at_mut(end);
        for block in packed.chunks_exact_mut(packed_elements) {
            // Transpose independent row-major states into SIMD lanes. The
            // caller's final row layout and every scalar tail stay unchanged.
            let mut lanes: [Packed; WIDTH] =
                std::array::from_fn(|column| Packed::from_fn(|lane| block[lane * WIDTH + column]));
            permutation().permute_mut(&mut lanes);
            for (column, lane) in lanes.iter().enumerate() {
                for (row, value) in lane.as_slice().iter().enumerate() {
                    block[row * WIDTH + column] = *value;
                }
            }
        }
        for state in tail.as_chunks_mut::<WIDTH>().0 {
            permutation().permute_mut(state);
        }
    });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_states_append_the_pinned_permutation() {
        let states: Vec<_> = (0..48).map(KoalaBear::new).collect();
        let mut out = vec![KoalaBear::new(99)];
        permute_states(&states, &mut out).unwrap();
        assert_eq!(out[0], KoalaBear::new(99));
        for (state, block) in states
            .as_chunks::<WIDTH>()
            .0
            .iter()
            .zip(out[1..].chunks(WIDTH))
        {
            let mut expected = *state;
            default_koalabear_poseidon2_16().permute_mut(&mut expected);
            assert_eq!(block, expected);
        }
        assert_eq!(out.len(), states.len() + 1);
        assert_eq!(work(states.len()).unwrap().permutations, 3);
        let saved = out.clone();
        permute_states(&[], &mut out).unwrap();
        assert_eq!(out, saved);
        assert_eq!(work(0), Ok(Work::default()));
    }

    #[test]
    fn invalid_widths_leave_the_destination_unchanged() {
        for width in [1, 15, 17, 31] {
            let mut out = vec![KoalaBear::new(99)];
            assert_eq!(work(width), Err(Error::Width));
            assert_eq!(
                permute_states(&vec![KoalaBear::new(1); width], &mut out),
                Err(Error::Width)
            );
            assert_eq!(out, [KoalaBear::new(99)]);
        }
    }

    #[test]
    fn packed_blocks_and_scalar_tails_preserve_every_state() {
        for count in [1, 15, 16, 17, 127, 128, 129, 257] {
            let states: Vec<_> = (0..count * WIDTH)
                .map(|i| KoalaBear::new((i * 17 + i / WIDTH) as u32))
                .collect();
            let mut expected = states.clone();
            for state in expected.as_chunks_mut::<WIDTH>().0 {
                default_koalabear_poseidon2_16().permute_mut(state);
            }
            let mut actual = Vec::new();
            permute_states(&states, &mut actual).unwrap();
            assert_eq!(actual, expected, "state count {count}");
        }
    }
}
