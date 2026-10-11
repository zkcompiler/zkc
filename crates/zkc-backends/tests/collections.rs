//! Collections backend contracts.
mod common;
#[path = "common/fixture.rs"]
mod fixture;
mod support;

#[path = "collections/field_array.rs"]
mod field_array;
#[path = "collections/fixed_vector.rs"]
mod fixed_vector;
#[path = "collections/matrix.rs"]
mod matrix;
#[path = "collections/matrix_contraction.rs"]
mod matrix_contraction;
#[path = "collections/matrix_identity.rs"]
mod matrix_identity;
#[path = "collections/sequence_execution.rs"]
mod sequence_execution;
#[path = "collections/sequences.rs"]
mod sequences;
#[path = "collections/vector_product.rs"]
mod vector_product;
#[path = "collections/vector_scatter.rs"]
mod vector_scatter;
#[path = "collections/vector_slice.rs"]
mod vector_slice;
#[path = "collections/vector_transpose.rs"]
mod vector_transpose;
